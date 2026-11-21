#![deny(warnings)]
use std::collections::{HashMap, HashSet};

use itertools::Itertools;
use petgraph::algo::tarjan_scc;
use petgraph::graphmap::DiGraphMap;
use petgraph::visit::Dfs;
use syn::{Error, Expr, Ident, Result, parse_quote, parse_quote_spanned};

use crate::ascent_hir::{AscentConfig, REL_DS_ATTR};
use crate::ascent_syntax::{
   AggClauseNode, AggregatorNode, AscentProgram, BodyItemNode, HeadItemNode, RelationIdentity, RelationNode, RuleNode,
};
use crate::syn_utils::pattern_get_vars;
use crate::utils::expr_to_ident;

fn body_item_rel(bitem: &BodyItemNode) -> Option<&Ident> {
   match bitem {
      BodyItemNode::Clause(bcl) => Some(&bcl.rel),
      BodyItemNode::Negation(neg) => Some(&neg.rel),
      BodyItemNode::Agg(agg) => Some(&agg.rel),
      _ => None,
   }
}

/// Is `agg` a negation written as an aggregation with the `not` aggregator?
fn is_negation(agg: &AggClauseNode) -> bool {
   let AggregatorNode::Path(path) = &agg.aggregator else { return false };
   let path = path.segments.iter().map(|segment| segment.ident.to_string()).collect_vec();
   (path == ["not"] || path == ["ascent", "aggregators", "not"])
      && agg.bound_args.is_empty()
      && pattern_get_vars(&agg.pat).is_empty()
}

/// Returns the relations in recursions through negation, mapped to the index of their recursion, and the relations
/// that may hold undefined facts: those, and the relations depending on them
fn relations_with_undefined_facts(rules: &[RuleNode]) -> (HashMap<Ident, usize>, HashSet<Ident>) {
   let mut dep_graph = DiGraphMap::<&Ident, ()>::new();
   let mut negations = vec![];
   for rule in rules.iter() {
      for head_rel in rule.head_clauses.iter().map(|hcl| &hcl.clause().rel) {
         dep_graph.add_node(head_rel);
         for bitem in rule.body_items.iter() {
            if let Some(body_rel) = body_item_rel(bitem) {
               dep_graph.add_edge(body_rel, head_rel, ());
            }
            if let BodyItemNode::Negation(neg) = bitem {
               negations.push((&neg.rel, head_rel));
            }
         }
      }
   }
   let sccs = tarjan_scc(&dep_graph);
   let mut negation_cycles = HashMap::new();
   let mut dfs = Dfs::empty(&dep_graph);
   let mut affected = HashSet::new();
   for (neg_rel, head_rel) in negations {
      let cycle = sccs.iter().find_position(|scc| scc.contains(&neg_rel) && scc.contains(&head_rel));
      if let Some((cycle_ind, cycle)) = cycle {
         negation_cycles.extend(cycle.iter().map(|&rel| (rel.clone(), cycle_ind)));
         dfs.move_to(head_rel);
         while let Some(rel) = dfs.next(&dep_graph) {
            affected.insert(rel.clone());
         }
      }
   }
   (negation_cycles, affected)
}

/// Prepares a program with the `well_founded` attribute for computing the well-founded model.
///
/// Relations that may hold undefined facts (those in a recursion through negation, and those depending on them)
/// get a twin relation holding their possible facts (the true and the undefined ones). Rules mentioning such relations
/// are duplicated: the original rule derives true facts, reading the possible facts of negated relations, while
/// its twin derives possible facts, reading the true facts of negated relations. Aggregations derive true facts
/// from groups without undefined facts, and possible facts from both the true and the possible facts of a group.
pub(crate) fn desugar_well_founded(prog: &mut AscentProgram) -> Result<()> {
   if !prog.attributes.iter().any(|attr| attr.path().is_ident(AscentConfig::WELL_FOUNDED_ATTR)) {
      return Ok(());
   }

   for bitem in prog.rules.iter_mut().flat_map(|rule| rule.body_items.iter_mut()) {
      if let BodyItemNode::Agg(agg) = bitem {
         if is_negation(agg) {
            let (rel, args) = (&agg.rel, &agg.rel_args);
            *bitem = parse_quote_spanned! {agg.agg_kw.span=> !#rel(#args)};
         }
      }
   }

   let (negation_cycles, affected) = relations_with_undefined_facts(&prog.rules);
   let lattices = prog.relations.iter().filter(|rel| rel.is_lattice).map(|rel| &rel.name).collect::<HashSet<_>>();
   for rule in prog.rules.iter() {
      for bitem in rule.body_items.iter() {
         if let BodyItemNode::Negation(neg) = bitem {
            if lattices.contains(&neg.rel) && affected.contains(&neg.rel) {
               let msg = format!("lattice `{}` may hold undefined facts, and cannot be negated", neg.rel);
               return Err(Error::new(neg.rel.span(), msg));
            }
         }
         if let BodyItemNode::Agg(agg) = bitem {
            let cycle = negation_cycles.get(&agg.rel);
            if cycle.is_some() && rule.head_clauses.iter().any(|hcl| negation_cycles.get(&hcl.clause().rel) == cycle) {
               let msg = format!("aggregation of relation `{}` inside a recursion through negation", agg.rel);
               return Err(Error::new(agg.agg_kw.span, msg));
            }
         }
      }
   }

   let mut possible_rels: Vec<(Ident, RelationNode)> = vec![];
   for rel in prog.relations.iter().filter(|rel| affected.contains(&rel.name)) {
      let ds_attrs = rel.attrs.iter().filter(|attr| attr.path().is_ident(REL_DS_ATTR)).cloned();
      let possible_rel = RelationNode {
         attrs: [parse_quote!(#[doc(hidden)])].into_iter().chain(ds_attrs).collect(),
         name: Ident::new(&format!("__{}_possible", rel.name), rel.name.span()),
         initialization: None,
         ..rel.clone()
      };
      prog.possible_relations.insert(RelationIdentity::from(rel), RelationIdentity::from(&possible_rel));
      prog.hidden_relations.insert(RelationIdentity::from(&possible_rel));
      possible_rels.push((rel.name.clone(), possible_rel));
   }

   let to_possible = |rel: &mut Ident| {
      if let Some((_, possible_rel)) = possible_rels.iter().find(|(name, _)| name == rel) {
         *rel = possible_rel.name.clone();
      }
   };
   let unsettled_rel_name = |rel: &Ident| Ident::new(&format!("__{rel}_unsettled"), rel.span());
   let mut unsettled_rels = vec![];
   let mut rules = vec![];
   for mut rule in std::mem::take(&mut prog.rules) {
      if rule.body_items.iter().any(|bitem| body_item_rel(bitem).is_some_and(|rel| affected.contains(rel))) {
         let mut possible_rule = rule.clone();
         for hitem in possible_rule.head_clauses.iter_mut() {
            if let HeadItemNode::HeadClause(hcl) = hitem {
               to_possible(&mut hcl.rel);
            }
         }
         for bitem in possible_rule.body_items.iter_mut() {
            if let BodyItemNode::Clause(bcl) = bitem {
               to_possible(&mut bcl.rel);
            }
         }
         let mut possible_rules = vec![possible_rule];
         let mut body_items = vec![];
         for (i, mut bitem) in std::mem::take(&mut rule.body_items).into_iter().enumerate() {
            match &mut bitem {
               BodyItemNode::Negation(neg) => to_possible(&mut neg.rel),
               BodyItemNode::Agg(agg) if affected.contains(&agg.rel) => {
                  // the aggregate of a group is true if the group has no undefined facts
                  let rel_args = agg.rel_args.iter().map(|arg| -> Expr {
                     if expr_to_ident(arg).is_some_and(|var| agg.bound_args.iter().contains(&var)) {
                        parse_quote!(_)
                     } else {
                        arg.clone()
                     }
                  });
                  let rel_args = rel_args.collect_vec();
                  unsettled_rels.push(agg.rel.clone());
                  let unsettled_rel = unsettled_rel_name(&agg.rel);
                  let span = agg.agg_kw.span;
                  let undefined_count = Ident::new(&format!("__undefined_count_{i}"), span);
                  body_items.extend::<[BodyItemNode; 2]>([
                     parse_quote_spanned! {span=>
                        agg #undefined_count = ::ascent::aggregators::count() in #unsettled_rel(#(#rel_args),*)
                     },
                     parse_quote_spanned! {span=> if #undefined_count == 0},
                  ]);
                  possible_rules = possible_rules
                     .into_iter()
                     .flat_map(|possible_rule| {
                        let mut possible_group_rule = possible_rule.clone();
                        if let BodyItemNode::Agg(agg) = &mut possible_group_rule.body_items[i] {
                           to_possible(&mut agg.rel);
                        }
                        [possible_rule, possible_group_rule]
                     })
                     .collect();
               },
               _ => (),
            }
            body_items.push(bitem);
         }
         rule.body_items = body_items;
         rules.extend(possible_rules);
      }
      rules.push(rule);
   }
   for (rel, possible_rel) in possible_rels {
      let vars = (0..possible_rel.field_types.len()).map(|i| Ident::new(&format!("__x{i}"), rel.span())).collect_vec();
      let possible_rel_name = &possible_rel.name;
      rules.push(parse_quote_spanned! {rel.span()=> #possible_rel_name(#(#vars),*) <-- #rel(#(#vars),*);});
      if unsettled_rels.contains(&rel) {
         // the undefined facts: possible facts that are not true facts
         let unsettled_rel = RelationNode {
            attrs: vec![parse_quote!(#[doc(hidden)]), parse_quote!(#[ds(::ascent::rel)])],
            name: unsettled_rel_name(&rel),
            is_lattice: false,
            ..possible_rel.clone()
         };
         let unsettled_name = &unsettled_rel.name;
         let unsettled_rel_head = quote! { #unsettled_name(#(#vars),*) <-- #possible_rel_name(#(#vars),*) };
         if possible_rel.is_lattice {
            let (value_var, key_vars) = vars.split_last().unwrap();
            rules.extend::<[RuleNode; 2]>([
               parse_quote_spanned! {rel.span()=> #unsettled_rel_head, !#rel(#(#key_vars,)* _);},
               parse_quote_spanned! {rel.span()=>
                  #unsettled_rel_head, #rel(#(#key_vars,)* __true_value), if __true_value != #value_var;
               },
            ]);
         } else {
            rules.push(parse_quote_spanned! {rel.span()=> #unsettled_rel_head, !#rel(#(#vars),*);});
         }
         prog.hidden_relations.insert(RelationIdentity::from(&unsettled_rel));
         prog.relations.push(unsettled_rel);
      }
      prog.relations.push(possible_rel);
   }
   prog.rules = rules;
   Ok(())
}
