#![cfg(test)]
//! Tests of the `#![generate_provenance]` attribute.
//!
//! Rule positions are zero-based and count every rule (including body-less fact rules)
//! in source order; relation declarations are not counted. A fact a fact rule makes may be a
//! leaf instead of naming that rule.
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;

use ascent::aggregators::{not, sum};
use ascent::provenance::Proof;
use ascent::{Dual, ascent, ascent_run};


/// An aggregator counting the tuples it consumes; its arguments name the counted columns.
fn count_of<T>(inp: impl Iterator<Item = T>) -> impl Iterator<Item = usize> { std::iter::once(inp.count()) }

/// Canonical rendering of a proof tree (does not rely on any trait impls of `Proof`). Premises are
/// unordered, so they are rendered sorted.
fn render(p: &Proof) -> String {
   let mut ps: Vec<String> = p.premises.iter().map(render).collect();
   ps.sort();
   format!("{}{}#{:?}[{}]", p.relation, p.fact, p.rule, ps.join(", "))
}

/// The Debug rendering of a fact.
fn fact<T: Debug>(t: &T) -> String { format!("{:?}", t) }

/// The rendering of a leaf proof of `relation` `fact_str`.
fn leaf(relation: &str, fact_str: &str) -> String { format!("{}{}#None[]", relation, fact_str) }

/// The sorted renderings of some proofs: premises compared as a multiset.
fn renders<'a>(ps: impl IntoIterator<Item = &'a Proof>) -> Vec<String> {
   let mut v: Vec<String> = ps.into_iter().map(render).collect();
   v.sort();
   v
}

/// The only premise of `p` from `relation`.
fn premise<'a>(p: &'a Proof, relation: &str) -> &'a Proof {
   let mut found = p.premises.iter().filter(|q| q.relation == relation);
   let q = found.next().unwrap_or_else(|| panic!("{}{} has no {} premise", p.relation, p.fact, relation));
   assert!(found.next().is_none(), "{}{} has more than one {} premise", p.relation, p.fact, relation);
   q
}

fn assert_leaf(p: &Proof, relation: &str, fact_str: &str) {
   assert_eq!(p.relation, relation);
   assert_eq!(p.fact, fact_str);
   assert_eq!(p.rule, None, "expected leaf for {}{}", relation, fact_str);
   assert!(p.premises.is_empty(), "expected no premises for {}{}", relation, fact_str);
}

/// The fact `fact_str` of `relation` made by the body-less fact rule at `position`: a leaf, or a
/// proof naming that rule.
fn assert_fact_rule_fact(p: &Proof, relation: &str, fact_str: &str, position: usize) {
   assert_eq!(p.relation, relation);
   assert_eq!(p.fact, fact_str);
   assert!(p.rule.is_none() || p.rule == Some(position), "{}{} has rule {:?}", p.relation, p.fact, p.rule);
   assert!(p.premises.is_empty(), "{}{} has premises", p.relation, p.fact);
}

/// The relations of `p`'s premises, sorted: premises are unordered.
fn premise_relations(p: &Proof) -> Vec<String> {
   let mut v: Vec<String> = p.premises.iter().map(|q| q.relation.to_string()).collect();
   v.sort();
   v
}

fn sorted_strings(v: &[String]) -> Vec<String> {
   let mut v = v.to_vec();
   v.sort();
   v
}

/// The facts (as Debug strings) of a program's relations and the rule positions that may derive each relation.
#[derive(Default)]
struct Db {
   facts: HashMap<String, HashSet<String>>,
   rules: HashMap<String, HashSet<usize>>,
}

impl Db {
   fn rel<'a, T: Debug + 'a>(mut self, name: &str, tuples: impl IntoIterator<Item = &'a T>, rules: &[usize]) -> Self {
      self.facts.entry(name.to_string()).or_default().extend(tuples.into_iter().map(fact));
      self.rules.entry(name.to_string()).or_default().extend(rules.iter().copied());
      self
   }
}

/// Structural validity: every node's fact is in its relation, rule numbers belong to the relation,
/// and nodes without a rule have no premises.
fn check_valid(p: &Proof, db: &Db) { check_valid_grouped(p, db, &Db::default()) }

/// `check_valid`, where the premises of each relation in `aggregated` may be grouped (see `is_group`).
fn check_valid_grouped(p: &Proof, db: &Db, aggregated: &Db) {
   let rel = p.relation.to_string();
   let facts = db.facts.get(&rel).unwrap_or_else(|| panic!("unknown relation {}", rel));
   assert!(facts.contains(&p.fact), "fact {}{} is not in its relation", rel, p.fact);
   match p.rule {
      Some(r) => assert!(db.rules[&rel].contains(&r), "rule {} cannot derive {}{}", r, rel, p.fact),
      None => assert!(p.premises.is_empty(), "underived fact {}{} has premises", rel, p.fact),
   }
   for q in &p.premises {
      if is_group(q, aggregated) {
         q.premises.iter().for_each(|r| check_valid_grouped(r, db, aggregated));
      } else {
         check_valid_grouped(q, db, aggregated);
      }
   }
}

// An implementation may group the proofs of one aggregation's facts (a negation is an aggregation
// by `not`) under one extra premise. The tests recognise such a group by what they know of the
// rule body: `aggregated` holds the facts of each relation that the body aggregates or negates (and
// does not otherwise match), and a group is a premise named after one of them, with no rule and a
// fact that is not one of that relation's facts.

fn is_group(q: &Proof, aggregated: &Db) -> bool {
   // A rule-less proof of an aggregated relation with premises can only be a group; one without
   // premises is a group if its fact is not a fact of the relation.
   q.rule.is_none()
      && aggregated
         .facts
         .get(&q.relation.to_string())
         .is_some_and(|facts| !q.premises.is_empty() || !facts.contains(&q.fact))
}

/// `p`'s premises with each group replaced by its premises, and the number of groups. A relation
/// has at most one group, whose premises are all of that relation and which no premise of that
/// relation sits beside.
fn open_groups<'a>(p: &'a Proof, aggregated: &Db) -> (Vec<&'a Proof>, usize) {
   let (groups, mut flat): (Vec<&Proof>, Vec<&Proof>) = p.premises.iter().partition(|q| is_group(q, aggregated));
   for g in &groups {
      assert_eq!(groups.iter().filter(|h| h.relation == g.relation).count(), 1, "{} has two groups", g.relation);
      assert!(flat.iter().all(|q| q.relation != g.relation), "{} premises outside its group", g.relation);
      assert!(g.premises.iter().all(|q| q.relation == g.relation), "group of {} holds other relations", g.relation);
      flat.extend(g.premises.iter());
   }
   (flat, groups.len())
}


ascent! {
   #![generate_provenance]
   struct Tc;
   relation edge(i32, i32);
   relation path(i32, i32);
   path(x, y) <-- edge(x, y);                 // rule 0
   path(x, z) <-- edge(x, y), path(y, z);     // rule 1
}

fn tc_with(edges: &[(i32, i32)]) -> Tc {
   let mut prog = Tc::default();
   prog.edge = edges.to_vec();
   prog.run();
   prog
}

fn tc_db(prog: &Tc) -> Db { Db::default().rel("edge", prog.edge.iter(), &[]).rel("path", prog.path.iter(), &[0, 1]) }

#[test]
fn input_fact_has_no_rule_and_no_premises() {
   let prog = tc_with(&[(1, 2), (2, 3)]);
   let p = prog.explain_edge(&(1, 2)).expect("edge(1, 2) is an input fact");
   assert_leaf(&p, "edge", "(1, 2)");
}

#[test]
fn missing_fact_returns_none() {
   let prog = tc_with(&[(1, 2), (2, 3)]);
   assert!(prog.explain_path(&(3, 1)).is_none());
   assert!(prog.explain_path(&(9, 9)).is_none());
   assert!(prog.explain_edge(&(1, 3)).is_none());
}

#[test]
fn base_rule_proof() {
   let prog = tc_with(&[(1, 2), (2, 3)]);
   let p = prog.explain_path(&(1, 2)).unwrap();
   assert_eq!(p.relation, "path");
   assert_eq!(p.fact, "(1, 2)");
   assert_eq!(p.rule, Some(0));
   assert_eq!(p.premises.len(), 1);
   assert_leaf(&p.premises[0], "edge", "(1, 2)");
}

#[test]
fn chain_proof_structure() {
   let prog = tc_with(&[(1, 2), (2, 3), (3, 4)]);
   let p = prog.explain_path(&(1, 4)).unwrap();
   assert_eq!(p.rule, Some(1));
   assert_eq!(premise_relations(&p), vec!["edge", "path"]);
   assert_leaf(premise(&p, "edge"), "edge", "(1, 2)");

   let p24 = premise(&p, "path");
   assert_eq!(p24.fact, "(2, 4)");
   assert_eq!(p24.rule, Some(1));
   assert_eq!(premise_relations(p24), vec!["edge", "path"]);
   assert_leaf(premise(p24, "edge"), "edge", "(2, 3)");

   let p34 = premise(p24, "path");
   assert_eq!(p34.relation, "path");
   assert_eq!(p34.fact, "(3, 4)");
   assert_eq!(p34.rule, Some(0));
   assert_eq!(p34.premises.len(), 1);
   assert_leaf(&p34.premises[0], "edge", "(3, 4)");
}

#[test]
fn first_derivation_is_the_direct_edge() {
   let prog = tc_with(&[(1, 2), (2, 3), (1, 3)]);
   let p = prog.explain_path(&(1, 3)).unwrap();
   assert_eq!(p.rule, Some(0));
   assert_eq!(p.premises.len(), 1);
   assert_leaf(&p.premises[0], "edge", "(1, 3)");
}

#[test]
fn every_fact_of_cyclic_graph_has_valid_proof() {
   let prog = tc_with(&[(1, 2), (2, 3), (3, 1), (3, 4), (4, 4)]);
   let db = tc_db(&prog);
   for t in prog.path.iter() {
      let p = prog.explain_path(t).unwrap_or_else(|| panic!("no proof for path{:?}", t));
      assert_eq!(p.fact, fact(t));
      assert!(p.rule.is_some(), "path{:?} is derived", t);
      check_valid(&p, &db);
   }
   for t in prog.edge.iter() {
      assert_leaf(&prog.explain_edge(t).unwrap(), "edge", &fact(t));
   }
}

#[test]
fn multi_clause_join_premises_are_the_matched_facts() {
   ascent! {
      #![generate_provenance]
      struct Join3;
      relation a(i32, i32);
      relation b(i32, i32);
      relation c(i32, i32);
      relation out(i32, i32);
      out(x, w) <-- c(z, w), a(x, y), b(y, z);   // rule 0
   }
   let mut prog = Join3::default();
   prog.a = vec![(1, 2)];
   prog.b = vec![(2, 3)];
   prog.c = vec![(3, 4), (5, 6)];
   prog.run();
   let p = prog.explain_out(&(1, 4)).unwrap();
   assert_eq!(p.relation, "out");
   assert_eq!(p.rule, Some(0));
   assert_eq!(premise_relations(&p), vec!["a", "b", "c"]);
   assert_leaf(premise(&p, "c"), "c", "(3, 4)");
   assert_leaf(premise(&p, "a"), "a", "(1, 2)");
   assert_leaf(premise(&p, "b"), "b", "(2, 3)");
   assert!(prog.explain_out(&(1, 6)).is_none());
}

#[test]
fn self_join_premises_are_both_matched_facts() {
   ascent! {
      #![generate_provenance]
      struct Family;
      relation parent(&'static str, &'static str);
      relation grandparent(&'static str, &'static str);
      grandparent(x, z) <-- parent(x, y), parent(y, z);   // rule 0
   }
   let mut prog = Family::default();
   prog.parent = vec![("ann", "bob"), ("bob", "cid"), ("dan", "eve")];
   prog.run();
   let p = prog.explain_grandparent(&("ann", "cid")).unwrap();
   assert_eq!(p.fact, "(\"ann\", \"cid\")");
   assert_eq!(p.rule, Some(0));
   let expected = sorted_strings(&[leaf("parent", "(\"ann\", \"bob\")"), leaf("parent", "(\"bob\", \"cid\")")]);
   assert_eq!(renders(&p.premises), expected);
   assert!(prog.explain_grandparent(&("bob", "eve")).is_none());
}

#[test]
fn fact_rules_count_toward_rule_positions() {
   ascent! {
      #![generate_provenance]
      struct FactRules;
      relation edge(i32, i32);
      relation path(i32, i32);
      edge(1, 2);                                // rule 0
      edge(2, 3);                                // rule 1
      path(x, y) <-- edge(x, y);                 // rule 2
      path(x, z) <-- edge(x, y), path(y, z);     // rule 3
   }
   let mut prog = FactRules::default();
   prog.run();
   assert_fact_rule_fact(&prog.explain_edge(&(1, 2)).unwrap(), "edge", "(1, 2)", 0);
   assert_fact_rule_fact(&prog.explain_edge(&(2, 3)).unwrap(), "edge", "(2, 3)", 1);

   let p = prog.explain_path(&(1, 3)).unwrap();
   assert_eq!(p.rule, Some(3));
   assert_eq!(premise_relations(&p), vec!["edge", "path"]);
   assert_fact_rule_fact(premise(&p, "edge"), "edge", "(1, 2)", 0);
   assert_eq!(premise(&p, "path").rule, Some(2));
   assert_eq!(premise(&p, "path").fact, "(2, 3)");
   assert_fact_rule_fact(&premise(&p, "path").premises[0], "edge", "(2, 3)", 1);
}

#[test]
fn multi_head_rule_gives_both_heads_the_same_position() {
   ascent! {
      #![generate_provenance]
      struct MultiHead;
      relation seed(i32);
      relation c(i32);
      relation a(i32);
      relation b(i32);
      relation d(i32);
      c(x) <-- seed(x);              // rule 0
      a(x), b(x) <-- c(x);           // rule 1
      d(x) <-- a(x), b(x);           // rule 2
   }
   let mut prog = MultiHead::default();
   prog.seed = vec![(5,)];
   prog.run();
   let a = prog.explain_a(&(5,)).unwrap();
   let b = prog.explain_b(&(5,)).unwrap();
   assert_eq!(a.relation, "a");
   assert_eq!(b.relation, "b");
   assert_eq!(a.rule, Some(1));
   assert_eq!(b.rule, Some(1));
   assert_eq!(premise_relations(&a), vec!["c"]);
   assert_eq!(premise_relations(&b), vec!["c"]);
   assert_eq!(a.premises[0].rule, Some(0));
   let d = prog.explain_d(&(5,)).unwrap();
   assert_eq!(d.rule, Some(2));
   assert_eq!(premise_relations(&d), vec!["a", "b"]);
}

ascent! {
   #![generate_provenance]
   struct Neg;
   relation node(i32);
   relation bad(i32);
   relation good(i32);
   bad(x) <-- node(x), if *x > 2;     // rule 0
   good(x) <-- node(x), !bad(x);      // rule 1
}

#[test]
fn negation_adds_no_premise() {
   let mut prog = Neg::default();
   prog.node = (1..=4).map(|x| (x,)).collect();
   prog.run();
   let negated = Db::default().rel("bad", prog.bad.iter(), &[]);
   let g = prog.explain_good(&(1,)).unwrap();
   assert_eq!(g.rule, Some(1));
   let (premises, groups) = open_groups(&g, &negated);
   assert!(groups <= 1);
   assert_eq!(renders(premises), vec![leaf("node", "(1,)")]);
   assert!(prog.explain_good(&(3,)).is_none());
}

#[test]
fn if_and_let_add_no_premises() {
   ascent! {
      #![generate_provenance]
      struct IfLet;
      relation a(i32);
      relation b(i32, i32);
      relation out(i32, i32);
      out(x, w) <-- a(x), if *x > 0, let y = *x + 1, b(y, w);   // rule 0
   }
   let mut prog = IfLet::default();
   prog.a = vec![(1,), (-1,)];
   prog.b = vec![(2, 7), (0, 9)];
   prog.run();
   let p = prog.explain_out(&(1, 7)).unwrap();
   assert_eq!(p.rule, Some(0));
   assert_eq!(renders(&p.premises), vec![leaf("a", "(1,)"), leaf("b", "(2, 7)")]);
   assert!(prog.explain_out(&(-1, 9)).is_none());
}

ascent! {
   #![generate_provenance]
   struct Disj;
   relation number(i32);
   relation even(i32);
   relation square(i32);
   relation eos(i32);
   even(x) <-- number(x), if x % 2 == 0;            // rule 0
   square(y * y) <-- number(y), number(y * y);       // rule 1
   eos(x) <-- (even(x) | square(x));                 // rule 2
}

fn disj() -> Disj {
   let mut prog = Disj::default();
   prog.number = (1..=5).map(|x| (x,)).collect();
   prog.run();
   prog
}

#[test]
fn disjunction_right_alternative_same_position() {
   let prog = disj();
   let p = prog.explain_eos(&(1,)).unwrap();
   assert_eq!(p.rule, Some(2));
   assert_eq!(premise_relations(&p), vec!["square"]);
   let sq = &p.premises[0];
   assert_eq!(sq.fact, "(1,)");
   assert_eq!(sq.rule, Some(1));
   assert_eq!(sq.premises.len(), 2);
   assert_leaf(&sq.premises[0], "number", "(1,)");
   assert_leaf(&sq.premises[1], "number", "(1,)");
   assert!(prog.explain_eos(&(3,)).is_none());

   let s4 = prog.explain_square(&(4,)).unwrap();
   assert_eq!(renders(&s4.premises), vec![leaf("number", "(2,)"), leaf("number", "(4,)")]);
}

ascent! {
   #![generate_provenance]
   struct Agg;
   relation store(&'static str);
   relation sale(&'static str, u32);
   relation total(&'static str, u32);
   relation cnt(&'static str, usize);
   total(s, t) <-- store(s), agg t = sum(v) in sale(s, v);     // rule 0
   cnt(s, n) <-- store(s), agg n = count_of(v) in sale(s, v);  // rule 1
}

fn agg_prog() -> Agg {
   let mut prog = Agg::default();
   prog.store = vec![("a",), ("b",), ("c",)];
   prog.sale = vec![("a", 1), ("a", 2), ("a", 4), ("b", 5)];
   prog.run();
   prog
}

#[test]
fn sum_aggregation_premises() {
   let prog = agg_prog();
   let sales = Db::default().rel("sale", prog.sale.iter(), &[]);
   let p = prog.explain_total(&("a", 7)).unwrap();
   assert_eq!(p.relation, "total");
   assert_eq!(p.rule, Some(0));
   let (premises, groups) = open_groups(&p, &sales);
   assert!(groups <= 1);
   let expected = sorted_strings(&[
      leaf("store", "(\"a\",)"),
      leaf("sale", &fact(&("a", 1u32))),
      leaf("sale", &fact(&("a", 2u32))),
      leaf("sale", &fact(&("a", 4u32))),
   ]);
   assert_eq!(renders(premises), expected);

   let b = prog.explain_total(&("b", 5)).unwrap();
   let expected = vec![leaf("sale", "(\"b\", 5)"), leaf("store", "(\"b\",)")];
   assert_eq!(renders(open_groups(&b, &sales).0), expected);
}

#[test]
fn count_of_empty_group_consumes_nothing() {
   let prog = agg_prog();
   let sales = Db::default().rel("sale", prog.sale.iter(), &[]);
   let p = prog.explain_cnt(&("c", 0)).unwrap();
   assert_eq!(p.rule, Some(1));
   let (premises, groups) = open_groups(&p, &sales);
   assert!(groups <= 1);
   assert_eq!(renders(premises), vec![leaf("store", "(\"c\",)")]);
}

#[test]
fn aggregated_premises_carry_their_own_proofs() {
   ascent! {
      #![generate_provenance]
      struct AggDerived;
      relation raw(u32, u32);
      relation grp(u32);
      relation val(u32, u32);
      relation tot(u32, u32);
      val(g, v * 2) <-- raw(g, v);                                // rule 0
      tot(g, s) <-- grp(g), agg s = sum(v) in val(g, v);          // rule 1
   }
   let mut prog = AggDerived::default();
   prog.raw = vec![(1, 1), (1, 2), (2, 3)];
   prog.grp = vec![(1,), (2,)];
   prog.run();
   let vals = Db::default().rel("val", prog.val.iter(), &[]);
   let p = prog.explain_tot(&(1, 6)).unwrap();
   assert_eq!(p.rule, Some(1));
   let (premises, groups) = open_groups(&p, &vals);
   assert!(groups <= 1);
   let expected = vec![
      leaf("grp", "(1,)"),
      format!("val(1, 2)#Some(0)[{}]", leaf("raw", "(1, 1)")),
      format!("val(1, 4)#Some(0)[{}]", leaf("raw", "(1, 2)")),
   ];
   assert_eq!(renders(premises), expected);

   let db = Db::default()
      .rel("raw", prog.raw.iter(), &[])
      .rel("grp", prog.grp.iter(), &[])
      .rel("val", prog.val.iter(), &[0])
      .rel("tot", prog.tot.iter(), &[1]);
   for t in prog.tot.iter() {
      check_valid_grouped(&prog.explain_tot(t).unwrap(), &db, &vals);
   }
}

ascent! {
   #![generate_provenance]
   struct Sp;
   relation edge(u32, u32, u32);
   lattice dist(u32, u32, Dual<u32>);
   relation close(u32, u32);
   dist(x, y, Dual(*w)) <-- edge(x, y, w);                               // rule 0
   dist(x, z, Dual(w + l)) <-- edge(x, y, w), dist(y, z, ?Dual(l));      // rule 1
   close(x, y) <-- dist(x, y, ?Dual(d)), if *d <= 2;                     // rule 2
}

fn sp() -> Sp {
   let mut prog = Sp::default();
   prog.edge = vec![(1, 2, 1), (2, 3, 1), (1, 3, 5)];
   prog.run();
   prog
}

#[test]
fn lattice_final_value_names_last_improving_rule() {
   let prog = sp();
   let p = prog.explain_dist(&(1, 3, Dual(2))).unwrap();
   assert_eq!(p.relation, "dist");
   assert_eq!(p.fact, fact(&(1u32, 3u32, Dual(2u32))));
   assert_eq!(p.rule, Some(1));
   assert_eq!(premise_relations(&p), vec!["dist", "edge"]);
   assert_leaf(premise(&p, "edge"), "edge", "(1, 2, 1)");
}

#[test]
fn lattice_superseded_value_is_none() {
   let prog = sp();
   assert!(prog.explain_dist(&(1, 3, Dual(5))).is_none());
   assert!(prog.explain_dist(&(1, 3, Dual(3))).is_none());
   assert!(prog.explain_dist(&(3, 1, Dual(2))).is_none());
}

#[test]
fn lattice_fact_as_premise_is_a_leaf() {
   let prog = sp();
   let p = prog.explain_dist(&(1, 3, Dual(2))).unwrap();
   assert_leaf(premise(&p, "dist"), "dist", &fact(&(2u32, 3u32, Dual(1u32))));

   let c = prog.explain_close(&(1, 3)).unwrap();
   assert_eq!(c.relation, "close");
   assert_eq!(c.rule, Some(2));
   assert_eq!(c.premises.len(), 1);
   assert_leaf(&c.premises[0], "dist", &fact(&(1u32, 3u32, Dual(2u32))));
}

#[test]
fn ascent_run_with_captured_vector() {
   let v = vec![(1, 2), (2, 3), (3, 4)];
   let res = ascent_run! {
      #![generate_provenance]
      relation r(i32, i32);
      relation tc(i32, i32);
      r(*x, *y) <-- for (x, y) in v.iter();   // rule 0
      tc(x, y) <-- r(x, y);                   // rule 1
      tc(x, z) <-- r(x, y), tc(y, z);         // rule 2
   };
   let r12 = res.explain_r(&(1, 2)).unwrap();
   assert_eq!(r12.rule, Some(0));
   assert!(r12.premises.is_empty());
   let p = res.explain_tc(&(1, 4)).unwrap();
   assert_eq!(p.relation, "tc");
   assert_eq!(p.rule, Some(2));
   assert_eq!(premise_relations(&p), vec!["r", "tc"]);
   assert!(res.explain_tc(&(4, 1)).is_none());
}

ascent! {
   #![generate_provenance]
   struct G<T: Clone + Eq + std::hash::Hash + std::fmt::Debug>;
   relation edge(T, T);
   relation reach(T, T);
   reach(x, y) <-- edge(x, y);                  // rule 0
   reach(x, z) <-- reach(x, y), edge(y, z);     // rule 1
}

#[test]
fn generic_program_with_str() {
   let mut prog: G<&'static str> = G::default();
   prog.edge = vec![("a", "b"), ("b", "c")];
   prog.run();
   let p = prog.explain_reach(&("a", "c")).unwrap();
   assert_eq!(p.relation, "reach");
   assert_eq!(p.fact, "(\"a\", \"c\")");
   assert_eq!(p.rule, Some(1));
   assert_eq!(premise_relations(&p), vec!["edge", "reach"]);
   assert_eq!(premise(&p, "reach").fact, "(\"a\", \"b\")");
   assert_eq!(premise(&p, "reach").rule, Some(0));
   assert_leaf(premise(&p, "edge"), "edge", "(\"b\", \"c\")");
   assert!(prog.explain_reach(&("c", "a")).is_none());
}

#[test]
fn rerun_after_adding_facts_explains_old_and_new() {
   let mut prog = Tc::default();
   prog.edge = vec![(1, 2)];
   prog.run();
   assert_eq!(prog.explain_path(&(1, 2)).unwrap().rule, Some(0));
   assert!(prog.explain_path(&(1, 3)).is_none());

   prog.edge.push((2, 3));
   prog.run();
   let old = prog.explain_path(&(1, 2)).unwrap();
   assert_eq!(old.rule, Some(0));
   assert_leaf(&old.premises[0], "edge", "(1, 2)");
   assert_leaf(&prog.explain_edge(&(2, 3)).unwrap(), "edge", "(2, 3)");
   let new = prog.explain_path(&(1, 3)).unwrap();
   assert_eq!(new.rule, Some(1));
   assert_eq!(premise_relations(&new), vec!["edge", "path"]);
   assert_eq!(premise(&new, "path").fact, "(2, 3)");
   let db = tc_db(&prog);
   for t in prog.path.iter() {
      check_valid(&prog.explain_path(t).unwrap(), &db);
   }
}

#[test]
fn rerun_after_replacing_used_input_forgets_derivations() {
   let mut prog = tc_with(&[(1, 2), (2, 3)]);
   assert_eq!(prog.explain_path(&(1, 3)).unwrap().rule, Some(1));
   prog.edge[0] = (7, 8);
   prog.run();
   assert!(prog.explain_edge(&(1, 2)).is_none());
   assert_leaf(&prog.explain_edge(&(7, 8)).unwrap(), "edge", "(7, 8)");
   assert_leaf(&prog.explain_path(&(1, 2)).unwrap(), "path", "(1, 2)");
   assert_leaf(&prog.explain_path(&(1, 3)).unwrap(), "path", "(1, 3)");
   let p23 = prog.explain_path(&(2, 3)).unwrap();
   assert_eq!(p23.rule, Some(0));
   assert_eq!(p23.premises.len(), 1);
   assert_leaf(&p23.premises[0], "edge", "(2, 3)");
   let db = tc_db(&prog);
   for t in prog.path.iter() {
      check_valid(&prog.explain_path(t).unwrap(), &db);
   }
}

#[test]
fn rerun_after_removing_first_input_keeps_unaffected_derivations() {
   let mut prog = tc_with(&[(1, 2), (2, 3), (3, 4)]);
   let before_23 = render(&prog.explain_path(&(2, 3)).unwrap());
   let before_24 = render(&prog.explain_path(&(2, 4)).unwrap());
   let before_34 = render(&prog.explain_path(&(3, 4)).unwrap());
   prog.edge.remove(0);
   prog.run();
   assert_eq!(render(&prog.explain_path(&(2, 3)).unwrap()), before_23);
   assert_eq!(render(&prog.explain_path(&(2, 4)).unwrap()), before_24);
   assert_eq!(render(&prog.explain_path(&(3, 4)).unwrap()), before_34);
   assert_eq!(prog.explain_path(&(2, 4)).unwrap().rule, Some(1));
}

ascent! {
   #![generate_provenance]
   struct Unrelated;
   relation edge(i32, i32);
   relation path(i32, i32);
   relation note(i32);
   relation tagged(i32);
   path(x, y) <-- edge(x, y);                 // rule 0
   path(x, z) <-- edge(x, y), path(y, z);     // rule 1
   tagged(x) <-- note(x);                     // rule 2
}

#[test]
fn rerun_after_changing_unrelated_relation_keeps_derivations() {
   let mut prog = Unrelated::default();
   prog.edge = vec![(1, 2), (2, 3), (3, 4)];
   prog.note = vec![(1,)];
   prog.run();
   let before: Vec<((i32, i32), String)> =
      prog.path.iter().map(|t| (*t, render(&prog.explain_path(t).unwrap()))).collect();
   assert_eq!(prog.explain_tagged(&(1,)).unwrap().rule, Some(2));

   prog.note = vec![(5,)];
   prog.run();
   for (t, r) in &before {
      assert_eq!(&render(&prog.explain_path(t).unwrap()), r, "path{:?}", t);
   }
   assert!(prog.explain_note(&(1,)).is_none());
   assert_leaf(&prog.explain_tagged(&(1,)).unwrap(), "tagged", "(1,)");
   let t5 = prog.explain_tagged(&(5,)).unwrap();
   assert_eq!(t5.rule, Some(2));
   assert_eq!(t5.premises.len(), 1);
   assert_leaf(&t5.premises[0], "note", "(5,)");
}

#[test]
fn rerun_lattice_input_replaced_forgets_derivations() {
   let mut prog = Sp::default();
   prog.edge = vec![(1, 2, 1), (2, 3, 1)];
   prog.run();
   assert_eq!(prog.explain_dist(&(1, 3, Dual(2))).unwrap().rule, Some(1));
   prog.edge[0] = (7, 8, 1);
   prog.run();
   assert_leaf(&prog.explain_dist(&(1, 2, Dual(1))).unwrap(), "dist", &fact(&(1u32, 2u32, Dual(1u32))));
   assert_leaf(&prog.explain_dist(&(1, 3, Dual(2))).unwrap(), "dist", &fact(&(1u32, 3u32, Dual(2u32))));
   let d23 = prog.explain_dist(&(2, 3, Dual(1))).unwrap();
   assert_eq!(d23.rule, Some(0));
   assert_leaf(&d23.premises[0], "edge", "(2, 3, 1)");
}

ascent! {
   #![generate_provenance]
   struct Counter;
   relation n(u32);
   n(0);                                 // rule 0
   n(x + 1) <-- n(x), if *x < 300;      // rule 1
}

/// Walks the proof of `n(top)` down its premises without recursion (the chain is deep): `top + 1`
/// nodes, one per value from `top` down to the fact rule's `n(0)`.
fn check_counter_chain(p: &Proof, top: u32) {
   let mut cur = p;
   for k in (0..=top).rev() {
      assert_eq!(cur.relation, "n");
      assert_eq!(cur.fact, fact(&(k,)));
      if k == 0 {
         assert_fact_rule_fact(cur, "n", "(0,)", 0);
      } else {
         assert_eq!(cur.rule, Some(1), "n({})", k);
         assert_eq!(cur.premises.len(), 1);
         cur = &cur.premises[0];
      }
   }
}

#[test]
fn deep_derivation_chain() {
   let mut prog = Counter::default();
   prog.run();
   check_counter_chain(&prog.explain_n(&(300,)).unwrap(), 300);
   assert!(prog.explain_n(&(301,)).is_none());
   check_counter_chain(&prog.explain_n(&(150,)).unwrap(), 150);
}

#[test]
fn macro_definitions_do_not_shift_rule_numbers() {
   ascent! {
      #![generate_provenance]
      struct Mac;
      relation a(i32);
      relation b(i32);
      relation c(i32);
      relation first(i32);
      relation out(i32);
      relation more(i32);
      first(x) <-- a(x);                  // rule 0
      macro ab($x: expr) {
         a($x), b($x)
      }
      macro okb($x: expr) {
         b($x), !c($x)
      }
      out(x) <-- c(x), ab!(x);            // rule 1
      more(x) <-- a(x), okb!(x);          // rule 2
   }
   let mut prog = Mac::default();
   prog.a = vec![(1,), (2,)];
   prog.b = vec![(1,), (2,)];
   prog.c = vec![(1,)];
   prog.run();
   assert_eq!(prog.explain_first(&(1,)).unwrap().rule, Some(0));
   let o = prog.explain_out(&(1,)).unwrap();
   assert_eq!(o.rule, Some(1));
   assert_eq!(renders(&o.premises), vec![leaf("a", "(1,)"), leaf("b", "(1,)"), leaf("c", "(1,)")]);
   let negated = Db::default().rel("c", prog.c.iter(), &[]);
   let m = prog.explain_more(&(2,)).unwrap();
   assert_eq!(m.rule, Some(2));
   let (premises, groups) = open_groups(&m, &negated);
   assert!(groups <= 1);
   assert_eq!(renders(premises), vec![leaf("a", "(2,)"), leaf("b", "(2,)")]);
   assert!(prog.explain_more(&(1,)).is_none());
}

#[test]
fn zero_arity_relation() {
   ascent! {
      #![generate_provenance]
      struct Zero;
      relation a(i32);
      relation any();
      relation out(i32);
      any() <-- a(_);              // rule 0
      out(x) <-- a(x), any();      // rule 1
   }
   let mut prog = Zero::default();
   prog.a = vec![(1,)];
   prog.run();
   let any = prog.explain_any(&()).unwrap();
   assert_eq!(any.relation, "any");
   assert_eq!(any.fact, "()");
   assert_eq!(any.rule, Some(0));
   assert_leaf(&any.premises[0], "a", "(1,)");
   let o = prog.explain_out(&(1,)).unwrap();
   assert_eq!(premise_relations(&o), vec!["a", "any"]);
   assert_eq!(premise(&o, "any").fact, "()");
   assert_eq!(premise(&o, "any").rule, Some(0));
   let empty = Zero::default();
   assert!(empty.explain_any(&()).is_none());
}

#[test]
fn string_facts_in_rule_heads() {
   ascent! {
      #![generate_provenance]
      struct Greet;
      relation person(String, u32);
      relation greeting(String);
      relation adult(String, u32);
      greeting(format!("hi {}", p)) <-- person(p, _);         // rule 0
      adult(p.clone(), *a) <-- person(p, a), if *a >= 18;     // rule 1
   }
   let mut prog = Greet::default();
   prog.person = vec![("ann".to_string(), 30), ("bob".to_string(), 9)];
   prog.run();
   let g = prog.explain_greeting(&("hi bob".to_string(),)).unwrap();
   assert_eq!(g.rule, Some(0));
   assert_eq!(renders(&g.premises), vec![leaf("person", "(\"bob\", 9)")]);
   let a = prog.explain_adult(&("ann".to_string(), 30)).unwrap();
   assert_eq!(a.rule, Some(1));
   assert_eq!(renders(&a.premises), vec![leaf("person", "(\"ann\", 30)")]);
   assert!(prog.explain_adult(&("bob".to_string(), 9)).is_none());
}
