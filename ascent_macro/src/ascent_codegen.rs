#![deny(warnings)]
use std::collections::HashSet;

use itertools::{Either, Itertools};
use proc_macro2::{Ident, Span, TokenStream};
use syn::spanned::Spanned;
use syn::{Expr, Type, parse_quote, parse_quote_spanned, parse2};

use crate::ascent_hir::{IndexValType, IrAggClause, IrHeadClause, IrRelation};
use crate::ascent_mir::MirRelationVersion::*;
use crate::ascent_mir::{
   AscentMir, MirBodyClause, MirBodyItem, MirRelation, MirRelationVersion, MirRule, MirScc,
   ir_relation_version_var_name, mir_rule_summary, mir_summary,
};
use crate::ascent_syntax::{CondClause, RelationIdentity};
use crate::utils::{TokenStreamExtensions, exp_cloned, expr_to_ident, tuple, tuple_spanned, tuple_type};

pub(crate) fn compile_mir(mir: &AscentMir, is_ascent_run: bool) -> proc_macro2::TokenStream {
   let mut relation_fields = vec![];
   let mut field_defaults = vec![];

   let sorted_relations_ir_relations = mir.relations_ir_relations.iter().sorted_by_key(|(rel, _)| &rel.name);
   for (rel, rel_indices) in sorted_relations_ir_relations {
      let name = &rel.name;
      let rel_attrs = &mir.relations_metadata[rel].attributes;
      let sorted_rel_index_names = rel_indices.iter().map(|ind| format!("{}", ind.ir_name())).sorted();
      let rel_indices_comment = format!("\nlogical indices: {}", sorted_rel_index_names.into_iter().join("; "));
      let rel_type = rel_type(rel, mir);
      let rel_ind_common = rel_ind_common_var_name(rel);
      let rel_ind_common_type = rel_ind_common_type(rel, mir);
      relation_fields.push(quote! {
         #(#rel_attrs)*
         #[doc = #rel_indices_comment]
         pub #name: #rel_type,
         #rel_ind_common: #rel_ind_common_type,
      });
      field_defaults.push(quote! {#name : Default::default(), #rel_ind_common: Default::default(),});
      if mir.config.generate_provenance {
         let rows = provenance_rows_var_name(rel);
         let row_type = tuple_type(&rel.field_types);
         relation_fields.push(quote! {
            #rows: ::ascent::internal::RelFullIndexType<#row_type, usize>,
         });
         field_defaults.push(quote! {#rows: Default::default(),});
         if !rel.is_lattice {
            let facts = provenance_facts_var_name(rel);
            relation_fields.push(quote! {
               #facts: ::std::vec::Vec<#row_type>,
            });
            field_defaults.push(quote! {#facts: Default::default(),});
         }
      }
      if rel.is_lattice && mir.is_parallel {
         let lattice_mutex_name = lattice_insertion_mutex_var_name(rel);
         relation_fields.push(quote! {
            #lattice_mutex_name: ::std::vec::Vec<std::sync::Mutex<()>>,
         });
         field_defaults.push(quote! {#lattice_mutex_name: {
            let len = ::ascent::internal::shards_count();
            let mut v = Vec::with_capacity(len); for _ in 0..len {v.push(Default::default())};
            v },
         })
      }
      let sorted_indices = rel_indices.iter().sorted_by_cached_key(|ind| ind.ir_name());
      for ind in sorted_indices {
         let name = &ind.ir_name();
         let rel_index_type = rel_index_type(ind, mir);
         relation_fields.push(quote! {
            #name: #rel_index_type,
         });
         field_defaults.push(quote! {#name : Default::default(),});
      }
   }

   if mir.config.generate_provenance {
      relation_fields.push(quote! {
         __provenance: ::ascent::internal::Provenance,
      });
      field_defaults.push(quote! {__provenance: Default::default(),});
   }

   let sccs_ordered = &mir.sccs;
   let mut rule_time_fields = vec![];
   let mut rule_time_fields_defaults = vec![];
   for i in 0..mir.sccs.len() {
      for (rule_ind, _rule) in mir.sccs[i].rules.iter().enumerate() {
         let name = rule_time_field_name(i, rule_ind);
         rule_time_fields.push(quote! {
            pub #name: std::time::Duration,
         });
         rule_time_fields_defaults.push(quote! {
            #name: std::time::Duration::ZERO,
         });
      }
   }

   let mut sccs_compiled = vec![];
   for (i, _scc) in sccs_ordered.iter().enumerate() {
      let msg = format!("scc {}", i);
      let scc_compiled = compile_mir_scc(mir, i);
      sccs_compiled.push(quote! {
         ascent::internal::comment(#msg);
         {
            let _scc_start_time = ::ascent::internal::Instant::now();
            #scc_compiled
            _self.scc_times[#i] += _scc_start_time.elapsed();
         }
      });
   }

   let update_indices_body = compile_update_indices_function_body(mir);
   let relation_sizes_body = compile_relation_sizes_body(mir);
   let scc_times_summary_body = compile_scc_times_summary_body(mir);

   let mut type_constraints = vec![];
   let mut field_type_names = HashSet::<String>::new();
   let mut lat_field_type_names = HashSet::<String>::new();

   for relation in mir.relations_ir_relations.keys().sorted_by_key(|rel| &rel.name) {
      use crate::quote::ToTokens;
      for (i, field_type) in relation.field_types.iter().enumerate() {
         let is_lat = relation.is_lattice && i == relation.field_types.len() - 1;
         let add = if let Type::Path(path) = field_type {
            let container = if is_lat { &mut lat_field_type_names } else { &mut field_type_names };
            container.insert(path.path.clone().into_token_stream().to_string())
         } else {
            true
         };
         if add {
            let type_constraints_type = if is_lat {
               quote_spanned!(field_type.span()=>LatTypeConstraints)
            } else {
               quote_spanned!(field_type.span()=>TypeConstraints)
            };
            type_constraints.push(quote_spanned! {field_type.span()=>
               let _type_constraints : ascent::internal::#type_constraints_type<#field_type>;
            });
            if mir.is_parallel {
               type_constraints.push(quote_spanned! {field_type.span()=>
                  let _par_constraints : ascent::internal::ParTypeConstraints<#field_type>;
               });
            }
         }
      }
   }

   let mut relation_initializations = vec![];
   for (rel, md) in mir.relations_metadata.iter().sorted_by_key(|(rel, _)| &rel.name) {
      if let Some(ref init) = md.initialization {
         let rel_name = &rel.name;
         relation_initializations.push(quote! {
            _self.#rel_name = #init;
         });
      }
   }
   if !relation_initializations.is_empty() {
      relation_initializations.push(quote! {
         _self.update_indices_priv();
      })
   }

   let par_usings = if mir.is_parallel {
      quote! {
         use ascent::rayon::iter::ParallelBridge;
         use ascent::rayon::iter::ParallelIterator;
         use ascent::internal::CRelIndexRead;
         use ascent::internal::CRelIndexReadAll;
         use ascent::internal::Freezable;
      }
   } else {
      quote! {}
   };

   let more_usings = if !mir.is_parallel {
      quote! {
         use ascent::internal::RelIndexWrite;
      }
   } else {
      quote! {
         use ascent::internal::CRelIndexWrite;
      }
   };

   let run_usings = quote! {
      use core::cmp::PartialEq;
      use ascent::internal::{RelIndexRead, RelIndexReadAll, ToRelIndex0, TupleOfBorrowed};
      #more_usings
      #par_usings
   };

   let generate_run_timeout = !is_ascent_run && mir.config.generate_run_partial;
   let run_func = if is_ascent_run {
      quote! {}
   } else if generate_run_timeout {
      quote! {
         #[doc = "Runs the Ascent program to a fixed point."]
         pub fn run(&mut self) {
            #![allow(clippy::all)]
            self.run_timeout(::std::time::Duration::MAX);
         }
      }
   } else {
      quote! {
         #[allow(unused_imports, noop_method_call, suspicious_double_ref_op)]
         #[doc = "Runs the Ascent program to a fixed point."]
         pub fn run(&mut self) {
            #![allow(clippy::all)]
            macro_rules! __check_return_conditions {() => {};}
            #run_usings
            self.update_indices_priv();
            let _self = self;
            #(#sccs_compiled)*
         }
      }
   };
   let run_timeout_func = if !generate_run_timeout {
      quote! {}
   } else {
      quote! {
         #[allow(unused_imports, noop_method_call, suspicious_double_ref_op)]
         #[doc = "Runs the Ascent program to a fixed point or until the timeout is reached. In case of a timeout returns false"]
         pub fn run_timeout(&mut self, timeout: ::std::time::Duration) -> bool {
            let __start_time = ::ascent::internal::Instant::now();
            macro_rules! __check_return_conditions {() => {
               if timeout < ::std::time::Duration::MAX && __start_time.elapsed() >= timeout {return false;}
            };}
            #run_usings
            self.update_indices_priv();
            let _self = self;
            #(#sccs_compiled)*
            true
         }
      }
   };
   let run_code = if !is_ascent_run {
      quote! {}
   } else {
      quote! {
         macro_rules! __check_return_conditions {() => {};}
         #run_usings
         let _self = &mut __run_res;
         #(#relation_initializations)*
         #(#sccs_compiled)*
      }
   };

   let relation_initializations_for_default_impl = if is_ascent_run { vec![] } else { relation_initializations };
   let summary = mir_summary(mir);

   let (ty_impl_generics, ty_ty_generics, ty_where_clause) = mir.signatures.split_ty_generics_for_impl();
   let (impl_impl_generics, impl_ty_generics, impl_where_clause) = mir.signatures.split_impl_generics_for_impl();

   let ty_signature = &mir.signatures.declaration;
   if let Some(impl_signature) = &mir.signatures.implementation {
      assert_eq!(ty_signature.ident, impl_signature.ident, "The identifiers of struct and impl must match");
   }

   let ty_ty_generics_str = quote!(#ty_ty_generics).to_string();
   let impl_ty_generics_str = quote!(#impl_ty_generics).to_string();
   assert_eq!(
      ty_ty_generics_str, impl_ty_generics_str,
      "The generic parameters of struct ({ty_ty_generics_str}) and impl ({impl_ty_generics_str}) must match"
   );

   let vis = &ty_signature.visibility;
   let struct_name = &ty_signature.ident;
   let struct_attrs = &ty_signature.attrs;
   let summary_fn = if is_ascent_run {
      quote! {
         pub fn summary(&self) -> &'static str {#summary}
      }
   } else {
      quote! {
         pub fn summary() -> &'static str {#summary}
      }
   };
   let rule_time_fields = if mir.config.include_rule_times { rule_time_fields } else { vec![] };
   let rule_time_fields_defaults = if mir.config.include_rule_times { rule_time_fields_defaults } else { vec![] };

   let mut rel_codegens = vec![];
   for rel in mir.relations_ir_relations.keys() {
      let Some(ds_attr) = &mir.relations_metadata[rel].ds_attr else { continue };
      let macro_path = &ds_attr.path;
      let macro_input = rel_ds_macro_input(rel, mir);
      rel_codegens.push(quote_spanned! { macro_path.span()=> #macro_path::rel_codegen!{#macro_input} });
   }

   let explain_impl = if mir.config.generate_provenance {
      let row_less_impl = compile_row_less_impl(mir);
      let explain_impl = compile_explain_impl(mir);
      quote! { #row_less_impl #explain_impl }
   } else {
      quote! {}
   };

   let sccs_count = sccs_ordered.len();
   let res = quote! {
      #(#rel_codegens)*

      #(#struct_attrs)*
      #vis struct #struct_name #ty_impl_generics #ty_where_clause {
         #(#relation_fields)*
         scc_times: [std::time::Duration; #sccs_count],
         scc_iters: [usize; #sccs_count],
         #(#rule_time_fields)*
         update_time_nanos: std::sync::atomic::AtomicU64,
         update_indices_duration: std::time::Duration,
      }
      impl #impl_impl_generics #struct_name #impl_ty_generics #impl_where_clause {
         #run_func

         #run_timeout_func
         // TODO remove pub update_indices at some point
         #[allow(noop_method_call, suspicious_double_ref_op)]
         fn update_indices_priv(&mut self) {
            #![allow(clippy::all)]
            let before = ::ascent::internal::Instant::now();
            #update_indices_body
            self.update_indices_duration += before.elapsed();
         }

         #[deprecated = "Explicit call to update_indices not required anymore."]
         pub fn update_indices(&mut self) {
            self.update_indices_priv();
         }
         fn type_constraints() {
            #![allow(clippy::all)]
            #(#type_constraints)*
         }
         #summary_fn

         pub fn relation_sizes_summary(&self) -> String {
            #![allow(clippy::all)]
            #relation_sizes_body
         }
         pub fn scc_times_summary(&self) -> String {
            #![allow(clippy::all)]
            #scc_times_summary_body
         }
      }
      #explain_impl
      impl #impl_impl_generics Default for #struct_name #impl_ty_generics #impl_where_clause {
         fn default() -> Self {
            let mut _self = #struct_name {
               #(#field_defaults)*
               scc_times: [std::time::Duration::ZERO; #sccs_count],
               scc_iters: [0; #sccs_count],
               #(#rule_time_fields_defaults)*
               update_time_nanos: Default::default(),
               update_indices_duration: std::time::Duration::default()
            };
            #(#relation_initializations_for_default_impl)*
            _self
         }
      }
   };
   if !is_ascent_run {
      res
   } else {
      quote! {
         {{
            #![allow(unused_imports, noop_method_call, suspicious_double_ref_op, clippy::all)]
            #res
            let mut __run_res: #struct_name #ty_ty_generics = #struct_name::default();
            {
               ascent::internal::comment("running...");
               #run_code
            }
            __run_res
         }}
      }
   }
}

fn rel_ind_common_type(rel: &RelationIdentity, mir: &AscentMir) -> Type {
   match &mir.relations_metadata[rel].ds_attr {
      None => {
         assert!(rel.is_lattice);
         parse_quote! { () }
      },
      Some(ds_attr) => {
         let macro_path = &ds_attr.path;
         let macro_input = rel_ds_macro_input(rel, mir);
         parse_quote_spanned! { macro_path.span()=> #macro_path::rel_ind_common!(#macro_input) }
      },
   }
}

fn rel_index_type(rel: &IrRelation, mir: &AscentMir) -> Type {
   let span = rel.relation.name.span();
   let key_type = rel.key_type();
   let value_type = rel.value_type();

   let is_lat_full_index = rel.relation.is_lattice && &mir.lattices_full_indices[&rel.relation] == rel;

   if rel.relation.is_lattice {
      let res = if !mir.is_parallel {
         if is_lat_full_index {
            quote_spanned! { span=>ascent::internal::RelFullIndexType<#key_type, #value_type> }
         } else {
            quote_spanned! { span=>ascent::internal::LatticeIndexType<#key_type, #value_type> }
         }
      } else {
         // parallel
         if is_lat_full_index {
            quote_spanned! { span=>ascent::internal::CRelFullIndex<#key_type, #value_type> }
         } else if rel.is_no_index() {
            quote_spanned! { span=>ascent::internal::CRelNoIndex<#value_type> }
         } else {
            quote_spanned! { span=>ascent::internal::CRelIndex<#key_type, #value_type> }
         }
      };
      syn::parse2(res).unwrap()
   } else {
      let macro_path = &mir.relations_metadata[&rel.relation].ds_attr.as_ref().unwrap().path;
      let span = macro_path.span();
      let macro_input = rel_ds_macro_input(&rel.relation, mir);
      if rel.is_full_index() {
         parse_quote_spanned! {span=> #macro_path::rel_full_ind!(#macro_input, #key_type, #value_type)}
      } else {
         let ind = rel_index_to_macro_input(&rel.indices);
         parse_quote_spanned! {span=> #macro_path::rel_ind!(#macro_input, #ind, #key_type, #value_type)}
      }
   }
}

fn rel_type(rel: &RelationIdentity, mir: &AscentMir) -> Type {
   let field_types = tuple_type(&rel.field_types);

   match &mir.relations_metadata[rel].ds_attr {
      None => {
         assert!(rel.is_lattice);
         if mir.is_parallel {
            parse_quote! {::ascent::boxcar::Vec<::std::sync::RwLock<#field_types>>}
         } else {
            parse_quote! {::std::vec::Vec<#field_types>}
         }
      },
      Some(ds_attr) => {
         let macro_path = &ds_attr.path;
         let macro_input = rel_ds_macro_input(rel, mir);
         parse_quote_spanned! {macro_path.span()=> #macro_path::rel!(#macro_input) }
      },
   }
}

fn rel_index_to_macro_input(ind: &[usize]) -> TokenStream {
   let indices = ind.iter().cloned().map(syn::Index::from);
   quote! { [#(#indices),*] }
}

fn rel_ds_macro_input(rel: &RelationIdentity, mir: &AscentMir) -> TokenStream {
   let span = rel.name.span();
   let field_types = tuple_type(&rel.field_types);
   let indices = mir.relations_ir_relations[rel]
      .iter()
      .sorted_by_key(|r| &r.indices)
      .map(|ir_rel| rel_index_to_macro_input(&ir_rel.indices));
   let args = &mir.relations_metadata[rel].ds_attr.as_ref().expect("must have the ds attribute").args;
   let par: Ident = if mir.is_parallel {
      parse_quote_spanned! {span=> par}
   } else {
      parse_quote_spanned! {span=> ser}
   };
   let name = Ident::new(&format!("{}_{}", mir.signatures.declaration.ident, rel.name), span);
   quote! {
      #name,
      #field_types,
      [#(#indices),*],
      #par,
      (#args)
   }
}

fn rule_time_field_name(scc_ind: usize, rule_ind: usize) -> Ident {
   Ident::new(&format!("rule{}_{}_duration", scc_ind, rule_ind), Span::call_site())
}

fn compile_mir_scc(mir: &AscentMir, scc_ind: usize) -> proc_macro2::TokenStream {
   let scc = &mir.sccs[scc_ind];
   let mut move_total_to_delta = vec![];
   let mut shift_delta_to_total_new_to_delta = vec![];
   let mut move_total_to_field = vec![];
   let mut freeze_code = vec![];
   let mut unfreeze_code = vec![];

   let _self = quote! { _self };

   use std::iter::once;
   let sorted_dynamic_relations = scc.dynamic_relations.iter().sorted_by_cached_key(|(rel, _)| rel.name.clone());
   for rel in sorted_dynamic_relations.flat_map(|(rel, indices)| {
      once(Either::Left(rel)).chain(indices.iter().sorted_by_cached_key(|rel| rel.ir_name()).map(Either::Right))
   }) {
      let (ir_name, ty) = match rel {
         Either::Left(rel) => (rel_ind_common_var_name(rel), rel_ind_common_type(rel, mir)),
         Either::Right(rel_ind) => (rel_ind.ir_name(), rel_index_type(rel_ind, mir)),
      };
      let delta_var_name = ir_relation_version_var_name(&ir_name, MirRelationVersion::Delta);
      let total_var_name = ir_relation_version_var_name(&ir_name, MirRelationVersion::Total);
      let new_var_name = ir_relation_version_var_name(&ir_name, MirRelationVersion::New);
      let total_field = &ir_name;
      move_total_to_delta.push(quote_spanned! {ir_name.span()=>
         let mut #delta_var_name: #ty = ::std::mem::take(&mut #_self.#total_field);
         let mut #total_var_name : #ty = Default::default();
         let mut #new_var_name : #ty = Default::default();
      });

      match rel {
         Either::Left(_rel_ind_common) => {
            shift_delta_to_total_new_to_delta.push(quote_spanned!{ir_name.span()=>
               ::ascent::internal::RelIndexMerge::merge_delta_to_total_new_to_delta(&mut #new_var_name, &mut #delta_var_name, &mut #total_var_name);
            });
            move_total_to_delta.push(quote_spanned! {ir_name.span()=>
               ::ascent::internal::RelIndexMerge::init(&mut #new_var_name, &mut #delta_var_name, &mut #total_var_name);
            });
         },
         Either::Right(ir_rel) => {
            let delta_expr = expr_for_rel_write(&MirRelation::from(ir_rel.clone(), Delta), mir);
            let total_expr = expr_for_rel_write(&MirRelation::from(ir_rel.clone(), Total), mir);
            let new_expr = expr_for_rel_write(&MirRelation::from(ir_rel.clone(), New), mir);

            shift_delta_to_total_new_to_delta.push(quote_spanned!{ir_name.span()=>
               ::ascent::internal::RelIndexMerge::merge_delta_to_total_new_to_delta(&mut #new_expr, &mut #delta_expr, &mut #total_expr);
            });
            move_total_to_delta.push(quote_spanned! {ir_name.span()=>
               ::ascent::internal::RelIndexMerge::init(&mut #new_expr, &mut #delta_expr, &mut #total_expr);
            });
         },
      }

      move_total_to_field.push(quote_spanned! {ir_name.span()=>
         #_self.#total_field = #total_var_name;
      });

      if mir.is_parallel {
         freeze_code.push(quote_spanned! {ir_name.span()=>
            #total_var_name.freeze();
            #delta_var_name.freeze();
         });

         unfreeze_code.push(quote_spanned! {ir_name.span()=>
            #total_var_name.unfreeze();
            #delta_var_name.unfreeze();
         });
      }
   }
   let sorted_body_only_relations = scc.body_only_relations.iter().sorted_by_cached_key(|(rel, _)| rel.name.clone());
   for rel in sorted_body_only_relations.flat_map(|(rel, indices)| {
      let sorted_indices = indices.iter().sorted_by_cached_key(|rel| rel.ir_name());
      once(Either::Left(rel)).chain(sorted_indices.map(Either::Right))
   }) {
      let (ir_name, ty) = match rel {
         Either::Left(rel) => (rel_ind_common_var_name(rel), rel_ind_common_type(rel, mir)),
         Either::Right(rel_ind) => (rel_ind.ir_name(), rel_index_type(rel_ind, mir)),
      };
      let total_var_name = ir_relation_version_var_name(&ir_name, MirRelationVersion::Total);
      let total_field = &ir_name;

      if mir.is_parallel {
         move_total_to_delta.push(quote_spanned! {ir_name.span()=>
            #_self.#total_field.freeze();
         });
      }

      move_total_to_delta.push(quote_spanned! {ir_name.span()=>
         let #total_var_name: #ty = std::mem::take(&mut #_self.#total_field);
      });

      move_total_to_field.push(quote_spanned! {ir_name.span()=>
         #_self.#total_field = #total_var_name;
      });
   }

   let rule_parallelism = mir.config.inter_rule_parallelism && mir.is_parallel;

   let mut evaluate_rules = vec![];

   for (i, rule) in scc.rules.iter().enumerate() {
      let msg = mir_rule_summary(rule);
      let rule_compiled = compile_mir_rule(rule, scc, mir);
      let rule_time_field = rule_time_field_name(scc_ind, i);
      let (before_rule_var, update_rule_time_field) = if mir.config.include_rule_times {
         (
            quote! {let before_rule = ::ascent::internal::Instant::now();},
            quote! {_self.#rule_time_field += before_rule.elapsed();},
         )
      } else {
         (quote! {}, quote! {})
      };
      evaluate_rules.push(if rule_parallelism {
         quote! {
            ascent::internal::comment(#msg);
            __scope.spawn(|_| {
               #before_rule_var
               ascent::internal::run_rule(|| {
                  #rule_compiled
               });
               #update_rule_time_field
            });
         }
      } else {
         quote! {
            #before_rule_var
            ascent::internal::comment(#msg);
            ascent::internal::run_rule(|| {
               #rule_compiled
            });
            #update_rule_time_field
         }
      });
   }

   let evaluate_rules = if rule_parallelism {
      quote! {
         ascent::rayon::scope(|__scope| {
            #(#evaluate_rules)*
         });
      }
   } else {
      quote! { #(#evaluate_rules)* }
   };

   let changed_var_def_code = if !mir.is_parallel {
      quote! { let mut __changed = false; }
   } else {
      quote! { let __changed = std::sync::atomic::AtomicBool::new(false); }
   };
   let check_changed_code = if !mir.is_parallel {
      quote! {__changed}
   } else {
      quote! {__changed.load(std::sync::atomic::Ordering::Relaxed)}
   };

   let evaluate_rules_loop = if scc.is_looping {
      quote! {
         #[allow(unused_assignments, unused_variables)]
         loop {
            #changed_var_def_code

            #(#freeze_code)*
            // evaluate rules
            #evaluate_rules

            #(#unfreeze_code)*
            #(#shift_delta_to_total_new_to_delta)*
            _self.scc_iters[#scc_ind] += 1;
            if !#check_changed_code {break;}
            __check_return_conditions!();
         }

      }
   } else {
      quote! {
         #[allow(unused_assignments, unused_variables)]
         {
            #changed_var_def_code
            #(#freeze_code)*

            #evaluate_rules

            #(#unfreeze_code)*

            #(#shift_delta_to_total_new_to_delta)*
            #(#shift_delta_to_total_new_to_delta)*
            _self.scc_iters[#scc_ind] += 1;
            __check_return_conditions!();
         }
      }
   };
   quote! {
      // define variables for delta and new versions of dynamic relations in the scc
      // move total versions of dynamic indices to delta
      #(#move_total_to_delta)*

      #evaluate_rules_loop

      #(#move_total_to_field)*
   }
}

fn compile_relation_sizes_body(mir: &AscentMir) -> proc_macro2::TokenStream {
   let mut write_sizes = vec![];
   for r in mir.relations_ir_relations.keys().sorted_by_key(|r| &r.name) {
      let rel_name = &r.name;
      let rel_name_str = r.name.to_string();
      write_sizes.push(quote! {
         writeln!(&mut res, "{} size: {}", #rel_name_str, self.#rel_name.len()).unwrap();
      });
   }
   quote! {
      use std::fmt::Write;
      let mut res = String::new();
      #(#write_sizes)*
      res
   }
}

fn compile_scc_times_summary_body(mir: &AscentMir) -> proc_macro2::TokenStream {
   let mut res = vec![];
   for i in 0..mir.sccs.len() {
      let i_str = format!("{}", i);
      res.push(quote!{
         writeln!(&mut res, "scc {}: iterations: {}, time: {:?}", #i_str, self.scc_iters[#i], self.scc_times[#i]).unwrap();
      });
      if mir.config.include_rule_times {
         let mut sum_of_rule_times = quote! { std::time::Duration::ZERO };
         for (rule_ind, _rule) in mir.sccs[i].rules.iter().enumerate() {
            let rule_time_field = rule_time_field_name(i, rule_ind);
            sum_of_rule_times = quote! { #sum_of_rule_times + self.#rule_time_field};
         }
         res.push(quote! {
            let sum_of_rule_times = #sum_of_rule_times;
            writeln!(&mut res, "  sum of rule times: {:?}", sum_of_rule_times).unwrap();
         });
         for (rule_ind, rule) in mir.sccs[i].rules.iter().enumerate() {
            let rule_time_field = rule_time_field_name(i, rule_ind);
            let rule_summary = mir_rule_summary(rule);
            res.push(quote! {
               writeln!(&mut res, "  rule {}\n    time: {:?}", #rule_summary, self.#rule_time_field).unwrap();
            });
         }
         res.push(quote! {
            writeln!(&mut res, "-----------------------------------------").unwrap();
         });
      }
   }
   let update_indices_time_code = quote! {
      writeln!(&mut res, "update_indices time: {:?}", self.update_indices_duration).unwrap();
   };
   quote! {
      use std::fmt::Write;
      let mut res = String::new();
      #update_indices_time_code
      #(#res)*
      res
   }
}

fn compile_update_indices_function_body(mir: &AscentMir) -> proc_macro2::TokenStream {
   let par = mir.is_parallel;
   let mut res = vec![];
   if par {
      res.push(quote! { use ascent::rayon::iter::{IntoParallelIterator, ParallelIterator}; })
   }
   let (rel_index_write_trait, index_insert_fn) = if !par {
      (quote! {ascent::internal::RelIndexWrite}, quote! {index_insert})
   } else {
      (quote! {ascent::internal::CRelIndexWrite}, quote! {index_insert})
   };
   let sorted_relations_ir_relations = mir.relations_ir_relations.iter().sorted_by_key(|(rel, _)| &rel.name);
   for (r, indices_set) in sorted_relations_ir_relations {
      let _ref = if !par {
         quote! {&mut}
      } else {
         quote! {&}
      }
      .with_span(r.name.span());
      let ind_common = rel_ind_common_var_name(r);
      let rel_index_write_trait = rel_index_write_trait.clone().with_span(r.name.span());
      let _self = quote_spanned! {r.name.span().resolved_at(Span::call_site())=> self };
      let to_rel_index_fn = if !par {
         quote! {to_rel_index_write}
      } else {
         quote! {to_c_rel_index_write}
      };
      let to_rel_index = if r.is_lattice {
         quote! {}
      } else {
         quote! {.#to_rel_index_fn(#_ref #_self.#ind_common) }
      };

      let mut update_indices = vec![];
      for ind in indices_set.iter().sorted_by_cached_key(|rel| rel.ir_name()) {
         let ind_name = &ind.ir_name();
         let selection_tuple: Vec<Expr> = ind
            .indices
            .iter()
            .map(|&i| {
               let ind = syn::Index::from(i);
               parse_quote_spanned! {r.name.span()=> tuple.#ind.clone()}
            })
            .collect_vec();
         let selection_tuple = tuple_spanned(&selection_tuple, r.name.span());
         let entry_val = index_get_entry_val_for_insert(
            ind,
            &parse_quote_spanned! {r.name.span()=> tuple},
            &parse_quote_spanned! {r.name.span()=> _i},
         );
         let _pre_ref = if r.is_lattice { quote!() } else { _ref.clone() };
         update_indices.push(quote_spanned! {r.name.span()=>
            let selection_tuple = #selection_tuple;
            let rel_ind = #_ref #_self.#ind_name;
            #rel_index_write_trait::#index_insert_fn(#_pre_ref rel_ind #to_rel_index, selection_tuple, #entry_val);
         });
      }
      let rel_name = &r.name;
      let maybe_lock = if r.is_lattice && mir.is_parallel {
         quote_spanned! {r.name.span()=> let tuple = tuple.read().unwrap(); }
      } else {
         quote! {}
      };
      if mir.config.generate_provenance {
         let rows = provenance_rows_var_name(r);
         update_indices.push(quote_spanned! {r.name.span()=>
            #_self.#rows.entry(tuple.clone()).or_insert(_i);
         });
         // The rows of a row-less relation are the provenance's own, not reindexed from the field
         let clear_rows = if r.is_lattice {
            quote_spanned! {r.name.span()=> #_self.#rows.clear(); }
         } else {
            let row_less = provenance_row_less(r, &_self, r.name.span());
            quote_spanned! {r.name.span()=> if !#row_less { #_self.#rows.clear(); } }
         };
         res.push(clear_rows);
      }
      if !par {
         res.push(quote_spanned! {r.name.span()=>
            for (_i, tuple) in #_self.#rel_name.iter().enumerate() {
               #maybe_lock
               #(#update_indices)*
            }
         });
      } else {
         res.push(quote_spanned! {r.name.span()=>
            (0..#_self.#rel_name.len()).into_par_iter().for_each(|_i| {
               let tuple = &#_self.#rel_name[_i];
               #maybe_lock
               #(#update_indices)*
            });
         });
      }
   }

   let relocate_derivations = if mir.config.generate_provenance {
      provenance_relocate_derivations(mir)
   } else {
      quote! {}
   };
   quote! {
      use ascent::internal::ToRelIndex0;
      use #rel_index_write_trait;
      #relocate_derivations
      #(#res)*
   }
}

fn compile_cond_clause(cond: &CondClause, body: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
   match cond {
      CondClause::IfLet(if_let_clause) => {
         let pat = &if_let_clause.pattern;
         let expr = &if_let_clause.exp;
         quote_spanned! {if_let_clause.if_keyword.span()=>
            if let #pat = #expr {
               #body
            }
         }
      },
      CondClause::Let(let_clause) => {
         let pat = &let_clause.pattern;
         let expr = &let_clause.exp;
         quote_spanned! {let_clause.let_keyword.span()=>
            let #pat = #expr;
            #body
         }
      },
      CondClause::If(if_clause) => {
         let cond = &if_clause.cond;
         quote_spanned! {if_clause.if_keyword.span()=>
            if #cond {
               #body
            }
         }
      },
   }
}

fn compile_mir_rule(rule: &MirRule, scc: &MirScc, mir: &AscentMir) -> proc_macro2::TokenStream {
   let head_update_code = head_update_code(rule, scc, mir);

   const MAX_PAR_ITERS: usize = 2;

   // do parallel iteration up to this clause index (exclusive)
   let par_iter_to_ind = if mir.is_parallel {
      use itertools::FoldWhile::*;
      rule
         .body_items
         .iter()
         .fold_while((0, 0), |(count, i), bi| {
            let new_count = count + matches!(bi, MirBodyItem::Clause(..)) as usize;
            if new_count > MAX_PAR_ITERS { Done((new_count, i)) } else { Continue((new_count, i + 1)) }
         })
         .into_inner()
         .1
   } else {
      0
   };
   let rule_body_clauses = rule.body_items.iter().filter_map(|bi| bi.clause()).collect_vec();
   let check_any_empty_rel_can_help =
      rule_body_clauses.len() > 1 && !(rule.simple_join_start_index.is_some() && rule_body_clauses.len() == 2);
   let any_empty_rel_code = check_any_empty_rel_can_help
      .then(|| {
         rule_body_clauses
            .iter()
            .map(|bclause| {
               let rel_expr = expr_for_rel(&bclause.rel, mir);
               quote_spanned! { bclause.rel_args_span=> #rel_expr.is_empty() }
            })
            .reduce(|l, r| quote! { #l || #r})
      })
      .flatten();

   let rule_compiled = compile_mir_rule_inner(rule, scc, mir, par_iter_to_ind, head_update_code, 0);
   if let Some(any_empty_rel_code) = any_empty_rel_code {
      quote! {
         let any_rel_empty = #any_empty_rel_code;
         if !any_rel_empty {
            #rule_compiled
         }
      }
   } else {
      rule_compiled
   }
}

fn compile_mir_rule_inner(
   rule: &MirRule, _scc: &MirScc, mir: &AscentMir, par_iter_to_ind: usize, head_update_code: proc_macro2::TokenStream,
   clause_ind: usize,
) -> proc_macro2::TokenStream {
   if Some(clause_ind) == rule.simple_join_start_index && rule.reorderable {
      let mut rule_cp1 = rule.clone();
      let mut rule_cp2 = rule.clone();
      rule_cp1.reorderable = false;
      rule_cp2.reorderable = false;
      rule_cp2.body_items.swap(clause_ind, clause_ind + 1);
      let rule_cp1_compiled =
         compile_mir_rule_inner(&rule_cp1, _scc, mir, par_iter_to_ind, head_update_code.clone(), clause_ind);
      let rule_cp2_compiled =
         compile_mir_rule_inner(&rule_cp2, _scc, mir, par_iter_to_ind, head_update_code, clause_ind);

      let [MirBodyItem::Clause(bcl1), MirBodyItem::Clause(bcl2)] = &rule.body_items[clause_ind..clause_ind + 2] else {
         panic!("unexpected body items in reorderable rule")
      };
      let rel1_var_name = expr_for_rel(&bcl1.rel, mir);
      let rel2_var_name = expr_for_rel(&bcl2.rel, mir);

      return quote_spanned! {bcl1.rel_args_span=>
         if #rel1_var_name.len_estimate() <= #rel2_var_name.len_estimate() {
            #rule_cp1_compiled
         } else {
            #rule_cp2_compiled
         }
      };
   }
   if clause_ind < rule.body_items.len() {
      let bitem = &rule.body_items[clause_ind];
      let doing_simple_join = rule.simple_join_start_index == Some(clause_ind);
      let next_loop = if doing_simple_join {
         compile_mir_rule_inner(rule, _scc, mir, par_iter_to_ind, head_update_code, clause_ind + 2)
      } else {
         compile_mir_rule_inner(rule, _scc, mir, par_iter_to_ind, head_update_code, clause_ind + 1)
      };

      match bitem {
         MirBodyItem::Clause(bclause) => {
            let (clause_ind, bclause) = if doing_simple_join {
               (clause_ind + 1, rule.body_items[clause_ind + 1].unwrap_clause())
            } else {
               (clause_ind, bclause)
            };

            let bclause_rel_name = &bclause.rel.relation.name;
            let selected_args = &bclause.selected_args();
            let pre_clause_vars =
               rule.body_items.iter().take(clause_ind).flat_map(MirBodyItem::bound_vars).collect::<Vec<_>>();

            let clause_vars = bclause.vars();
            let common_vars = clause_vars.iter().filter(|(_i, v)| pre_clause_vars.contains(v)).collect::<Vec<_>>();
            let common_vars_no_indices = common_vars.iter().map(|(_i, v)| v.clone()).collect::<Vec<_>>();

            let cloning_needed = true;

            let matched_val_ident = Ident::new("__val", bclause.rel_args_span);
            let new_vars_assignments = clause_var_assignments(
               &bclause.rel,
               clause_vars.iter().filter(|(_i, var)| !common_vars_no_indices.contains(var)).cloned(),
               &matched_val_ident,
               &parse_quote! {_self.#bclause_rel_name},
               cloning_needed,
               mir,
            );

            let selected_args_cloned = selected_args.iter().map(exp_cloned).collect_vec();
            let selected_args_tuple = tuple_spanned(&selected_args_cloned, bclause.args_span);
            let rel_version_exp = expr_for_rel(&bclause.rel, mir);

            let mut conds_then_next_loop = next_loop;
            for cond in bclause.cond_clauses.iter().rev() {
               conds_then_next_loop = compile_cond_clause(cond, conds_then_next_loop);
            }

            let span = bclause.rel_args_span;

            let matching_dot_iter = quote_spanned! {bclause.rel_args_span=> __matching};

            let (index_get, iter_all) = if clause_ind < par_iter_to_ind {
               (quote_spanned! {span=> c_index_get}, quote_spanned! {span=> c_iter_all})
            } else {
               (quote_spanned! {span=> index_get}, quote_spanned! {span=> iter_all})
            };

            // The special case where the first clause has indices, but there are no expressions
            // in the args of the first clause
            if doing_simple_join {
               let cl1 = rule.body_items[rule.simple_join_start_index.unwrap()].unwrap_clause();
               let cl2 = bclause;
               let cl1_var_name = expr_for_rel(&cl1.rel, mir);
               let cl2_var_name = expr_for_rel(&cl2.rel, mir);
               let cl1_vars = cl1.vars();

               let cl1_rel_name = &cl1.rel.relation.name;

               let mut cl1_join_vars_assignments = vec![];
               for (tuple_ind, &i) in cl1.rel.indices.iter().enumerate() {
                  let var = expr_to_ident(&cl1.args[i]).unwrap();
                  let tuple_ind = syn::Index { index: tuple_ind as u32, span: var.span() };
                  cl1_join_vars_assignments
                     .push(quote_spanned! {var.span()=> let #var = __cl1_joined_columns.#tuple_ind;});
               }

               let cl1_matched_val_ident = syn::Ident::new("cl1_val", cl1.rel_args_span);
               let cl1_vars_assignments = clause_var_assignments(
                  &cl1.rel,
                  cl1_vars.iter().filter(|(i, _var)| !cl1.rel.indices.contains(i)).cloned(),
                  &cl1_matched_val_ident,
                  &parse_quote! {_self.#cl1_rel_name},
                  cloning_needed,
                  mir,
               );
               let cl1_vars_assignments = vec![cl1_vars_assignments];

               let joined_args_for_cl2_cloned = cl2.selected_args().iter().map(exp_cloned).collect_vec();
               let joined_args_tuple_for_cl2 = tuple_spanned(&joined_args_for_cl2_cloned, cl2.args_span);

               let cl1_tuple_indices_iter = quote_spanned!(cl1.rel_args_span=> __cl1_tuple_indices);

               let cl1_row_capture = provenance_row_capture(cl1, &cl1_matched_val_ident, mir);
               let cl2_row_capture = provenance_row_capture(cl2, &matched_val_ident, mir);
               let mut cl1_conds_then_rest = quote_spanned! {bclause.rel_args_span=>
                  #matching_dot_iter.clone().for_each(|__val|  {
                     #cl2_row_capture
                     // TODO we may be doing excessive cloning
                     #new_vars_assignments
                     #conds_then_next_loop
                  });
               };
               for cond in cl1.cond_clauses.iter().rev() {
                  cl1_conds_then_rest = compile_cond_clause(cond, cl1_conds_then_rest);
               }
               quote_spanned! {cl1.rel_args_span=>
                  #cl1_var_name.#iter_all().for_each(|(__cl1_joined_columns, __cl1_tuple_indices)| {
                     let __cl1_joined_columns = __cl1_joined_columns.tuple_of_borrowed();
                     #(#cl1_join_vars_assignments)*
                     if let Some(__matching) = #cl2_var_name.#index_get(&#joined_args_tuple_for_cl2) {
                        #cl1_tuple_indices_iter.for_each(|cl1_val| {
                           #cl1_row_capture
                           #(#cl1_vars_assignments)*
                           #cl1_conds_then_rest
                        });
                     }
                  });
               }
            } else {
               let row_capture = provenance_row_capture(bclause, &matched_val_ident, mir);
               let (key_binding, selected_args_tuple) = provenance_key_binding(
                  &bclause.rel.indices, &bclause.args, selected_args_tuple, bclause.body_ind, bclause.rel_args_span,
                  mir,
               );
               quote_spanned! {bclause.rel_args_span=>
                  #key_binding
                  if let Some(__matching) = #rel_version_exp.#index_get( &#selected_args_tuple) {
                     #matching_dot_iter.for_each(|__val|  {
                        #row_capture
                        // TODO we may be doing excessive cloning
                        #new_vars_assignments
                        #conds_then_next_loop
                     });
                  }
               }
            }
         },
         MirBodyItem::Generator(gen) => {
            let pat = &gen.pattern;
            let expr = &gen.expr;
            quote_spanned! {gen.for_keyword.span()=>
               for #pat in #expr {
                  #next_loop
               }
            }
         },
         MirBodyItem::Cond(cond) => compile_cond_clause(cond, next_loop),
         MirBodyItem::Agg(agg) => {
            let pat = &agg.pat;
            let rel_name = &agg.rel.relation.name;
            let mir_relation = MirRelation::from(agg.rel.clone(), Total);
            // let rel_version_var_name = mir_relation.var_name();
            let rel_expr = expr_for_rel(&mir_relation, mir);
            let selected_args = mir_relation.indices.iter().map(|&i| &agg.rel_args[i]);
            let selected_args_cloned = selected_args.map(exp_cloned).collect_vec();
            let selected_args_tuple = tuple_spanned(&selected_args_cloned, agg.span);
            let agg_args_tuple_indices = agg.bound_args.iter().map(|arg| {
               (
                  agg.rel_args.iter().find_position(|rel_arg| expr_to_ident(rel_arg) == Some(arg.clone())).unwrap().0,
                  arg.clone(),
               )
            });

            let agg_args_tuple =
               tuple_spanned(&agg.bound_args.iter().map(|v| parse_quote! {#v}).collect_vec(), agg.span);

            let vars_assignments = clause_var_assignments(
               &MirRelation::from(agg.rel.clone(), MirRelationVersion::Total),
               agg_args_tuple_indices,
               &parse_quote_spanned! {agg.span=> __val},
               &parse_quote! {_self.#rel_name},
               false,
               mir,
            );

            let agg_func = &agg.aggregator;
            let _self = quote! { _self };
            let (key_binding, selected_args_tuple) =
               provenance_key_binding(&agg.rel.indices, &agg.rel_args, selected_args_tuple, clause_ind, agg.span, mir);
            let aggregated_rows = provenance_aggregated_rows(agg, clause_ind, &selected_args_tuple, mir);
            quote_spanned! {agg.span=>
               #key_binding
               let __aggregated_rel = #rel_expr;
               #aggregated_rows
               let __matching = __aggregated_rel.index_get( &#selected_args_tuple);
               let __agg_args = __matching.into_iter().flatten().map(|__val| {
                  #vars_assignments
                  #agg_args_tuple
               });
               for #pat in #agg_func(__agg_args) {
                  #next_loop
               }

            }
         },
      }
   } else {
      quote! {
         // let before_update = ::ascent::internal::Instant::now();
         #head_update_code
         // let update_took = before_update.elapsed();
         // _self.update_time_nanos.fetch_add(update_took.as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
      }
   }
}

fn head_update_code(rule: &MirRule, scc: &MirScc, mir: &AscentMir) -> proc_macro2::TokenStream {
   let mut add_rows = vec![];

   let set_changed_true_code = if !mir.is_parallel {
      quote! { __changed = true; }
   } else {
      quote! { __changed.store(true, std::sync::atomic::Ordering::Relaxed);}
   };

   for hcl in rule.head_clause.iter() {
      let head_rel_name = Ident::new(&hcl.rel.name.to_string(), hcl.span);
      let hcl_args_converted = hcl.args.iter().cloned().map(convert_head_arg).collect_vec();
      let new_row_tuple = tuple_spanned(&hcl_args_converted, hcl.args_span);

      let head_relation = &hcl.rel;
      let row_type = tuple_type(&head_relation.field_types);

      let mut update_indices = vec![];
      let rel_indices = scc.dynamic_relations.get(head_relation);
      let (rel_index_write_trait, index_insert_fn) = if !mir.is_parallel {
         (quote! { ::ascent::internal::RelIndexWrite }, quote! {index_insert})
      } else {
         (quote! { ::ascent::internal::CRelIndexWrite }, quote! {index_insert})
      };
      let (rel_index_write_trait, index_insert_fn) =
         (rel_index_write_trait.with_span(hcl.span), index_insert_fn.with_span(hcl.span));
      let new_ref = if !mir.is_parallel {
         quote! {&mut}
      } else {
         quote! {&}
      };
      let mut used_fields = HashSet::new();
      if let Some(rel_indices) = rel_indices {
         for rel_ind in rel_indices.iter().sorted_by_cached_key(|rel| rel.ir_name()) {
            if rel_ind.is_full_index() {
               continue
            };
            let var_name = if !mir.is_parallel {
               expr_for_rel_write(&MirRelation::from(rel_ind.clone(), New), mir)
            } else {
               expr_for_c_rel_write(&MirRelation::from(rel_ind.clone(), New), mir)
            };
            let args_tuple: Vec<Expr> = rel_ind
               .indices
               .iter()
               .map(|&i| {
                  let i_ind = syn::Index::from(i);
                  syn::parse2(quote_spanned! {hcl.span=> __new_row.#i_ind.clone()}).unwrap()
               })
               .collect();
            used_fields.extend(rel_ind.indices.iter().cloned());
            if let IndexValType::Direct(direct) = &rel_ind.val_type {
               used_fields.extend(direct.iter().cloned());
            }
            let args_tuple = tuple(&args_tuple);
            let entry_val = index_get_entry_val_for_insert(
               rel_ind,
               &parse_quote_spanned! {hcl.span=> __new_row},
               &parse_quote_spanned! {hcl.span=> __new_row_ind},
            );
            update_indices.push(quote_spanned! {hcl.span=>
               #rel_index_write_trait::#index_insert_fn(#new_ref #var_name, #args_tuple, #entry_val);
            });
         }
      }

      let head_rel_full_index = &mir.relations_full_indices[head_relation];

      let expr_for_rel_maybe_mut = if mir.is_parallel { expr_for_c_rel_write } else { expr_for_rel_write };
      let head_rel_full_index_expr_new =
         expr_for_rel_maybe_mut(&MirRelation::from(head_rel_full_index.clone(), New), mir);
      let head_rel_full_index_expr_delta = expr_for_rel(&MirRelation::from(head_rel_full_index.clone(), Delta), mir);
      let head_rel_full_index_expr_total = expr_for_rel(&MirRelation::from(head_rel_full_index.clone(), Total), mir);

      let rel_full_index_write_trait = if !mir.is_parallel {
         quote! { ::ascent::internal::RelFullIndexWrite }
      } else {
         quote! { ::ascent::internal::CRelFullIndexWrite }
      }
      .with_span(hcl.span);

      let new_row_to_be_pushed = (0..hcl.rel.field_types.len())
         .map(|i| {
            let ind = syn::Index::from(i);
            let clone = if used_fields.contains(&i) {
               quote! {.clone()}
            } else {
               quote! {}
            };
            parse_quote_spanned! {hcl.span=> __new_row.#ind #clone }
         })
         .collect_vec();
      let new_row_to_be_pushed = tuple_spanned(&new_row_to_be_pushed, hcl.span);

      let push_code = if !mir.is_parallel {
         quote! {
            let __new_row_ind = _self.#head_rel_name.len();
            _self.#head_rel_name.push(#new_row_to_be_pushed);
         }
      } else {
         quote! {
            let __new_row_ind = _self.#head_rel_name.push(#new_row_to_be_pushed);
         }
      };

      let push_code = if mir.config.generate_provenance && !head_relation.is_lattice {
         provenance_push_code(hcl)
      } else {
         push_code
      };
      let HeadProvenanceCode {
         record_derivation,
         save_lattice_row,
         track_lattice_row,
         track_new_lattice_row,
         track_new_row,
      } = head_provenance_code(rule, hcl, mir);

      if !hcl.rel.is_lattice {
         let add_row = quote_spanned! {hcl.span=>
            let __new_row: #row_type = #new_row_tuple;

            if !::ascent::internal::RelFullIndexRead::contains_key(&#head_rel_full_index_expr_total, &__new_row) &&
               !::ascent::internal::RelFullIndexRead::contains_key(&#head_rel_full_index_expr_delta, &__new_row) {
               if #rel_full_index_write_trait::insert_if_not_present(#new_ref #head_rel_full_index_expr_new,
                  &__new_row, ())
               {
                  #push_code
                  #record_derivation
                  #(#update_indices)*
                  #track_new_row
                  #set_changed_true_code
               }
            }
         };
         add_rows.push(add_row);
      } else {
         // rel.is_lattice:
         let lattice_insertion_mutex = lattice_insertion_mutex_var_name(head_relation);
         let head_lat_full_index = &mir.lattices_full_indices[head_relation];
         let head_lat_full_index_var_name_new = ir_relation_version_var_name(&head_lat_full_index.ir_name(), New);
         let head_lat_full_index_var_name_delta = ir_relation_version_var_name(&head_lat_full_index.ir_name(), Delta);
         let head_lat_full_index_var_name_full = ir_relation_version_var_name(&head_lat_full_index.ir_name(), Total);
         let tuple_lat_index = syn::Index::from(hcl.rel.field_types.len() - 1);
         let lattice_key_args: Vec<Expr> = (0..hcl.args.len() - 1)
            .map(|i| {
               let i_ind = syn::Index::from(i);
               syn::parse2(quote_spanned! {hcl.span=> __new_row.#i_ind}).unwrap()
            })
            .map(|e| exp_cloned(&e))
            .collect_vec();
         let lattice_key_tuple = tuple(&lattice_key_args);

         let _self = quote! { _self };
         let add_row = if !mir.is_parallel {
            quote_spanned! {hcl.span=>
               let __new_row: #row_type = #new_row_tuple;
               let __lattice_key = #lattice_key_tuple;
               if let Some(mut __existing_ind) = #head_lat_full_index_var_name_new.index_get(&__lattice_key)
                  .or_else(|| #head_lat_full_index_var_name_delta.index_get(&__lattice_key))
                  .or_else(|| #head_lat_full_index_var_name_full.index_get(&__lattice_key))
               {
                  let __existing_ind = *__existing_ind.next().unwrap();
                  #save_lattice_row
                  // TODO possible excessive cloning here?
                  let __lat_changed = ::ascent::Lattice::join_mut(&mut #_self.#head_rel_name[__existing_ind].#tuple_lat_index, __new_row.#tuple_lat_index.clone());
                  if __lat_changed {
                     let __new_row_ind = __existing_ind;
                     #track_lattice_row
                     #record_derivation
                     #(#update_indices)*
                     #set_changed_true_code
                  }
               } else {
                  let __new_row_ind = #_self.#head_rel_name.len();
                  #record_derivation
                  #(#update_indices)*
                  #_self.#head_rel_name.push(#new_row_to_be_pushed);
                  #track_new_lattice_row
                  #set_changed_true_code
               }
            }
         } else {
            quote_spanned! {hcl.span=> // mir.is_parallel:
               let __new_row: #row_type = #new_row_tuple;
               let __lattice_key = #lattice_key_tuple;
               let __existing_ind_in_new = #head_lat_full_index_var_name_new.get_cloned(&__lattice_key);
               let __new_has_ind = __existing_ind_in_new.is_some();
               if let Some(__existing_ind) = __existing_ind_in_new
                  .or_else(|| #head_lat_full_index_var_name_delta.get_cloned(&__lattice_key))
                  .or_else(|| #head_lat_full_index_var_name_full.get_cloned(&__lattice_key))
               {
                  let __lat_changed = ::ascent::Lattice::join_mut(&mut #_self.#head_rel_name[__existing_ind].write().unwrap().#tuple_lat_index,
                                                                  __new_row.#tuple_lat_index.clone());
                  if __lat_changed && !__new_has_ind {
                     let __new_row_ind = __existing_ind;
                     #(#update_indices)*
                     #set_changed_true_code
                  }
               } else {
                  let __hash = #head_lat_full_index_var_name_new.hash_usize(&__lattice_key);
                  let __lock = #_self.#lattice_insertion_mutex.get(__hash % #_self.#lattice_insertion_mutex.len()).expect("lattice_insertion_mutex index out of bounds").lock().unwrap();
                  if let Some(__existing_ind) = #head_lat_full_index_var_name_new.get_cloned(&__lattice_key) {
                     ::ascent::Lattice::join_mut(&mut #_self.#head_rel_name[__existing_ind].write().unwrap().#tuple_lat_index,
                                                 __new_row.#tuple_lat_index.clone());
                  } else {
                     let __new_row_ind = #_self.#head_rel_name.push(::std::sync::RwLock::new(#new_row_to_be_pushed));
                     #(#update_indices)*
                     #set_changed_true_code
                  }
               }
            }
         };
         add_rows.push(add_row);
      }
   }
   quote! {#(#add_rows)*}
}

/// The provenance code woven into the insertion code of a head clause by [`head_update_code`].
/// Each stream refers to the locals of the insertion code around it, and is empty without
/// `#![generate_provenance]` or where it does not apply.
#[derive(Default)]
struct HeadProvenanceCode {
   /// Records the derivation of the fact at `__new_row_ind` from the facts the rule matched
   record_derivation: TokenStream,
   /// Saves the lattice fact at `__existing_ind` as `__old_row` before its value is joined
   save_lattice_row: TokenStream,
   /// Remaps the lattice fact at `__new_row_ind`, whose value the join changed, from `__old_row`
   track_lattice_row: TokenStream,
   /// Maps the lattice fact just pushed at `__new_row_ind` to its row
   track_new_lattice_row: TokenStream,
   /// Maps the relation fact `__new_row`, just pushed at `__new_row_ind`, to its row
   track_new_row: TokenStream,
}

/// The provenance code of the insertion of the facts of `hcl`, the head clause of `rule`.
fn head_provenance_code(rule: &MirRule, hcl: &IrHeadClause, mir: &AscentMir) -> HeadProvenanceCode {
   if !mir.config.generate_provenance {
      return HeadProvenanceCode::default();
   }
   let head_relation = &hcl.rel;
   let head_rel_name = Ident::new(&hcl.rel.name.to_string(), hcl.span);
   let rows = provenance_rows_var_name(head_relation);
   let self_tok = quote! { _self };
   // The provenance code refers to the locals of the insertion code around it, so it is spanned
   // like their definitions: at the call site for relations, at the head clause for lattices
   let local_span = if head_relation.is_lattice { hcl.span } else { Span::call_site() };

   let rel_id = mir.provenance_relations.id(head_relation);
   let origin = rule.origin;
   let premises_var = Ident::new("__premises", local_span);
   let label = syn::Lifetime::new("'__provenance_premises", local_span);
   let premises = provenance_premises(rule, mir, &premises_var, &label);
   // A premise has no row when the rule matched a fact the user removed, which the
   // indices of the previous run still hold
   let (record, otherwise) = if head_relation.is_lattice {
      (
         quote! { record_latest },
         quote_spanned! {local_span=> #self_tok.__provenance.forget(#rel_id, __new_row_ind); },
      )
   } else {
      (quote! { record }, quote! {})
   };
   // A block rather than a closure, so that the premises can be looked up and registered
   // in the row maps while the matched facts are borrowed from `_self`
   let record_derivation = quote_spanned! {local_span=>
      #[allow(unused_labels)]
      let #premises_var = #label: {
         let mut #premises_var = ::std::vec::Vec::new();
         #(#premises)*
         ::std::option::Option::Some(#premises_var)
      };
      match #premises_var {
         ::std::option::Option::Some(#premises_var) =>
            #self_tok.__provenance.#record(#rel_id, __new_row_ind, #origin, #premises_var),
         ::std::option::Option::None => { #otherwise }
      }
   };

   if !head_relation.is_lattice {
      // The whole of `__new_row` is kept for the row map, which it is moved into once the indices
      // are updated
      let new_row = Ident::new("__new_row", hcl.span);
      let track_new_row = quote_spanned! {local_span=> #self_tok.#rows.insert(#new_row, __new_row_ind); };
      return HeadProvenanceCode { record_derivation, track_new_row, ..Default::default() };
   }

   // Keeps the row map of a lattice up to date as the values of its facts change, leaving the old
   // value mapped if its entry names another row.
   let save_lattice_row =
      quote_spanned! {local_span=> let __old_row = #self_tok.#head_rel_name[__existing_ind].clone(); };
   let track_lattice_row = quote_spanned! {local_span=>
      if #self_tok.#rows.get(&__old_row) == ::std::option::Option::Some(&__new_row_ind) {
         #self_tok.#rows.remove(&__old_row);
      }
      #self_tok.#rows.insert(#self_tok.#head_rel_name[__new_row_ind].clone(), __new_row_ind);
   };
   let track_new_lattice_row = quote_spanned! {local_span=>
      #self_tok.#rows.insert(#self_tok.#head_rel_name[__new_row_ind].clone(), __new_row_ind);
   };
   HeadProvenanceCode {
      record_derivation,
      save_lattice_row,
      track_lattice_row,
      track_new_lattice_row,
      track_new_row: quote! {},
   }
}

/// The push of `__new_row` to the relation of `hcl` in a program with provenance, binding its row
/// to `__new_row_ind`. A row-less relation, whose `push` leaves the field as it was, gets its
/// facts numbered by the provenance's own list of them instead; a field that stores rows grows by
/// the pushed row, as the generated code reads it back by its index, so the rows of the default
/// providers are always the relation's.
fn provenance_push_code(hcl: &IrHeadClause) -> TokenStream {
   let head_rel_name = Ident::new(&hcl.rel.name.to_string(), hcl.span);
   let facts = provenance_facts_var_name(&hcl.rel);
   let new_row = Ident::new("__new_row", hcl.span);
   quote! {
      let __new_row_ind = _self.#head_rel_name.len();
      _self.#head_rel_name.push(#new_row.clone());
      let __new_row_ind = if _self.#head_rel_name.len() > __new_row_ind {
         __new_row_ind
      } else {
         let __new_row_ind = _self.#facts.len();
         _self.#facts.push(#new_row.clone());
         __new_row_ind
      };
   }
}

/// The field mapping the facts of a relation or lattice to their rows.
fn provenance_rows_var_name(relation: &RelationIdentity) -> Ident {
   Ident::new(&format!("__{}_provenance_rows", relation.name), relation.name.span())
}

/// The field listing the facts of a relation, by row, when its data structure provider stores no
/// rows. Empty, and the rows those of the relation, otherwise.
fn provenance_facts_var_name(relation: &RelationIdentity) -> Ident {
   Ident::new(&format!("__{}_provenance_facts", relation.name), relation.name.span())
}

/// The method telling whether a relation is row-less, generated by [`compile_row_less_impl`].
fn provenance_row_less_fn_name(relation: &RelationIdentity) -> Ident {
   Ident::new(&format!("__{}_provenance_row_less", relation.name), relation.name.span())
}

/// Whether `relation`, which is not a lattice, is row-less, as told by its generated method.
fn provenance_row_less(relation: &RelationIdentity, self_tok: &TokenStream, span: Span) -> TokenStream {
   let row_less = provenance_row_less_fn_name(relation);
   quote_spanned! {span=> #self_tok.#row_less() }
}

/// The `__<relation>_provenance_row_less` methods of a program with provenance, one per relation
/// that is not a lattice: the single place that tells a row-less relation from one whose data
/// structure stores rows.
fn compile_row_less_impl(mir: &AscentMir) -> TokenStream {
   let (impl_generics, ty_generics, where_clause) = mir.signatures.split_impl_generics_for_impl();
   let struct_name = &mir.signatures.declaration.ident;
   let row_less_fns = mir.provenance_relations.relations().iter().filter(|rel| !rel.is_lattice).map(|rel| {
      let row_less = provenance_row_less_fn_name(rel);
      let facts = provenance_facts_var_name(rel);
      let doc = format!(
         "Whether `{name}` is row-less: backed by a data structure provider whose field stores no \
          rows, so that its facts are numbered by `{facts}`, the provenance's own list of them. \
          The list, not a flag, is the source of truth: a fact is appended to it exactly when a \
          `push` left the field as it was, so it is non-empty if and only if the relation is \
          row-less and holds facts, and a row-less relation without facts has no rows to number.",
         name = rel.name
      );
      quote! {
         #[doc = #doc]
         fn #row_less(&self) -> bool { !self.#facts.is_empty() }
      }
   });
   quote! {
      impl #impl_generics #struct_name #ty_generics #where_clause {
         #(#row_less_fns)*
      }
   }
}

/// The fact at `row` of `relation`, if the relation has such a row.
fn provenance_stored_row(relation: &RelationIdentity, self_tok: &TokenStream, row: &Ident, span: Span) -> TokenStream {
   let name = &relation.name;
   quote_spanned! {span=> (#row < #self_tok.#name.len()).then(|| &#self_tok.#name[#row]) }
}

/// The row of `fact`, a fact a clause or aggregation matched in `relation`, evaluating to `missing`
/// if it has none. A fact of a row-less relation is given a row if it has none yet: the data
/// structure can hold facts no rule derived, such as those a transitive relation implies, which
/// are explained as leaves. A fact without a row of a relation that stores rows was removed by
/// the user and only matched from the indices of the previous run.
fn provenance_fact_row(
   relation: &RelationIdentity, fact: TokenStream, missing: TokenStream, span: Span,
) -> TokenStream {
   let rows = provenance_rows_var_name(relation);
   let facts = provenance_facts_var_name(relation);
   let self_tok = quote! { _self };
   let row_less = provenance_row_less(relation, &self_tok, span);
   let register = quote_spanned! {span=>
      {
         let __row = #self_tok.#facts.len();
         #self_tok.#facts.push(__fact.clone());
         #self_tok.#rows.insert(__fact, __row);
         __row
      }
   };
   quote_spanned! {span=>
      {
         let __fact = #fact;
         let __row = #self_tok.#rows.get(&__fact).copied();
         match __row {
            ::std::option::Option::Some(__row) => __row,
            ::std::option::Option::None if #row_less => #register,
            ::std::option::Option::None => #missing,
         }
      }
   }
}

fn provenance_row_var_name(bclause: &MirBodyClause) -> Ident {
   Ident::new(&format!("__provenance_row_{}", bclause.body_ind), bclause.rel_args_span)
}

fn provenance_aggregated_rows_var_name(body_ind: usize, span: Span) -> Ident {
   Ident::new(&format!("__provenance_rows_{body_ind}"), span)
}

/// Collects the `(relation id, row)` pairs of the facts the aggregation at `body_ind` aggregates.
fn provenance_aggregated_rows(agg: &IrAggClause, body_ind: usize, key: &Expr, mir: &AscentMir) -> TokenStream {
   if !mir.config.generate_provenance {
      return quote! {};
   }
   let relation = &agg.rel.relation;
   let rel_id = mir.provenance_relations.id(relation);
   let rows_var = provenance_aggregated_rows_var_name(body_ind, agg.span);
   // Spanned like the aggregation code around it, whose locals it refers to
   let span = agg.span;
   let label = syn::Lifetime::new(&format!("'__provenance_rows_{body_ind}"), span);
   let missing = quote_spanned! {span=> break #label ::std::option::Option::None };
   let row = match &agg.rel.val_type {
      IndexValType::Reference => {
         let selected = agg
            .rel
            .indices
            .iter()
            .map(|&i| (i, provenance_matched_column(&agg.rel.indices, &agg.rel_args, i, body_ind, span)))
            .collect_vec();
         let row = provenance_lattice_row(relation, &selected, quote_spanned! {span=> *__val }, span);
         quote_spanned! {span=>
            match #row {
               ::std::option::Option::Some(__row) => __row,
               ::std::option::Option::None => #missing,
            }
         }
      },
      IndexValType::Direct(val_cols) => {
         let fact = (0..relation.field_types.len())
            .map(|i| match val_cols.iter().position(|&col| col == i) {
               Some(pos) => {
                  let pos = syn::Index::from(pos);
                  parse_quote_spanned! {span=> __val.#pos.clone()}
               },
               None => provenance_matched_column(&agg.rel.indices, &agg.rel_args, i, body_ind, span),
            })
            .collect_vec();
         let fact = tuple_spanned(&fact, agg.span);
         let fact = quote_spanned! {span=>
            {
               let __val = __val.tuple_of_borrowed();
               #fact
            }
         };
         provenance_fact_row(relation, fact, missing, span)
      },
   };
   // A block rather than an iterator, so that the facts can be registered in the row map while
   // the matched facts are borrowed from `_self`
   quote_spanned! {span=>
      let #rows_var: ::std::option::Option<::std::vec::Vec<(usize, usize)>> = #label: {
         let mut #rows_var = ::std::vec::Vec::new();
         for __val in __aggregated_rel.index_get(&#key).into_iter().flatten() {
            #rows_var.push((#rel_id, #row));
         }
         ::std::option::Option::Some(#rows_var)
      };
   }
}

/// The local holding the index key the clause or aggregation at `body_ind` looked its facts up by.
fn provenance_key_var_name(body_ind: usize, span: Span) -> Ident {
   Ident::new(&format!("__provenance_key_{body_ind}"), span)
}

/// Binds the index key `key` of a clause or aggregation to a local when provenance needs the
/// value of one of its non-variable columns, so that the expression is evaluated only once.
/// Returns the binding and the expression to look facts up by.
fn provenance_key_binding(
   indices: &[usize], args: &[Expr], key: Expr, body_ind: usize, span: Span, mir: &AscentMir,
) -> (TokenStream, Expr) {
   if mir.config.generate_provenance && indices.iter().any(|&i| expr_to_ident(&args[i]).is_none()) {
      let key_var = provenance_key_var_name(body_ind, span);
      (quote_spanned! {span=> let #key_var = #key; }, parse_quote! { #key_var })
   } else {
      (quote! {}, key)
   }
}

/// Column `i` of the fact the clause or aggregation at `body_ind` matched: a clone of its
/// variable, or the column of the key bound by `provenance_key_binding`.
fn provenance_matched_column(indices: &[usize], args: &[Expr], i: usize, body_ind: usize, span: Span) -> Expr {
   match indices.iter().position(|&col| col == i) {
      Some(pos) if expr_to_ident(&args[i]).is_none() => {
         let key_var = provenance_key_var_name(body_ind, span);
         let pos = syn::Index::from(pos);
         parse_quote_spanned! {span=> #key_var.#pos.clone() }
      },
      _ => exp_cloned(&args[i]),
   }
}

/// The row of a lattice fact a clause matched, or `None` if that row no longer holds a fact with
/// the `selected` column values the clause looked it up by. Indices are not cleared between runs,
/// so a rerun can match a row whose fact the user replaced. The row is named as the fact's mapped
/// row, as relation facts are. A lattice holds one row per key; a key the user supplied at several
/// rows is not supported, by the engine either.
fn provenance_lattice_row(
   relation: &RelationIdentity, selected: &[(usize, Expr)], row: TokenStream, span: Span,
) -> TokenStream {
   let rows = provenance_rows_var_name(relation);
   let self_tok = quote! { _self };
   let columns_match = selected.iter().map(|(i, column)| {
      let i = syn::Index::from(*i);
      quote_spanned! {span=> __fact.#i == #column }
   });
   let columns_match = if selected.is_empty() {
      quote_spanned! {span=> true }
   } else {
      quote_spanned! {span=> #(#columns_match)&&* }
   };
   let mapped_row = quote_spanned! {span=>
      if #columns_match { #self_tok.#rows.get(__fact).copied() } else { ::std::option::Option::None }
   };
   let row_ident = Ident::new("__row", span);
   let stored_row = provenance_stored_row(relation, &self_tok, &row_ident, span);
   quote_spanned! {span=>
      {
         let #row_ident: usize = #row;
         #stored_row.and_then(|__fact| #mapped_row)
      }
   }
}

/// Saves the row of the fact a lattice clause matched. The rows of other facts are found from
/// the clause arguments once the rule fires, as their indices do not refer to rows.
fn provenance_row_capture(bclause: &MirBodyClause, val_ident: &Ident, mir: &AscentMir) -> TokenStream {
   if mir.config.generate_provenance && bclause.rel.relation.is_lattice {
      let row = provenance_row_var_name(bclause);
      quote! { let #row: usize = *#val_ident; }
   } else {
      quote! {}
   }
}

/// Pushes to `premises` the `(relation id, row)` pairs of the facts the relation clauses and
/// aggregations of `rule` matched, in source order, breaking out of the enclosing block `label`
/// with `None` if one of them has no row. `rule` must not have been reordered.
fn provenance_premises(rule: &MirRule, mir: &AscentMir, premises: &Ident, label: &syn::Lifetime) -> Vec<TokenStream> {
   let missing = quote! { break #label ::std::option::Option::None };
   rule
      .body_items
      .iter()
      .enumerate()
      .filter_map(|(body_ind, bitem)| match bitem {
         MirBodyItem::Clause(bclause) => {
            let relation = &bclause.rel.relation;
            let rel_id = mir.provenance_relations.id(relation);
            let matched_column = |i| {
               provenance_matched_column(
                  &bclause.rel.indices, &bclause.args, i, bclause.body_ind, bclause.rel_args_span,
               )
            };
            let row = if relation.is_lattice {
               let row = provenance_row_var_name(bclause);
               let selected = bclause.rel.indices.iter().map(|&i| (i, matched_column(i))).collect_vec();
               let row = provenance_lattice_row(relation, &selected, quote! { #row }, Span::call_site());
               quote! {
                  match #row {
                     ::std::option::Option::Some(__row) => __row,
                     ::std::option::Option::None => #missing,
                  }
               }
            } else {
               let fact = tuple_spanned(&(0..bclause.args.len()).map(matched_column).collect_vec(), bclause.args_span);
               provenance_fact_row(relation, quote! { #fact }, missing.clone(), Span::call_site())
            };
            Some(quote! { #premises.push((#rel_id, #row)); })
         },
         MirBodyItem::Agg(agg) => {
            let rows_var = provenance_aggregated_rows_var_name(body_ind, agg.span);
            Some(quote! {
               match #rows_var.as_ref() {
                  ::std::option::Option::Some(__rows) => #premises.extend(__rows.iter().copied()),
                  ::std::option::Option::None => #missing,
               }
            })
         },
         MirBodyItem::Generator(_) | MirBodyItem::Cond(_) => None,
      })
      .collect()
}

/// Moves the derivations of facts the user moved since the last run, and forgets those of
/// facts the user removed or that were derived from them. Runs before the rows of the facts are
/// reindexed.
fn provenance_relocate_derivations(mir: &AscentMir) -> TokenStream {
   let relations = mir.provenance_relations.relations();
   let self_tok = quote! { self };
   let mut find_moved = vec![];
   for (rel_id, rel) in relations.iter().enumerate() {
      let name = &rel.name;
      let rows = provenance_rows_var_name(rel);
      let find_moved_in_rel = quote! {
         let mut __new_rows = ::std::collections::HashMap::new();
         for (row, fact) in self.#name.iter().enumerate() {
            __new_rows.entry(fact).or_insert(row);
         }
         for (fact, &row) in self.#rows.iter() {
            let new_row = __new_rows.get(fact).copied();
            if new_row != ::std::option::Option::Some(row) {
               __moved.insert((#rel_id, row), new_row);
            }
         }
      };
      // The user cannot move the facts of a row-less relation
      find_moved.push(if rel.is_lattice {
         find_moved_in_rel
      } else {
         let row_less = provenance_row_less(rel, &self_tok, Span::call_site());
         quote! { if !#row_less { #find_moved_in_rel } }
      });
   }
   // The rows of a row-less relation are numbered by the provenance's list of its facts
   let lens = relations.iter().map(|rel| {
      let name = &rel.name;
      if rel.is_lattice {
         quote! { self.#name.len() }
      } else {
         let facts = provenance_facts_var_name(rel);
         let row_less = provenance_row_less(rel, &self_tok, Span::call_site());
         quote! { if #row_less { self.#facts.len() } else { self.#name.len() } }
      }
   });
   quote! {
      let mut __moved = ::std::collections::HashMap::new();
      #(#find_moved)*
      let __relocation = ::ascent::internal::Relocation { lens: &[#(#lens),*], moved: &__moved };
      self.__provenance.relocate(&__relocation);
   }
}

/// The `explain_<relation>` functions of a program with provenance.
fn compile_explain_impl(mir: &AscentMir) -> TokenStream {
   let (impl_generics, ty_generics, where_clause) = mir.signatures.split_impl_generics_for_impl();
   let struct_name = &mir.signatures.declaration.ident;
   let relations = mir.provenance_relations.relations();

   let mut where_clause = where_clause.cloned().unwrap_or_else(|| parse_quote! { where });
   for field_type in relations.iter().flat_map(|rel| &rel.field_types).unique() {
      where_clause.predicates.push(parse_quote! { #field_type: ::core::fmt::Debug });
   }

   let mut explain_fns = vec![];
   let mut fact_arms = vec![];
   for (rel_id, rel) in relations.iter().enumerate() {
      let name = &rel.name;
      let name_str = name.to_string();
      let is_lattice = rel.is_lattice;
      let rows = provenance_rows_var_name(rel);
      let row_from_map = quote! { self.#rows.get(fact).copied() };
      let self_tok = quote! { self };
      let row_ident = Ident::new("row", Span::call_site());
      let stored_row = provenance_stored_row(rel, &self_tok, &row_ident, Span::call_site());
      // The facts of a row-less relation are listed by the provenance and never moved or removed
      // by the user; the full index answers whether it holds a fact
      let (listed_fact, in_index, or_in_index) = if rel.is_lattice {
         (quote! {}, quote! {}, quote! {})
      } else {
         let facts = provenance_facts_var_name(rel);
         let row_less = provenance_row_less(rel, &self_tok, Span::call_site());
         let full_index = &mir.relations_full_indices[rel].ir_name();
         let ind_common = rel_ind_common_var_name(rel);
         (
            quote! {
               if #row_less {
                  return self.#facts.get(row).map(|fact| (#name_str, ::std::format!("{:?}", fact), false));
               }
            },
            quote! {
               // Row-less, so that the field stores no facts and the full index holds them instead
               let in_index = || #row_less
                  && ::ascent::internal::RelFullIndexRead::contains_key(
                     &::ascent::internal::ToRelIndex0::to_rel_index(&self.#full_index, &self.#ind_common),
                     fact,
                  );
            },
            quote! { || in_index() },
         )
      };
      fact_arms.push(quote! {
         #rel_id => {
            #listed_fact
            let in_place = #stored_row.and_then(|fact| {
               (#row_from_map == ::std::option::Option::Some(row)).then(|| ::std::format!("{:?}", fact))
            });
            let fact = match in_place {
               ::std::option::Option::Some(fact) => fact,
               // The user moved or removed the fact since the last run
               ::std::option::Option::None => {
                  let fact = self.#rows.iter().find(|(_, fact_row)| **fact_row == row)?.0;
                  if !self.#name.iter().any(|row| row == fact) {
                     return ::std::option::Option::None;
                  }
                  ::std::format!("{:?}", fact)
               },
            };
            ::std::option::Option::Some((#name_str, fact, #is_lattice))
         },
      });
      let explain_fn = Ident::new(&format!("explain_{name}"), name.span());
      let row_type = tuple_type(&rel.field_types);
      let doc = format!(
         "Explains how the fact `fact` of `{name}` was derived, or returns `None` if `{name}` does not contain it."
      );
      explain_fns.push(quote! {
         #[doc = #doc]
         pub fn #explain_fn(&self, fact: &#row_type) -> ::std::option::Option<::ascent::provenance::Proof> {
            let row = #row_from_map;
            // In place at its mapped row, where the last run left it
            let at_mapped_row = row.and_then(|row| #stored_row).is_some_and(|row| row == fact);
            // Elsewhere in the field: added, or moved, by the user since the last run
            let in_field = || self.#name.iter().any(|row| row == fact);
            #in_index
            if !(at_mapped_row || in_field() #or_in_index) {
               return ::std::option::Option::None;
            }
            match row {
               // Possibly moved by the user since the last run
               ::std::option::Option::Some(row) => self.__explain(#rel_id, row),
               // A fact added since the last run
               ::std::option::Option::None => ::std::option::Option::Some(::ascent::provenance::Proof {
                  relation: #name_str,
                  fact: ::std::format!("{:?}", fact),
                  rule: ::std::option::Option::None,
                  premises: ::std::vec::Vec::new(),
               }),
            }
         }
      });
   }

   quote! {
      impl #impl_generics #struct_name #ty_generics #where_clause {
         #(#explain_fns)*

         /// The name of `relation`, the fact the last run recorded at `row` of it, and whether it is a
         /// lattice, or `None` if the user has removed that fact since. Rows refer to the relations
         /// as they were after the last run: the user may have moved facts since, in which case the
         /// fact is found by a scan of the relation. The rows of a relation whose data structure
         /// stores no rows refer to the provenance's list of its facts.
         fn __provenance_fact(
            &self, relation: usize, row: usize,
         ) -> ::std::option::Option<(&'static str, ::std::string::String, bool)> {
            match relation {
               #(#fact_arms)*
               _ => unreachable!("unknown relation id"),
            }
         }

         /// The proof of the fact the last run recorded at `row` of `relation`. A lattice fact is only
         /// explained at the root: as a premise, its value may have changed since it was matched. A
         /// derivation one of whose premises the user removed since the last run is not used.
         fn __explain(&self, relation: usize, row: usize) -> ::std::option::Option<::ascent::provenance::Proof> {
            ::ascent::internal::build_proof(relation, row, |relation, row, is_root| {
               let (relation_name, fact, is_lattice) = self.__provenance_fact(relation, row)?;
               let derivation = if is_lattice && !is_root {
                  ::std::option::Option::None
               } else {
                  self.__provenance.derivation(relation, row)
               };
               let derivation = derivation.filter(|derivation| {
                  derivation.premises.iter().all(|&(relation, row)| self.__provenance_fact(relation, row).is_some())
               });
               let node = ::ascent::internal::ProofNode { relation: relation_name, fact, derivation };
               ::std::option::Option::Some(node)
            })
         }
      }
   }
}

fn lattice_insertion_mutex_var_name(head_relation: &RelationIdentity) -> Ident {
   Ident::new(&format!("__{}_mutex", head_relation.name), head_relation.name.span())
}

fn rel_ind_common_var_name(relation: &RelationIdentity) -> Ident {
   Ident::new(&format!("__{}_ind_common", relation.name), relation.name.span())
}

fn convert_head_arg(arg: Expr) -> Expr {
   if let Some(var) = expr_to_ident(&arg) {
      parse2(quote_spanned! {arg.span()=> ascent::internal::Convert::convert(#var)}).unwrap()
   } else {
      arg
   }
}

fn expr_for_rel(rel: &MirRelation, mir: &AscentMir) -> proc_macro2::TokenStream {
   fn expr_for_rel_inner(
      ir_name: &Ident, version: MirRelationVersion, _mir: &AscentMir, mir_rel: &MirRelation,
   ) -> (TokenStream, bool) {
      let var = ir_relation_version_var_name(ir_name, version);
      if mir_rel.relation.is_lattice {
         (quote! { & #var }, true)
      } else {
         let rel_ind_common = ir_relation_version_var_name(&rel_ind_common_var_name(&mir_rel.relation), version);
         (quote! { #var.to_rel_index(& #rel_ind_common) }, false)
      }
   }

   if rel.version == MirRelationVersion::TotalDelta {
      let total_expr = expr_for_rel_inner(&rel.ir_name, MirRelationVersion::Total, mir, rel).0;
      let delta_expr = expr_for_rel_inner(&rel.ir_name, MirRelationVersion::Delta, mir, rel).0;
      quote! {
         ascent::internal::RelIndexCombined::new(& #total_expr, & #delta_expr)
      }
   } else {
      let (res, borrowed) = expr_for_rel_inner(&rel.ir_name, rel.version, mir, rel);
      if !borrowed {
         res
      } else {
         quote! {(#res)}
      }
   }
}

fn expr_for_rel_write(mir_rel: &MirRelation, _mir: &AscentMir) -> proc_macro2::TokenStream {
   let var = mir_rel.var_name();
   if mir_rel.relation.is_lattice {
      quote! { #var }
   } else {
      let rel_ind_common = ir_relation_version_var_name(&rel_ind_common_var_name(&mir_rel.relation), mir_rel.version);
      quote! { #var.to_rel_index_write(&mut #rel_ind_common) }
   }
}

fn expr_for_c_rel_write(mir_rel: &MirRelation, _mir: &AscentMir) -> proc_macro2::TokenStream {
   let var = mir_rel.var_name();
   if mir_rel.relation.is_lattice {
      quote! { #var }
   } else {
      let rel_ind_common = ir_relation_version_var_name(&rel_ind_common_var_name(&mir_rel.relation), mir_rel.version);
      quote! { #var.to_c_rel_index_write(&#rel_ind_common) }
   }
}

fn clause_var_assignments(
   rel: &MirRelation, vars: impl Iterator<Item = (usize, Ident)>, val_ident: &Ident, relation_expr: &Expr,
   cloning_needed: bool, mir: &AscentMir,
) -> proc_macro2::TokenStream {
   let mut assignments = vec![];

   let mut any_vars = false;
   for (ind_in_tuple, var) in vars {
      let var_type_ascription = {
         let ty = &rel.relation.field_types[ind_in_tuple];
         quote! { : & #ty}
      };
      any_vars = true;
      match &rel.val_type {
         IndexValType::Reference => {
            let ind = syn::Index::from(ind_in_tuple);
            assignments.push(quote! {
               let #var #var_type_ascription = &__row.#ind;
            })
         },
         IndexValType::Direct(inds) => {
            let ind = inds.iter().enumerate().find(|(_i, ind)| **ind == ind_in_tuple).unwrap().0;
            let ind = syn::Index::from(ind);

            assignments.push(quote! {
               let #var #var_type_ascription = #val_ident.#ind;
            })
         },
      }
   }

   if any_vars {
      match &rel.val_type {
         IndexValType::Reference => {
            let maybe_lock = if rel.relation.is_lattice && mir.is_parallel {
               quote! {.read().unwrap()}
            } else {
               quote! {}
            };
            let maybe_clone = if cloning_needed {
               quote! {.clone()}
            } else {
               quote! {}
            };
            assignments.insert(0, quote! {
               let __row = &#relation_expr[*#val_ident]#maybe_lock #maybe_clone;
            });
         },
         IndexValType::Direct(_) => {
            assignments.insert(0, quote! {
               let #val_ident = #val_ident.tuple_of_borrowed();
            });
         },
      }
   }

   quote! {
      #(#assignments)*
   }
}

fn index_get_entry_val_for_insert(rel_ind: &IrRelation, tuple_expr: &Expr, ind_expr: &Expr) -> Expr {
   match &rel_ind.val_type {
      IndexValType::Reference => ind_expr.clone(),
      IndexValType::Direct(inds) => {
         let val = inds
            .iter()
            .map(|&ind| {
               let ind = syn::Index::from(ind);
               parse_quote! {
                  #tuple_expr.#ind.clone()
               }
            })
            .collect_vec();
         tuple(&val)
      },
   }
}
