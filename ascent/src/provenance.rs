//! Explanations of the facts computed by Ascent programs.
//!
//! An `ascent!` or `ascent_run!` program with the `#![generate_provenance]` attribute records, for
//! every fact a rule derives, the rule and the facts it was derived from. Its `explain_<relation>`
//! methods turn these records into a [`Proof`] tree.

/// A derivation tree of a fact.
///
/// Like other recursive data, a proof several thousand facts deep can overflow the stack when it
/// is cloned, compared, formatted or dropped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
   /// The name of the relation of the fact.
   pub relation: &'static str,
   /// The fact, formatted with `Debug`.
   pub fact: String,
   /// The position, among the rules of the program in source order, of the rule that derived
   /// the fact, or `None` for a fact the user supplied or whose derivation was forgotten because
   /// the user removed or changed it or one of its premises, for a fact the data structure of its
   /// relation holds without a rule having derived it, such as one a transitive relation
   /// implies, and for a lattice fact that is a premise. A relation fact is explained by its first
   /// derivation, a lattice fact by the derivation that last changed its value.
   pub rule: Option<usize>,
   /// The proofs of the facts matched by the relation clauses of the rule's body and of the
   /// facts its aggregations consumed, in body order. A lattice fact here has no premises.
   pub premises: Vec<Proof>,
}
