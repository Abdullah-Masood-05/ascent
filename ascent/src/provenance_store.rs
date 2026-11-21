//! Records of how the facts of programs with `#![generate_provenance]` were derived.

use std::collections::HashMap;

use crate::provenance::Proof;

/// How a fact was derived: the rule and the facts, as `(relation, row)` pairs, it was derived from.
/// The row of a fact of a relation whose data structure provider stores no rows is the position
/// of the fact in the provenance's own list of the relation's facts.
#[derive(Clone, Debug)]
pub struct Derivation {
   pub rule: usize,
   pub premises: Vec<(usize, usize)>,
}

/// Where the facts of a program are after the user changed its relations between runs: the
/// lengths of the relations, and the new rows, or `None` for removed facts, of the facts that moved.
pub struct Relocation<'a> {
   pub lens: &'a [usize],
   pub moved: &'a HashMap<(usize, usize), Option<usize>>,
}

impl Relocation<'_> {
   /// The new row of the fact at `row` of `relation`, if it still exists.
   fn row(&self, (relation, row): (usize, usize)) -> Option<(usize, usize)> {
      match self.moved.get(&(relation, row)) {
         Some(moved) => moved.map(|row| (relation, row)),
         None => (row < self.lens[relation]).then_some((relation, row)),
      }
   }

   /// The derivation of the fact at `fact`, moved along with its premises, unless one of them
   /// no longer exists.
   fn derivation(&self, fact: (usize, usize), derivation: Derivation) -> Option<((usize, usize), Derivation)> {
      let fact = self.row(fact)?;
      let premises = derivation.premises.into_iter().map(|premise| self.row(premise)).collect::<Option<_>>()?;
      Some((fact, Derivation { rule: derivation.rule, premises }))
   }
}

/// A fact of a proof being built by [`build_proof`].
pub struct ProofNode {
   pub relation: &'static str,
   pub fact: String,
   pub derivation: Option<Derivation>,
}

/// Builds the proof of the fact at `row` of `relation`. `node(relation, row, is_root)` describes
/// the fact at `row` of `relation`, or returns `None` if there is no such row. The tree is built
/// with an explicit stack rather than by recursion.
pub fn build_proof(
   relation: usize, row: usize, node: impl Fn(usize, usize, bool) -> Option<ProofNode>,
) -> Option<Proof> {
   // Facts in depth-first order, each with the positions of its premises in `facts`.
   let mut facts: Vec<(Option<Proof>, Vec<usize>)> = vec![];
   let mut pending: Vec<(usize, usize, Option<usize>)> = vec![(relation, row, None)];
   while let Some((relation, row, parent)) = pending.pop() {
      let Some(ProofNode { relation, fact, derivation }) = node(relation, row, parent.is_none()) else {
         continue;
      };
      let (rule, premises) =
         derivation.map_or((None, vec![]), |derivation| (Some(derivation.rule), derivation.premises));
      let position = facts.len();
      facts.push((Some(Proof { relation, fact, rule, premises: vec![] }), vec![]));
      if let Some(parent) = parent {
         facts[parent].1.push(position);
      }
      pending.extend(premises.into_iter().rev().map(|(relation, row)| (relation, row, Some(position))));
   }
   // Premises come after the facts they derive, so they are complete by the time those are.
   for position in (0..facts.len()).rev() {
      let premises = std::mem::take(&mut facts[position].1);
      let premises = premises.into_iter().map(|premise| facts[premise].0.take().expect("premise already used"));
      let premises = premises.collect();
      facts[position].0.as_mut().expect("fact already used").premises = premises;
   }
   facts.into_iter().next().and_then(|(proof, _)| proof)
}

/// The derivations of the facts of a program, by relation and row.
#[derive(Default, Debug)]
pub struct Provenance {
   derivations: Vec<HashMap<usize, Derivation>>,
}

impl Provenance {
   /// Records the first derivation of the fact at `row` of `relation`.
   pub fn record(&mut self, relation: usize, row: usize, rule: usize, premises: Vec<(usize, usize)>) {
      self.relation_mut(relation).entry(row).or_insert(Derivation { rule, premises });
   }

   /// Records the derivation that last changed the value of the lattice fact at `row` of `relation`.
   pub fn record_latest(&mut self, relation: usize, row: usize, rule: usize, premises: Vec<(usize, usize)>) {
      self.relation_mut(relation).insert(row, Derivation { rule, premises });
   }

   /// Forgets the derivation of the lattice fact at `row` of `relation`, whose value changed in a
   /// way that cannot be explained.
   pub fn forget(&mut self, relation: usize, row: usize) { self.relation_mut(relation).remove(&row); }

   fn relation_mut(&mut self, relation: usize) -> &mut HashMap<usize, Derivation> {
      if self.derivations.len() <= relation {
         self.derivations.resize_with(relation + 1, HashMap::new);
      }
      &mut self.derivations[relation]
   }

   /// The derivation of the fact at `row` of `relation`, if it has one.
   pub fn derivation(&self, relation: usize, row: usize) -> Option<Derivation> {
      self.derivations.get(relation)?.get(&row).cloned()
   }

   /// Moves the derivations along with the facts they derive and use, and forgets those whose
   /// facts no longer exist.
   pub fn relocate(&mut self, relocation: &Relocation) {
      let derivations = std::mem::take(&mut self.derivations);
      for (relation, derivations) in derivations.into_iter().enumerate() {
         for (row, derivation) in derivations {
            if let Some(((relation, row), derivation)) = relocation.derivation((relation, row), derivation) {
               self.relation_mut(relation).insert(row, derivation);
            }
         }
      }
   }
}
