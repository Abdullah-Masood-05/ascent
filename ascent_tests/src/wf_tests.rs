#![cfg(test)]
// Nullary relations in rule bodies make the generated code warn about an unused `tuple` variable.
#![allow(unused_variables)]
//! Tests for the `#![well_founded]` attribute: with it, negation may occur inside recursion and the program
//! computes the well-founded model. Every relation `r` holds its true facts, `r_undefined` holds the facts that
//! are neither true nor false, and `r_truth` classifies a tuple.
use std::collections::BTreeSet;
use std::fmt::Debug;
use std::hash::Hash;

use ascent::{Dual, Truth, ascent, ascent_run};

/// Collects a relation (or any collection of tuples) into a set.
fn set<'a, T: Ord + Clone + 'a>(rel: impl IntoIterator<Item = &'a T>) -> BTreeSet<T> {
   rel.into_iter().cloned().collect()
}

/// Collects an `_undefined` field into a set, asserting that it holds no duplicates.
fn undef<'a, T: Ord + Clone + Debug + 'a>(rel: impl IntoIterator<Item = &'a T>) -> BTreeSet<T> {
   let all: Vec<T> = rel.into_iter().cloned().collect();
   let unique: BTreeSet<T> = all.iter().cloned().collect();
   assert_eq!(all.len(), unique.len(), "an `_undefined` field contains duplicate facts: {all:?}");
   unique
}

fn ones(xs: &[u32]) -> BTreeSet<(u32,)> { xs.iter().map(|&x| (x,)).collect() }

fn pairs(xs: &[(u32, u32)]) -> BTreeSet<(u32, u32)> { xs.iter().copied().collect() }

fn unit(present: bool) -> BTreeSet<()> {
   let mut s = BTreeSet::new();
   if present {
      s.insert(());
   }
   s
}

/// A graph mixing won, lost and drawn positions.
///
/// lost (no moves): 5, 9; won: 4 (->5), 2 (->3), 8 (->9), 11 (->9), 12 (->9);
/// lost: 3 (only ->4), 1 (only ->2); drawn: 6 (self loop), 7 (->6 drawn, ->8 won), 10 (->7).
const MIXED: &[(u32, u32)] =
   &[(1, 2), (2, 1), (2, 3), (3, 4), (4, 5), (6, 6), (7, 6), (7, 8), (8, 9), (10, 7), (11, 9), (12, 6), (12, 9)];
const MIXED_WON: &[u32] = &[2, 4, 8, 11, 12];
const MIXED_LOST: &[u32] = &[1, 3, 5, 9];
const MIXED_DRAWN: &[u32] = &[6, 7, 10];

// reference solver (alternating fixpoint over ground rules)

/// A ground rule `head <-- pos.., !neg..` over atoms numbered `0..n_atoms`.
struct GroundRule {
   head: usize,
   pos: Vec<usize>,
   neg: Vec<usize>,
}

/// Least model of `rules` where `!a` holds iff `a` is not in `assumed`.
fn gamma(rules: &[GroundRule], n_atoms: usize, assumed: &[bool]) -> Vec<bool> {
   let mut model = vec![false; n_atoms];
   loop {
      let mut changed = false;
      for r in rules {
         if !model[r.head] && r.pos.iter().all(|&a| model[a]) && r.neg.iter().all(|&a| !assumed[a]) {
            model[r.head] = true;
            changed = true;
         }
      }
      if !changed {
         return model;
      }
   }
}

/// Well-founded model: returns `(true atoms, undefined atoms)`.
fn well_founded(rules: &[GroundRule], n_atoms: usize) -> (Vec<bool>, Vec<bool>) {
   let mut under = vec![false; n_atoms];
   loop {
      let over = gamma(rules, n_atoms, &under);
      let next_under = gamma(rules, n_atoms, &over);
      if next_under == under {
         let undefined = (0..n_atoms).map(|a| over[a] && !under[a]).collect();
         return (under, undefined);
      }
      under = next_under;
   }
}

/// Deterministic linear congruential generator.
struct Lcg(u64);

impl Lcg {
   fn next(&mut self) -> u32 {
      self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
      (self.0 >> 33) as u32
   }
   fn below(&mut self, n: u32) -> u32 { self.next() % n }
}

/// A pseudo-random directed graph on nodes `0..n` (self loops allowed).
fn random_graph(rng: &mut Lcg, n: u32) -> Vec<(u32, u32)> {
   let mut edges = vec![];
   for x in 0..n {
      for y in 0..n {
         if rng.below(4) == 0 {
            edges.push((x, y));
         }
      }
   }
   edges
}

/// Reference win-move model on nodes `0..n`: `(won, drawn)`; `facts` are extra true `win` facts.
fn reference_win_move(n: u32, edges: &[(u32, u32)], facts: &[u32]) -> (BTreeSet<(u32,)>, BTreeSet<(u32,)>) {
   let mut rules = vec![];
   for &(x, y) in edges {
      rules.push(GroundRule { head: x as usize, pos: vec![], neg: vec![y as usize] });
   }
   for &f in facts {
      rules.push(GroundRule { head: f as usize, pos: vec![], neg: vec![] });
   }
   let (t, u) = well_founded(&rules, n as usize);
   let won = (0..n).filter(|&x| t[x as usize]).map(|x| (x,)).collect();
   let drawn = (0..n).filter(|&x| u[x as usize]).map(|x| (x,)).collect();
   (won, drawn)
}

#[test]
fn win_move_chain_alternates() {
   ascent! {
      #![well_founded]
      struct WinChain;
      relation mv(u32, u32);
      relation win(u32);
      win(x) <-- mv(x, y), !win(y);
   }
   let mut prog = WinChain::default();
   prog.mv = vec![(1, 2), (2, 3), (3, 4)];
   prog.run();
   assert_eq!(set(&prog.win), ones(&[1, 3]));
   assert_eq!(undef(&prog.win_undefined), ones(&[]));
}

#[test]
fn win_move_two_cycle_is_drawn() {
   ascent! {
      #![well_founded]
      struct WinTwoCycle;
      relation mv(u32, u32);
      relation win(u32);
      win(x) <-- mv(x, y), !win(y);
   }
   let mut prog = WinTwoCycle::default();
   prog.mv = vec![(1, 2), (2, 1)];
   prog.run();
   assert_eq!(set(&prog.win), ones(&[]));
   assert_eq!(undef(&prog.win_undefined), ones(&[1, 2]));
}

#[test]
fn win_move_cycle_with_exit_to_lost_position() {
   ascent! {
      #![well_founded]
      struct WinCycleExit;
      relation mv(u32, u32);
      relation win(u32);
      win(x) <-- mv(x, y), !win(y);
   }
   let mut prog = WinCycleExit::default();
   // 3 is lost, so 2 is won, so 1 (whose only move is to 2) is lost.
   prog.mv = vec![(1, 2), (2, 1), (2, 3)];
   prog.run();
   assert_eq!(set(&prog.win), ones(&[2]));
   assert_eq!(undef(&prog.win_undefined), ones(&[]));
}

#[test]
fn win_move_mixed_graph() {
   ascent! {
      #![well_founded]
      struct WinMixed;
      relation mv(u32, u32);
      relation pos(u32);
      relation win(u32);
      relation lost(u32);
      pos(x) <-- mv(x, _);
      pos(y) <-- mv(_, y);
      win(x) <-- mv(x, y), !win(y);
      lost(x) <-- pos(x), !win(x);
   }
   let mut prog = WinMixed::default();
   prog.mv = MIXED.to_vec();
   prog.run();
   assert_eq!(set(&prog.win), ones(MIXED_WON));
   assert_eq!(undef(&prog.win_undefined), ones(MIXED_DRAWN));
   assert_eq!(set(&prog.lost), ones(MIXED_LOST));
   assert_eq!(undef(&prog.lost_undefined), ones(MIXED_DRAWN));
   assert_eq!(set(&prog.pos), ones(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]));
   assert!(prog.pos_undefined.is_empty());
   assert!(prog.mv_undefined.is_empty());
}

#[test]
fn nullary_self_negation_is_undefined() {
   ascent! {
      #![well_founded]
      struct NullSelfNeg;
      relation p();
      p() <-- !p();
   }
   let mut prog = NullSelfNeg::default();
   prog.run();
   assert_eq!(set(&prog.p), unit(false));
   assert_eq!(undef(&prog.p_undefined), unit(true));
}

#[test]
fn nullary_mutual_negation_broken_by_fact() {
   ascent! {
      #![well_founded]
      struct NullMutualBroken;
      relation p();
      relation q();
      relation r();
      relation s();
      p() <-- !q();
      q() <-- !p();
      q() <-- r();
      r();
      s() <-- !p();
   }
   let mut prog = NullMutualBroken::default();
   prog.run();
   assert_eq!(set(&prog.p), unit(false));
   assert_eq!(set(&prog.q), unit(true));
   assert_eq!(set(&prog.r), unit(true));
   assert_eq!(set(&prog.s), unit(true));
   assert!(prog.p_undefined.is_empty());
   assert!(prog.q_undefined.is_empty());
   assert!(prog.r_undefined.is_empty());
   assert!(prog.s_undefined.is_empty());
}

#[test]
fn argumentation_grounded_labelling() {
   ascent! {
      #![well_founded]
      struct Argumentation;
      relation arg(u32);
      relation att(u32, u32);
      relation acc(u32);
      relation def(u32);
      arg(x) <-- for x in 1..=8u32;
      att(1, 2); att(2, 3); att(3, 4);
      att(5, 6); att(6, 5); att(6, 7);
      att(1, 8); att(6, 8);
      acc(x) <-- arg(x), !def(x);
      def(x) <-- att(y, x), acc(y);
   }
   let mut prog = Argumentation::default();
   prog.run();
   assert_eq!(set(&prog.acc), ones(&[1, 3]));
   // 8 is attacked by the accepted 1, so it is defeated even though 6 is undecided.
   assert_eq!(set(&prog.def), ones(&[2, 4, 8]));
   assert_eq!(undef(&prog.acc_undefined), ones(&[5, 6, 7]));
   assert_eq!(undef(&prog.def_undefined), ones(&[5, 6, 7]));
}

#[test]
fn undefined_propagates_through_transitive_closure() {
   ascent! {
      #![well_founded]
      struct PropClosure;
      relation mv(u32, u32);
      relation win(u32);
      relation link(u32, u32);
      relation tc(u32, u32);
      win(x) <-- mv(x, y), !win(y);
      link(x, y) <-- mv(x, y), win(x);
      tc(x, y) <-- link(x, y);
      tc(x, z) <-- link(x, y), tc(y, z);
   }
   let mut prog = PropClosure::default();
   prog.mv = vec![(1, 2), (2, 1), (3, 4), (4, 5)];
   prog.run();
   assert_eq!(set(&prog.win), ones(&[4]));
   assert_eq!(undef(&prog.win_undefined), ones(&[1, 2]));
   assert_eq!(set(&prog.link), pairs(&[(4, 5)]));
   assert_eq!(undef(&prog.link_undefined), pairs(&[(1, 2), (2, 1)]));
   assert_eq!(set(&prog.tc), pairs(&[(4, 5)]));
   assert_eq!(undef(&prog.tc_undefined), pairs(&[(1, 2), (2, 1), (1, 1), (2, 2)]));
}

#[test]
fn later_negation_of_undefined_is_undefined_and_of_false_is_true() {
   ascent! {
      #![well_founded]
      struct PropLaterNeg;
      relation mv(u32, u32);
      relation pos(u32);
      relation win(u32);
      relation lost(u32);
      pos(x) <-- mv(x, _);
      pos(y) <-- mv(_, y);
      win(x) <-- mv(x, y), !win(y);
      lost(x) <-- pos(x), !win(x);
   }
   let mut prog = PropLaterNeg::default();
   prog.mv = vec![(1, 2), (2, 1), (3, 4)];
   prog.run();
   assert_eq!(set(&prog.win), ones(&[3]));
   assert_eq!(undef(&prog.win_undefined), ones(&[1, 2]));
   // win(4) is false, so lost(4) is true; win(1), win(2) are undefined, so lost(1), lost(2) are too.
   assert_eq!(set(&prog.lost), ones(&[4]));
   assert_eq!(undef(&prog.lost_undefined), ones(&[1, 2]));
}

#[test]
fn user_fact_in_cyclic_relation_blocks_negation() {
   ascent! {
      #![well_founded]
      struct UserFactBlocks;
      relation mv(u32, u32);
      relation pos(u32);
      relation win(u32);
      relation lost(u32);
      pos(x) <-- mv(x, _);
      win(x) <-- mv(x, y), !win(y);
      lost(x) <-- pos(x), !win(x);
   }
   let mut prog = UserFactBlocks::default();
   prog.mv = vec![(1, 2), (2, 1)];
   prog.win = vec![(2,)];
   prog.run();
   assert_eq!(set(&prog.win), ones(&[2]));
   assert_eq!(undef(&prog.win_undefined), ones(&[]));
   assert_eq!(set(&prog.lost), ones(&[1]));
   assert_eq!(undef(&prog.lost_undefined), ones(&[]));
}

#[test]
fn stratifiable_program_is_unchanged_by_attribute() {
   ascent! {
      #![well_founded]
      struct StratWf;
      relation node(u32);
      relation edge(u32, u32);
      relation path(u32, u32);
      relation no_path(u32, u32);
      relation reach_count(u32, usize);
      lattice shortest(u32, u32, Dual<u32>);
      node(x), node(y) <-- edge(x, y);
      path(x, y) <-- edge(x, y);
      path(x, z) <-- edge(x, y), path(y, z);
      no_path(x, y) <-- node(x), node(y), !path(x, y);
      reach_count(x, c) <-- node(x), agg c = ascent::aggregators::count() in path(x, _);
      shortest(x, y, Dual(1)) <-- edge(x, y);
      shortest(x, z, Dual(d + 1)) <-- edge(x, y), shortest(y, z, ?Dual(d));
   }
   ascent! {
      struct StratPlain;
      relation node(u32);
      relation edge(u32, u32);
      relation path(u32, u32);
      relation no_path(u32, u32);
      relation reach_count(u32, usize);
      lattice shortest(u32, u32, Dual<u32>);
      node(x), node(y) <-- edge(x, y);
      path(x, y) <-- edge(x, y);
      path(x, z) <-- edge(x, y), path(y, z);
      no_path(x, y) <-- node(x), node(y), !path(x, y);
      reach_count(x, c) <-- node(x), agg c = ascent::aggregators::count() in path(x, _);
      shortest(x, y, Dual(1)) <-- edge(x, y);
      shortest(x, z, Dual(d + 1)) <-- edge(x, y), shortest(y, z, ?Dual(d));
   }
   let edges = vec![(1, 2), (2, 3), (3, 1), (3, 4), (5, 5), (6, 7)];
   let mut wf = StratWf::default();
   wf.edge = edges.clone();
   wf.run();
   let mut plain = StratPlain::default();
   plain.edge = edges;
   plain.run();

   assert_eq!(set(&wf.node), set(&plain.node));
   assert_eq!(set(&wf.edge), set(&plain.edge));
   assert_eq!(set(&wf.path), set(&plain.path));
   assert_eq!(set(&wf.no_path), set(&plain.no_path));
   assert_eq!(set(&wf.reach_count), set(&plain.reach_count));
   assert_eq!(set(&wf.shortest), set(&plain.shortest));

   // a few sanity values
   assert!(set(&wf.path).contains(&(1, 4)));
   assert!(set(&wf.no_path).contains(&(4, 1)));
   assert!(set(&wf.reach_count).contains(&(4, 0)));
   assert!(set(&wf.shortest).contains(&(1, 4, Dual(3))));

   assert!(wf.node_undefined.is_empty());
   assert!(wf.edge_undefined.is_empty());
   assert!(wf.path_undefined.is_empty());
   assert!(wf.no_path_undefined.is_empty());
   assert!(wf.reach_count_undefined.is_empty());
   let shortest_u: &Vec<(u32, u32, Dual<u32>)> = &wf.shortest_undefined;
   assert!(shortest_u.is_empty());
}

#[test]
fn undefined_field_has_relation_tuple_type() {
   ascent! {
      #![well_founded]
      struct FieldTypes;
      relation edge(u32, u32);
      relation pair(u32, u32);
      relation named(String, u32);
      relation p();
      pair(x, y) <-- edge(x, y), !pair(y, x);
      named(s, x) <-- pair(x, _), let s = format!("n{}", x);
      p() <-- !p();
   }
   let mut prog = FieldTypes::default();
   prog.edge = vec![(1, 1), (2, 3)];
   prog.run();

   let pair_u: Vec<(u32, u32)> = prog.pair_undefined.clone();
   let named_u: Vec<(String, u32)> = prog.named_undefined.clone();
   let p_u: Vec<()> = prog.p_undefined.clone();

   assert_eq!(set(&prog.pair), pairs(&[(2, 3)]));
   assert_eq!(undef(&pair_u), pairs(&[(1, 1)]));
   assert_eq!(set(&prog.named), [("n2".to_string(), 2)].into_iter().collect::<BTreeSet<_>>());
   assert_eq!(undef(&named_u), [("n1".to_string(), 1)].into_iter().collect::<BTreeSet<_>>());
   assert_eq!(p_u, vec![()]);
}

#[test]
fn disjunction_in_recursive_negation_rule() {
   ascent! {
      #![well_founded]
      struct Disjunction;
      relation mv(u32, u32);
      relation jump(u32, u32);
      relation win(u32);
      win(x) <-- (mv(x, y) | jump(x, y)), !win(y);
   }
   let mut prog = Disjunction::default();
   prog.mv = vec![(1, 2), (2, 1), (4, 5)];
   prog.jump = vec![(2, 3), (5, 4)];
   prog.run();
   assert_eq!(set(&prog.win), ones(&[2]));
   assert_eq!(undef(&prog.win_undefined), ones(&[4, 5]));
}

#[test]
fn generic_program_with_recursive_negation() {
   ascent! {
      #![well_founded]
      struct WfGeneric<N: Clone + Eq + Hash>;
      relation mv(N, N);
      relation win(N);
      win(x) <-- mv(x, y), !win(y);
   }
   let mut strs: WfGeneric<&'static str> = WfGeneric::default();
   strs.mv = vec![("a", "b"), ("b", "a"), ("c", "d")];
   strs.run();
   let u: Vec<(&'static str,)> = strs.win_undefined.clone();
   assert_eq!(set(&strs.win), [("c",)].into_iter().collect::<BTreeSet<_>>());
   assert_eq!(undef(&u), [("a",), ("b",)].into_iter().collect::<BTreeSet<_>>());

   let mut bytes: WfGeneric<u8> = WfGeneric::default();
   bytes.mv = vec![(1, 2), (2, 3), (4, 4)];
   bytes.run();
   assert_eq!(set(&bytes.win), [(2u8,)].into_iter().collect::<BTreeSet<_>>());
   assert_eq!(undef(&bytes.win_undefined), [(4u8,)].into_iter().collect::<BTreeSet<_>>());
}

#[test]
fn ascent_run_captures_local_variables() {
   fn solve(moves: &[(u32, u32)], banned: u32) -> (BTreeSet<(u32,)>, BTreeSet<(u32,)>) {
      let res = ascent_run! {
         #![well_founded]
         relation mv(u32, u32) = moves.to_vec();
         relation win(u32);
         win(x) <-- mv(x, y), if *y != banned, !win(y);
      };
      (set(&res.win), undef(&res.win_undefined))
   }
   let moves = [(1, 2), (2, 1), (2, 3), (5, 5)];
   // moving to 3 is banned: 1 and 2 only move to each other
   assert_eq!(solve(&moves, 3), (ones(&[]), ones(&[1, 2, 5])));
   // 3 is a lost position, so 2 is won and 1 is lost
   assert_eq!(solve(&moves, 99), (ones(&[2]), ones(&[5])));
}

#[test]
fn run_twice_gives_same_model() {
   ascent! {
      #![well_founded]
      struct RunTwice;
      relation mv(u32, u32);
      relation pos(u32);
      relation win(u32);
      relation lost(u32);
      pos(x) <-- mv(x, _);
      pos(y) <-- mv(_, y);
      win(x) <-- mv(x, y), !win(y);
      lost(x) <-- pos(x), !win(x);
   }
   let mut prog = RunTwice::default();
   prog.mv = MIXED.to_vec();
   prog.run();
   let first = (set(&prog.win), undef(&prog.win_undefined), set(&prog.lost), undef(&prog.lost_undefined));
   prog.run();
   let second = (set(&prog.win), undef(&prog.win_undefined), set(&prog.lost), undef(&prog.lost_undefined));
   assert_eq!(first, second);
   assert_eq!(second.0, ones(MIXED_WON));
   assert_eq!(second.1, ones(MIXED_DRAWN));
   assert_eq!(second.2, ones(MIXED_LOST));
   assert_eq!(second.3, ones(MIXED_DRAWN));
}

#[test]
fn randomized_win_move_matches_reference() {
   ascent! {
      #![well_founded]
      struct RandWin;
      relation pos(u32);
      relation mv(u32, u32);
      relation win(u32);
      relation lost(u32);
      win(x) <-- mv(x, y), !win(y);
      lost(x) <-- pos(x), !win(x);
   }
   let mut rng = Lcg(0x5eed_1234);
   for round in 0..30 {
      let n = 2 + rng.below(9);
      let edges = random_graph(&mut rng, n);
      let (won, drawn) = reference_win_move(n, &edges, &[]);
      let lost: BTreeSet<(u32,)> = (0..n).map(|x| (x,)).filter(|t| !won.contains(t) && !drawn.contains(t)).collect();

      let mut prog = RandWin::default();
      prog.pos = (0..n).map(|x| (x,)).collect();
      prog.mv = edges.clone();
      prog.run();
      assert_eq!(set(&prog.win), won, "round {round}, edges {edges:?}");
      assert_eq!(undef(&prog.win_undefined), drawn, "round {round}, edges {edges:?}");
      assert_eq!(set(&prog.lost), lost, "round {round}, edges {edges:?}");
      assert_eq!(undef(&prog.lost_undefined), drawn, "round {round}, edges {edges:?}");
   }
}

#[test]
fn agg_count_over_groups_with_undefined_members() {
   ascent! {
      #![well_founded]
      struct AggCount;
      relation mv(u32, u32);
      relation win(u32);
      relation group(u32);
      relation member(u32, u32);
      relation member_win(u32, u32);
      relation cnt(u32, usize);
      win(x) <-- mv(x, y), !win(y);
      member_win(g, x) <-- member(g, x), win(x);
      cnt(g, c) <-- group(g), agg c = ascent::aggregators::count() in member_win(g, _);
   }
   let mut prog = AggCount::default();
   prog.mv = AGG_MOVES.to_vec();
   prog.group = vec![(10,), (20,), (30,), (40,), (50,)];
   prog.member = vec![(10, 3), (10, 7), (20, 3), (20, 1), (30, 1), (30, 2), (40, 4), (50, 5), (50, 4)];
   prog.run();
   assert_eq!(set(&prog.member_win), pairs(&[(10, 3), (10, 7), (20, 3)]));
   assert_eq!(undef(&prog.member_win_undefined), pairs(&[(20, 1), (30, 1), (30, 2), (50, 5)]));
   // 10: all members true -> true count; 40: no members at all -> true count 0;
   // 20, 30, 50: undefined members -> counts over true facts and over true+undefined facts, both undefined
   assert_eq!(set(&prog.cnt), [(10, 2), (40, 0)].into_iter().collect::<BTreeSet<(u32, usize)>>());
   assert_eq!(
      undef(&prog.cnt_undefined),
      [(20, 1), (20, 2), (30, 0), (30, 2), (50, 0), (50, 1)].into_iter().collect::<BTreeSet<(u32, usize)>>()
   );
}

#[test]
fn agg_not_behaves_like_negation() {
   ascent! {
      #![well_founded]
      struct AggNot;
      relation mv(u32, u32);
      relation pos(u32);
      relation win(u32);
      relation lost(u32);
      relation lost2(u32);
      pos(x) <-- mv(x, _);
      pos(y) <-- mv(_, y);
      win(x) <-- mv(x, y), !win(y);
      lost(x) <-- pos(x), !win(x);
      lost2(x) <-- pos(x), agg () = ascent::aggregators::not() in win(x);
   }
   let mut prog = AggNot::default();
   prog.mv = MIXED.to_vec();
   prog.run();
   assert_eq!(set(&prog.lost), ones(MIXED_LOST));
   assert_eq!(undef(&prog.lost_undefined), ones(MIXED_DRAWN));
   assert_eq!(set(&prog.lost2), ones(MIXED_LOST));
   assert_eq!(undef(&prog.lost2_undefined), ones(MIXED_DRAWN));
}

#[test]
fn lattice_max_with_undefined_contributions() {
   ascent! {
      #![well_founded]
      struct LatMax;
      relation mv(u32, u32);
      relation win(u32);
      relation bid(u32, u32, u32);
      lattice best(u32, u32);
      relation rich(u32);
      win(x) <-- mv(x, y), !win(y);
      best(g, v) <-- bid(g, x, v), win(x);
      rich(g) <-- best(g, v), if *v >= 25;
   }
   let mut prog = LatMax::default();
   prog.mv = AGG_MOVES.to_vec();
   // (item, position, value); a bid counts if its position is won
   prog.bid = vec![(1, 3, 10), (1, 7, 20), (2, 3, 10), (2, 1, 30), (3, 1, 5), (4, 3, 50), (4, 1, 40), (5, 4, 9)];
   prog.run();
   // item 1: all true; item 2: true 10, possible 30; item 3: only possible 5;
   // item 4: possible 50 equals true 50 (absent from `_undefined`); item 5: nothing.
   assert_eq!(set(&prog.best), pairs(&[(1, 20), (2, 10), (4, 50)]));
   assert_eq!(undef(&prog.best_undefined), pairs(&[(2, 30), (3, 5)]));
   assert_eq!(set(&prog.rich), ones(&[4]));
   assert_eq!(undef(&prog.rich_undefined), ones(&[2]));
}

#[test]
fn lattice_shortest_path_through_undefined_edges() {
   ascent! {
      #![well_founded]
      struct LatDist;
      relation mv(u32, u32);
      relation win(u32);
      relation road(u32, u32, u32, u32);
      relation usable(u32, u32, u32);
      lattice dist(u32, Dual<u32>);
      relation close(u32);
      win(x) <-- mv(x, y), !win(y);
      usable(x, y, w) <-- road(x, y, w, g), win(g);
      dist(0, Dual(0));
      dist(y, Dual(d + w)) <-- dist(x, ?Dual(d)), usable(x, y, w);
      close(x) <-- dist(x, ?Dual(d)), if *d <= 4;
   }
   let mut prog = LatDist::default();
   // won: 3; drawn: 1, 2
   prog.mv = vec![(1, 2), (2, 1), (3, 4)];
   // (from, to, weight, gate): a road is usable if its gate position is won
   prog.road = vec![(0, 1, 5, 3), (1, 2, 5, 3), (0, 2, 3, 1), (2, 3, 1, 3), (0, 4, 1, 2), (4, 5, 1, 3)];
   prog.run();
   // true distances use true roads only: 0 -> 1 -> 2 -> 3
   assert_eq!(
      set(&prog.dist),
      [(0, Dual(0)), (1, Dual(5)), (2, Dual(10)), (3, Dual(11))].into_iter().collect::<BTreeSet<_>>()
   );
   // possible distances: 2 via 0 -> 2 (3), 3 via 2 (4), 4 (1), 5 (2); keys 0 and 1 cannot improve
   assert_eq!(
      undef(&prog.dist_undefined),
      [(2, Dual(3)), (3, Dual(4)), (4, Dual(1)), (5, Dual(2))].into_iter().collect::<BTreeSet<_>>()
   );
   assert_eq!(set(&prog.close), ones(&[0]));
   assert_eq!(undef(&prog.close_undefined), ones(&[2, 3, 4, 5]));
}

#[test]
fn lattice_in_negation_cycle_with_guards() {
   ascent! {
      #![well_founded]
      struct LatGuards;
      relation edge(u32, u32);
      relation guard(u32, u32);
      relation blocked(u32);
      lattice dist(u32, Dual<u32>);
      dist(0, Dual(0));
      dist(y, Dual(d + 1)) <-- dist(x, ?Dual(d)), edge(x, y), !blocked(y);
      // a node is blocked once its guard node is reachable
      blocked(y) <-- guard(y, g), dist(g, _);
   }
   let edges = vec![(0, 1), (0, 2), (1, 3), (0, 4), (4, 5), (5, 3)];

   // 1 and 2 guard each other: whether they are reachable is undefined
   let mut mutual = LatGuards::default();
   mutual.edge = edges.clone();
   mutual.guard = vec![(1, 2), (2, 1)];
   mutual.run();
   assert!(mutual.blocked.is_empty());
   assert_eq!(undef(&mutual.blocked_undefined), ones(&[1, 2]));
   assert_eq!(
      set(&mutual.dist),
      [(0, Dual(0)), (4, Dual(1)), (5, Dual(2)), (3, Dual(3))].into_iter().collect::<BTreeSet<_>>()
   );
   assert_eq!(
      undef(&mutual.dist_undefined),
      [(1, Dual(1)), (2, Dual(1)), (3, Dual(2))].into_iter().collect::<BTreeSet<_>>()
   );

   // only 1 is guarded (by 2, which is reachable): 1 is blocked, everything is determined
   let mut one_way = LatGuards::default();
   one_way.edge = edges;
   one_way.guard = vec![(1, 2)];
   one_way.run();
   assert_eq!(set(&one_way.blocked), ones(&[1]));
   assert!(one_way.blocked_undefined.is_empty());
   assert_eq!(
      set(&one_way.dist),
      [(0, Dual(0)), (2, Dual(1)), (4, Dual(1)), (5, Dual(2)), (3, Dual(3))].into_iter().collect::<BTreeSet<_>>()
   );
   assert!(one_way.dist_undefined.is_empty());
}

#[test]
fn truth_of_win_move_positions() {
   ascent! {
      #![well_founded]
      struct TruthWin;
      relation mv(u32, u32);
      relation win(u32);
      win(x) <-- mv(x, y), !win(y);
   }
   let mut prog = TruthWin::default();
   prog.mv = MIXED.to_vec();
   prog.run();
   for &x in MIXED_WON {
      assert_eq!(prog.win_truth(&(x,)), Truth::True, "position {x}");
   }
   for &x in MIXED_LOST {
      assert_eq!(prog.win_truth(&(x,)), Truth::False, "position {x}");
   }
   for &x in MIXED_DRAWN {
      assert_eq!(prog.win_truth(&(x,)), Truth::Undefined, "position {x}");
   }
   // positions that do not occur in the graph
   assert_eq!(prog.win_truth(&(0,)), Truth::False);
   assert_eq!(prog.win_truth(&(99,)), Truth::False);
   // user-supplied facts are true
   assert_eq!(prog.mv_truth(&(6, 6)), Truth::True);
   assert_eq!(prog.mv_truth(&(6, 7)), Truth::False);
}

#[test]
fn truth_of_lattice_max_values() {
   ascent! {
      #![well_founded]
      struct TruthLatMax;
      relation mv(u32, u32);
      relation win(u32);
      relation bid(u32, u32, u32);
      lattice best(u32, u32);
      relation rich(u32);
      win(x) <-- mv(x, y), !win(y);
      best(g, v) <-- bid(g, x, v), win(x);
      rich(g) <-- best(g, v), if *v >= 25;
   }
   let mut prog = TruthLatMax::default();
   prog.mv = AGG_MOVES.to_vec();
   prog.bid = vec![(1, 3, 10), (1, 7, 20), (2, 3, 10), (2, 1, 30), (3, 1, 5), (4, 3, 50), (4, 1, 40), (5, 4, 9)];
   prog.run();
   assert_eq!(prog.best_truth(&(1, 20)), Truth::True);
   assert_eq!(prog.best_truth(&(1, 10)), Truth::False);
   assert_eq!(prog.best_truth(&(2, 10)), Truth::True);
   assert_eq!(prog.best_truth(&(2, 30)), Truth::Undefined);
   assert_eq!(prog.best_truth(&(2, 20)), Truth::False);
   assert_eq!(prog.best_truth(&(3, 5)), Truth::Undefined);
   assert_eq!(prog.best_truth(&(3, 4)), Truth::False);
   // possible value equals the true value: only true
   assert_eq!(prog.best_truth(&(4, 50)), Truth::True);
   assert_eq!(prog.best_truth(&(4, 40)), Truth::False);
   assert_eq!(prog.best_truth(&(5, 9)), Truth::False);
   assert_eq!(prog.rich_truth(&(4,)), Truth::True);
   assert_eq!(prog.rich_truth(&(2,)), Truth::Undefined);
   assert_eq!(prog.rich_truth(&(1,)), Truth::False);
}

/// won: 3, 7; drawn: 1, 2, 5, 6; lost: 4, 8.
const AGG_MOVES: &[(u32, u32)] = &[(1, 2), (2, 1), (3, 4), (5, 6), (6, 5), (7, 8)];

#[cfg(feature = "par")]
fn lat_set<T: Ord + Clone>(rel: &ascent::boxcar::Vec<std::sync::RwLock<T>>) -> BTreeSet<T> {
   rel.iter().map(|row| row.read().unwrap().clone()).collect()
}

#[cfg(feature = "par")]
#[test]
fn par_win_move_mixed_graph_matches_serial() {
   ascent::ascent_par! {
      #![well_founded]
      struct ParWinMixed;
      relation mv(u32, u32);
      relation pos(u32);
      relation win(u32);
      relation lost(u32);
      pos(x) <-- mv(x, _);
      pos(y) <-- mv(_, y);
      win(x) <-- mv(x, y), !win(y);
      lost(x) <-- pos(x), !win(x);
   }
   ascent::ascent! {
      #![well_founded]
      struct SerWinMixed;
      relation mv(u32, u32);
      relation pos(u32);
      relation win(u32);
      relation lost(u32);
      pos(x) <-- mv(x, _);
      pos(y) <-- mv(_, y);
      win(x) <-- mv(x, y), !win(y);
      lost(x) <-- pos(x), !win(x);
   }
   let mut par = ParWinMixed::default();
   par.mv = FromIterator::from_iter(MIXED.iter().copied());
   par.run();
   let mut ser = SerWinMixed::default();
   ser.mv = MIXED.to_vec();
   ser.run();

   assert_eq!(set(&par.win), ones(MIXED_WON));
   assert_eq!(undef(&par.win_undefined), ones(MIXED_DRAWN));
   assert_eq!(set(&par.lost), ones(MIXED_LOST));
   assert_eq!(undef(&par.lost_undefined), ones(MIXED_DRAWN));
   assert_eq!(par.pos_undefined.len(), 0);

   assert_eq!(set(&par.win), set(&ser.win));
   assert_eq!(undef(&par.win_undefined), undef(&ser.win_undefined));
   assert_eq!(set(&par.lost), set(&ser.lost));
   assert_eq!(undef(&par.lost_undefined), undef(&ser.lost_undefined));
}

#[cfg(feature = "par")]
#[test]
fn par_agg_count_and_max_over_groups_with_undefined_members() {
   ascent::ascent_par! {
      #![well_founded]
      struct ParAgg;
      relation mv(u32, u32);
      relation win(u32);
      relation group(u32);
      relation member(u32, u32);
      relation member_win(u32, u32);
      relation cnt(u32, usize);
      relation hi(u32, u32);
      win(x) <-- mv(x, y), !win(y);
      member_win(g, x) <-- member(g, x), win(x);
      cnt(g, c) <-- group(g), agg c = ascent::aggregators::count() in member_win(g, _);
      hi(g, m) <-- group(g), agg m = ascent::aggregators::max(x) in member_win(g, x);
   }
   ascent::ascent! {
      #![well_founded]
      struct SerAgg;
      relation mv(u32, u32);
      relation win(u32);
      relation group(u32);
      relation member(u32, u32);
      relation member_win(u32, u32);
      relation cnt(u32, usize);
      relation hi(u32, u32);
      win(x) <-- mv(x, y), !win(y);
      member_win(g, x) <-- member(g, x), win(x);
      cnt(g, c) <-- group(g), agg c = ascent::aggregators::count() in member_win(g, _);
      hi(g, m) <-- group(g), agg m = ascent::aggregators::max(x) in member_win(g, x);
   }
   let groups = vec![(10,), (20,), (30,), (40,), (50,)];
   let members = vec![(10, 3), (10, 7), (20, 3), (20, 1), (30, 1), (30, 2), (40, 4), (50, 5), (50, 4)];
   let mut par = ParAgg::default();
   par.mv = FromIterator::from_iter(AGG_MOVES.iter().copied());
   par.group = FromIterator::from_iter(groups.clone());
   par.member = FromIterator::from_iter(members.clone());
   par.run();
   let mut ser = SerAgg::default();
   ser.mv = AGG_MOVES.to_vec();
   ser.group = groups;
   ser.member = members;
   ser.run();

   assert_eq!(set(&par.cnt), [(10, 2), (40, 0)].into_iter().collect::<BTreeSet<(u32, usize)>>());
   assert_eq!(
      undef(&par.cnt_undefined),
      [(20, 1), (20, 2), (30, 0), (30, 2), (50, 0), (50, 1)].into_iter().collect::<BTreeSet<(u32, usize)>>()
   );
   // group 10: max 7 true; 20: true {3} vs all {3, 1} -> 3 (equal) undefined; 30: only all -> 2;
   // 40: empty, nothing; 50: only all {5} -> 5
   assert_eq!(set(&par.hi), pairs(&[(10, 7)]));
   assert_eq!(undef(&par.hi_undefined), pairs(&[(20, 3), (30, 2), (50, 5)]));

   assert_eq!(set(&par.cnt), set(&ser.cnt));
   assert_eq!(undef(&par.cnt_undefined), undef(&ser.cnt_undefined));
   assert_eq!(set(&par.hi), set(&ser.hi));
   assert_eq!(undef(&par.hi_undefined), undef(&ser.hi_undefined));
}

#[cfg(feature = "par")]
#[test]
fn par_lattice_max_with_undefined_contributions() {
   ascent::ascent_par! {
      #![well_founded]
      struct ParLatMax;
      relation mv(u32, u32);
      relation win(u32);
      relation bid(u32, u32, u32);
      lattice best(u32, u32);
      relation rich(u32);
      win(x) <-- mv(x, y), !win(y);
      best(g, v) <-- bid(g, x, v), win(x);
      rich(g) <-- best(g, v), if *v >= 25;
   }
   let mut prog = ParLatMax::default();
   prog.mv = FromIterator::from_iter(AGG_MOVES.iter().copied());
   // (item, position, value); a bid counts if its position is won
   prog.bid = FromIterator::from_iter(vec![
      (1, 3, 10),
      (1, 7, 20),
      (2, 3, 10),
      (2, 1, 30),
      (3, 1, 5),
      (4, 3, 50),
      (4, 1, 40),
      (5, 4, 9),
   ]);
   prog.run();
   // item 1: all true; item 2: true 10, possible 30; item 3: only possible 5;
   // item 4: possible 50 equals true 50 (absent from `_undefined`); item 5: nothing.
   assert_eq!(lat_set(&prog.best), pairs(&[(1, 20), (2, 10), (4, 50)]));
   assert_eq!(undef(&prog.best_undefined), pairs(&[(2, 30), (3, 5)]));
   assert_eq!(set(&prog.rich), ones(&[4]));
   assert_eq!(undef(&prog.rich_undefined), ones(&[2]));
}

#[cfg(feature = "par")]
#[test]
fn par_truth_of_win_move_and_downstream() {
   use ascent::Truth;
   ascent::ascent_par! {
      #![well_founded]
      struct ParTruthWin;
      relation mv(u32, u32);
      relation pos(u32);
      relation win(u32);
      relation lost(u32);
      relation good(u32, u32);
      pos(x) <-- mv(x, _);
      pos(y) <-- mv(_, y);
      win(x) <-- mv(x, y), !win(y);
      lost(x) <-- pos(x), !win(x);
      good(x, y) <-- mv(x, y), !good(y, _);
   }
   let mut prog = ParTruthWin::default();
   prog.mv = FromIterator::from_iter(MIXED.iter().copied());
   prog.run();
   for &x in MIXED_WON {
      assert_eq!(prog.win_truth(&(x,)), Truth::True, "position {x}");
   }
   for &x in MIXED_LOST {
      assert_eq!(prog.win_truth(&(x,)), Truth::False, "position {x}");
   }
   for &x in MIXED_DRAWN {
      assert_eq!(prog.win_truth(&(x,)), Truth::Undefined, "position {x}");
   }
   assert_eq!(prog.win_truth(&(99,)), Truth::False);
   for &x in MIXED_LOST {
      assert_eq!(prog.lost_truth(&(x,)), Truth::True, "position {x}");
   }
   for &x in MIXED_DRAWN {
      assert_eq!(prog.lost_truth(&(x,)), Truth::Undefined, "position {x}");
   }
   assert_eq!(prog.lost_truth(&(2,)), Truth::False);
   assert_eq!(prog.good_truth(&(2, 3)), Truth::True);
   assert_eq!(prog.good_truth(&(12, 6)), Truth::Undefined);
   assert_eq!(prog.good_truth(&(1, 2)), Truth::False);
}
