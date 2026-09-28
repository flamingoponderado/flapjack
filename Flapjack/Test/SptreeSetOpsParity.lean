import Flapjack.Misc.Sptree

/-! Direct HOL parity for the sptree set operations used by `loop_live`
    (`sptree$union`, `inter`, `delete`, `backend_common$list_delete`, `list$oEL`).
    Each row matches `scripts/hol-probes/sptree_set_ops_probe.out`, the HOL
    `EVAL` of the same expression; trees are compared through their `toAList`
    key order and emptiness. -/

namespace Flapjack.Test.SptreeSetOpsParity

open Flapjack

private def keys (t : Spt Unit) : List Nat := (sptToAList t).map Prod.fst

private def set (ks : List Nat) : Spt Unit := sptFromAList (ks.map fun k => (k, ()))

def sptreeSetOpsGuard : Bool :=
  -- union_keys=[1; 9; 0; 4; 6]
  keys (sptUnion (set [0, 4, 6]) (set [1, 4, 9])) == [1, 9, 0, 4, 6] &&
  -- union_ln=T
  sptIsEmpty (sptUnion (.ln : Spt Unit) .ln) &&
  -- inter_keys=[9; 4]
  keys (sptInter (set [0, 4, 6, 9]) (set [1, 4, 9])) == [9, 4] &&
  -- inter_disjoint_empty=T
  sptIsEmpty (sptInter (set [0, 2]) (set [1, 3])) &&
  -- delete_keys=[9; 0; 6]
  keys (sptDelete 4 (set [0, 4, 6, 9])) == [9, 0, 6] &&
  -- delete_last_empty=T
  sptIsEmpty (sptDelete 5 (set [5])) &&
  -- delete_absent_keys=[0; 4]
  keys (sptDelete 7 (set [0, 4])) == [0, 4] &&
  -- list_delete_keys=[0; 6]
  keys (sptListDelete [4, 9, 11] (set [0, 4, 6, 9])) == [0, 6] &&
  -- oel_hit=SOME 20, oel_miss=NONE
  sptOel 1 [10, 20, 30] == some 20 &&
  sptOel 3 [10, 20, 30] == none

#guard sptreeSetOpsGuard

/-- Mixed-payload parity rows for the HETEROGENEOUS `sptInter`
(`Spt α → Spt β → Spt α`), matching `sptree_inter_mixed_probe.out`: the result
keeps the LEFT operand's values on keys present in both trees. -/
def sptreeInterMixedGuard : Bool :=
  -- inter_mixed_keys=[4]
  ((sptToAList (sptInter (sptFromAList [(0, (7 : Nat)), (4, 8)]) (sptFromAList [(4, ()), (9, ())]))).map Prod.fst
      == [4]) &&
  -- inter_mixed_vals=[8]
  ((sptToAList (sptInter (sptFromAList [(0, (7 : Nat)), (4, 8)]) (sptFromAList [(4, ()), (9, ())]))).map Prod.snd
      == [8]) &&
  -- inter_mixed_left_only=[false]
  ((sptToAList (sptInter (sptFromAList [(0, true), (4, false)]) (sptFromAList [(1, ()), (4, ())]))).map Prod.snd
      == [false]) &&
  -- inter_mixed_disjoint=T
  sptIsEmpty (sptInter (sptFromAList [(0, (7 : Nat))]) (sptFromAList [(1, ())]))

#guard sptreeInterMixedGuard

def runChecks : IO Bool := do
  if sptreeSetOpsGuard then
    IO.println "PASS sptree set operations HOL parity"
  else
    IO.println "FAIL sptree set operations HOL parity"
  if sptreeInterMixedGuard then
    IO.println "PASS heterogeneous sptree inter (mixed-payload) HOL parity"
  else
    IO.println "FAIL heterogeneous sptree inter (mixed-payload) HOL parity"
  pure (sptreeSetOpsGuard && sptreeInterMixedGuard)

end Flapjack.Test.SptreeSetOpsParity
