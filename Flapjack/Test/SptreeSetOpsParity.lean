import Flapjack.Misc.Sptree

/-! Direct HOL parity for sptree operations. The set operations used by
    `loop_live` (`sptree$union`, `inter`, `delete`, `backend_common$list_delete`,
    `list$oEL`) match `sptree_set_ops_probe.out`. Constructor-level
    `sptree$difference` rows match the external HOL `EVAL` fixture
    `sptree_difference_probe.out`; the latter assertions compare exact trees,
    so they also check payload retention and `mk_BN`/`mk_BS` collapse behavior. -/

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

/-- Direct replay of each clause in HOL `sptree$difference`
(`HOL/src/finite_maps/sptreeScript.sml:319-339`). The operands intentionally
have different value types as in HOL's heterogeneous map operation. These
closed checks are kernel-reduced Lean computations against
`scripts/hol-probes/sptree_difference_probe.out`. -/
def sptreeDifferenceGuard : Bool :=
  decide (sptDifference (.ln : Spt Nat) (.bs .ln true .ln : Spt Bool) = .ln) &&
  decide (sptDifference (.ls 17 : Spt Nat) (.ln : Spt Bool) = .ls 17) &&
  decide (sptDifference (.ls 17 : Spt Nat) (.ls false : Spt Bool) = .ln) &&
  decide (sptDifference (.ls 17 : Spt Nat) (.bn (.ls true) .ln : Spt Bool) = .ls 17) &&
  decide (sptDifference (.ls 17 : Spt Nat) (.bs .ln false .ln : Spt Bool) = .ln) &&
  decide (sptDifference (.bn (.ls 11) (.ls 22) : Spt Nat) (.ln : Spt Bool) =
      .bn (.ls 11) (.ls 22)) &&
  decide (sptDifference (.bn (.ls 11) (.ls 22) : Spt Nat) (.ls false : Spt Bool) =
      .bn (.ls 11) (.ls 22)) &&
  decide (sptDifference (.bn (.ls 11) (.ls 22) : Spt Nat) (.bn (.ls true) .ln : Spt Bool) =
      .bn .ln (.ls 22)) &&
  decide (sptDifference (.bn (.ls 11) .ln : Spt Nat) (.bn (.ls true) .ln : Spt Bool) = .ln) &&
  decide (sptDifference (.bn (.ls 11) (.ls 22) : Spt Nat) (.bs (.ls true) false .ln : Spt Bool) =
      .bn .ln (.ls 22)) &&
  decide (sptDifference (.bs (.ls 11) 33 (.ls 22) : Spt Nat) (.ln : Spt Bool) =
      .bs (.ls 11) 33 (.ls 22)) &&
  decide (sptDifference (.bs (.ls 11) 33 (.ls 22) : Spt Nat) (.ls false : Spt Bool) =
      .bn (.ls 11) (.ls 22)) &&
  decide (sptDifference (.bs .ln 33 .ln : Spt Nat) (.bn .ln .ln : Spt Bool) = .ls 33) &&
  decide (sptDifference (.bs (.ls 11) 33 (.ls 22) : Spt Nat) (.bn (.ls true) .ln : Spt Bool) =
      .bs .ln 33 (.ls 22)) &&
  decide (sptDifference (.bs (.ls 11) 33 (.ls 22) : Spt Nat) (.bs .ln false .ln : Spt Bool) =
      .bn (.ls 11) (.ls 22)) &&
  decide (sptDifference (.bs (.ls 11) 33 .ln : Spt Nat) (.bs (.ls true) false .ln : Spt Bool) =
      .ln)

#guard sptreeDifferenceGuard

/-- Kernel-checked replay of the constructor-level difference oracle rows. -/
theorem sptreeDifferenceGuard_proof : sptreeDifferenceGuard = true := by
  simp [sptreeDifferenceGuard, sptDifference, sptMkBN, sptMkBS]

def runChecks : IO Bool := do
  if sptreeSetOpsGuard then
    IO.println "PASS sptree set operations HOL parity"
  else
    IO.println "FAIL sptree set operations HOL parity"
  if sptreeInterMixedGuard then
    IO.println "PASS heterogeneous sptree inter (mixed-payload) HOL parity"
  else
    IO.println "FAIL heterogeneous sptree inter (mixed-payload) HOL parity"
  if sptreeDifferenceGuard then
    IO.println "PASS heterogeneous sptree difference direct HOL EVAL parity"
  else
    IO.println "FAIL heterogeneous sptree difference direct HOL EVAL parity"
  pure (sptreeSetOpsGuard && sptreeInterMixedGuard && sptreeDifferenceGuard)

end Flapjack.Test.SptreeSetOpsParity
