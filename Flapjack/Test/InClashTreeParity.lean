import Flapjack.Compiler.Backend.RegAlloc.Proofs
namespace Flapjack.Test.InClashTreeParity
open Flapjack Flapjack.RegAlloc

/-! Kernel replay of `scripts/hol-probes/reg_alloc_in_clash_tree_probe.out`:
original HOL `in_clash_tree` rows (`T`/`F` as proved `Prop`s) and
`check_clash_tree` composition observations, read through `toAList`. -/

private def s5 : NumSet := sptInsert 5 () .ln
private def s9 : NumSet := sptInsert 9 () .ln
private def s4 : NumSet := sptInsert 4 () .ln

-- ict_delta_write=T
example : inClashTree (.delta [1, 2] [3]) 2 := by simp [inClashTree]
-- ict_delta_read=T
example : inClashTree (.delta [1, 2] [3]) 3 := by simp [inClashTree]
-- ict_delta_miss=F
example : ¬ inClashTree (.delta [1, 2] [3]) 4 := by simp [inClashTree]
-- ict_set=T
example : inClashTree (.set s5) 5 := by simp [inClashTree, sptDomain, s5, sptInsert, sptLookup]
-- ict_set_miss=F
example : ¬ inClashTree (.set s5) 6 := by simp [inClashTree, sptDomain, s5, sptInsert, sptLookup]
-- ict_set_raw=T
example : inClashTree (.set (.bs .ln () .ln)) 0 := by simp [inClashTree, sptDomain, sptLookup]
-- ict_branch_left=T
example : inClashTree (.branch none (.delta [1] []) (.delta [2] [])) 1 := by simp [inClashTree]
-- ict_branch_right=T
example : inClashTree (.branch none (.delta [1] []) (.delta [2] [])) 2 := by simp [inClashTree]
-- ict_branch_none_miss=F
example : ¬ inClashTree (.branch none (.delta [1] []) (.delta [2] [])) 9 := by simp [inClashTree]
-- ict_branch_some=T
example : inClashTree (.branch (some s9) (.delta [1] []) (.delta [2] [])) 9 := by
  simp [inClashTree, sptDomain, s9, sptInsert, sptLookup]
-- ict_branch_some_miss=F
example : ¬ inClashTree (.branch (some s9) (.delta [1] []) (.delta [2] [])) 8 := by
  simp [inClashTree, sptDomain, s9, sptInsert, sptLookup]
-- ict_seq_left=T
example : inClashTree (.seq (.delta [1] []) (.set s4)) 1 := by simp [inClashTree]
-- ict_seq_right=T
example : inClashTree (.seq (.delta [1] []) (.set s4)) 4 := by simp [inClashTree, sptDomain, s4, sptInsert, sptLookup]
-- ict_large=T
example : inClashTree (.delta [36893488147419103232] []) 36893488147419103232 := by
  simp [inClashTree]

private def tree : ClashTree := .seq (.delta [1] [2]) (.set (sptInsert 2 () .ln))
private def obs (r : Option (NumSet × NumSet)) : Option (List (Nat × Unit) × List (Nat × Unit)) :=
  r.map fun p => (sptToAList p.1, sptToAList p.2)

-- cct_ok_f=SOME ([(2,())],[(3,())])
example : obs (checkClashTree (fun x => x + 1) tree .ln .ln) = some ([(2, ())], [(3, ())]) := by
  simp [obs, tree, checkClashTree, checkPartialCol, checkCol, numsetListDelete, sptDelete, sptMkBN, sptInsert, sptLookup, sptToAList, sptFoldi, sptFromAList, lrNext]
-- cct_ok_gf=SOME ([(2,())],[(6,())])
example : obs (checkClashTree ((fun x => 2 * x) ∘ (fun x => x + 1)) tree .ln .ln)
    = some ([(2, ())], [(6, ())]) := by
  simp [obs, tree, checkClashTree, checkPartialCol, checkCol, numsetListDelete, sptDelete, sptMkBN, sptInsert, sptLookup, sptToAList, sptFoldi, sptFromAList, lrNext, Function.comp]
-- cct_collision_f=NONE
example : obs (checkClashTree (fun _ => 0) (.delta [] [1, 2]) .ln .ln) = none := by
  simp [obs, checkClashTree, checkPartialCol, numsetListDelete, sptInsert, sptLookup, sptToAList]
-- cct_collision_gf=NONE
example : obs (checkClashTree ((fun x => 2 * x) ∘ (fun _ => 0)) (.delta [] [1, 2]) .ln .ln)
    = none := by
  simp [obs, checkClashTree, checkPartialCol, numsetListDelete, sptInsert, sptLookup, sptToAList, Function.comp]

/-- `check_clash_tree_INJ` instantiated at the probe's tree, `f = (· + 1)`,
`g = (2 * ·)` and empty incoming sets: HOL's `cct_ok_f`/`cct_ok_gf` rows are a
witness of the composed result it asserts. -/
example : match checkClashTree (fun x => x + 1) tree .ln .ln with
    | none => checkClashTree ((fun x => 2 * x) ∘ (fun x => x + 1)) tree .ln .ln = none
    | some (liveout, fliveout) => ∃ gliveout,
        checkClashTree ((fun x => 2 * x) ∘ (fun x => x + 1)) tree .ln .ln = some (liveout, gliveout) ∧
        sptDomain gliveout = (fun y => ∃ x, sptDomain fliveout x ∧ 2 * x = y) :=
  checkClashTreeInj tree (fun x => x + 1) (fun x => 2 * x) .ln .ln .ln
    ⟨fun a b h => by omega, by funext y; simp [sptDomain, sptLookup]⟩

end Flapjack.Test.InClashTreeParity
