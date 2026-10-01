import Flapjack.Compiler.Backend.RegAlloc.Proofs
namespace Flapjack.Test.RegAllocCheckPartialColParity
open Flapjack Flapjack.RegAlloc

/-! Kernel replay of `scripts/hol-probes/reg_alloc_check_partial_col_probe.out`:
original HOL `check_partial_col` rows through `toAList`, with
`checkPartialColSuccess` and `checkPartialColDomain` applied to them. -/

private def obs (r : Option (NumSet × NumSet)) : Option (List (Nat × Unit) × List (Nat × Unit)) :=
  r.map fun p => (sptToAList p.1, sptToAList p.2)
private def s3 : NumSet := sptInsert 3 () .ln
private def s4 : NumSet := sptInsert 4 () .ln
private def s0 : NumSet := sptInsert 0 () .ln

-- cpc_inj=SOME ([(3,()); (1,()); (2,())],[(3,()); (4,()); (2,())])
example : obs (checkPartialCol (fun x => x + 1) [1, 2] s3 s4) =
    some ([(3, ()), (1, ()), (2, ())], [(3, ()), (4, ()), (2, ())]) := by
  simp [obs, s3, s4, checkPartialCol, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext]
-- cpc_present=SOME ([(3,())],[(0,())])
example : obs (checkPartialCol (fun _ => 0) [3] s3 s0) = some ([(3, ())], [(0, ())]) := by
  simp [obs, s3, s0, checkPartialCol, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext]
-- cpc_dup=SOME ([(1,())],[(1,())])
example : obs (checkPartialCol (fun x => x) [1, 1] .ln .ln) = some ([(1, ())], [(1, ())]) := by
  simp [obs, checkPartialCol, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext]
-- cpc_clash_live=NONE
example : obs (checkPartialCol (fun _ => 0) [1] s3 s0) = none := by
  simp [obs, s3, s0, checkPartialCol, sptInsert, sptLookup, sptToAList]
-- cpc_clash_list=NONE
example : obs (checkPartialCol (fun _ => 0) [1, 2] .ln .ln) = none := by
  simp [obs, checkPartialCol, sptInsert, sptLookup, sptToAList]
-- cpc_domain=SOME [3; 1; 5]
example : (checkPartialCol (fun x => x + 1) [5, 1] s3 s4).map (fun p => (sptToAList p.1).map Prod.fst)
    = some [3, 1, 5] := by
  simp [s3, s4, checkPartialCol, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext]
-- cpc_large=SOME ([(36893488147419103232,())],[(36893488147419103232,())])
example : obs (checkPartialCol (fun x => x) [36893488147419103232] .ln .ln) =
    some ([(36893488147419103232, ())], [(36893488147419103232, ())]) := by
  simp [obs, checkPartialCol, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext]

private theorem dom3 (k : Nat) : sptDomain s3 k ↔ k = 3 := by
  by_cases h : k = 3
  · subst h; simp [sptDomain, s3, sptLookup_sptInsert_same]
  · simp [sptDomain, s3, sptLookup_sptInsert_ne _ _ _ _ h, sptLookup, h]
private theorem dom4 (k : Nat) : sptDomain s4 k ↔ k = 4 := by
  by_cases h : k = 4
  · subst h; simp [sptDomain, s4, sptLookup_sptInsert_same]
  · simp [sptDomain, s4, sptLookup_sptInsert_ne _ _ _ _ h, sptLookup, h]

/-- `check_partial_col_success` at the `cpc_inj` inputs: `x + 1` is injective and
`{4}` is the image of `{3}`. -/
example : ∃ livein flivein, checkPartialCol (fun x => x + 1) [1, 2] s3 s4 = some (livein, flivein) ∧
    sptDomain flivein = (fun y => ∃ x, sptDomain livein x ∧ x + 1 = y) :=
  checkPartialColSuccess [1, 2] s3 s4 (fun x => x + 1)
    ⟨by funext y; apply propext; simp [dom3, dom4]; omega, fun a b _ _ h => by omega⟩

/-- `check_partial_col_domain` at the `cpc_domain` inputs. -/
example (v : NumSet × NumSet) (h : checkPartialCol (fun x => x + 1) [5, 1] s3 s4 = some v) :
    sptDomain v.1 = fun x => x ∈ [5, 1] ∨ sptDomain s3 x :=
  checkPartialColDomain _ _ _ _ v h

end Flapjack.Test.RegAllocCheckPartialColParity
