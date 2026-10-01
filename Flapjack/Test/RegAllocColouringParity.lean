import Flapjack.Compiler.Backend.RegAlloc.Colouring
namespace Flapjack.Test.RegAllocColouringParity
open Flapjack Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-! Kernel replay of `scripts/hol-probes/reg_alloc_colouring_probe.out`: original
HOL `remove_colours`, `assign_Atemp_tag`, `assign_Atemps` and `first_match_col`
rows on two concrete states and two preference oracles. -/

private def s0 : State :=
  { adj_ls := [[1], [0, 2], [1]], node_tag := [.Fixed 0, .Atemp, .Stemp], degrees := [1, 2, 1],
    dim := 3, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [],
    unavail_moves_wl := [], coalesced := [0, 1, 2], move_related := [false, false, false],
    stack := [] }
private def s1 : State :=
  { adj_ls := [[1, 2], [0], [0], []], node_tag := [.Fixed 1, .Atemp, .Atemp, .Atemp],
    degrees := [2, 1, 1, 0], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [],
    avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 2, 3],
    move_related := [false, false, false, false], stack := [] }
private def pnone : Nat → List Nat → M State (Option Nat) StateException :=
  fun _ _ s => (.success none, s)
/-- HOL's `λn ks s. (M_success (SOME (LAST ks)), s)`; the oracle is only called with a
nonempty `ks`, where `getLast?.getD 0` is `LAST ks`. -/
private def plast : Nat → List Nat → M State (Option Nat) StateException :=
  fun _ ks s => (.success (some (ks.getLast?.getD 0)), s)

-- rc_empty_ks=M_success []
example : (removeColours [0, 1] [] s0).1 = .success [] := by decide
-- rc_no_nodes=M_success [3; 4]
example : (removeColours [] [3, 4] s0).1 = .success [3, 4] := by decide
-- rc_fixed=M_success [1; 2]
example : (removeColours [0, 1] [0, 1, 2] s0).1 = .success [1, 2] := by decide
-- rc_dup_colours=M_success [1]
example : (removeColours [0] [0, 0, 1] s0).1 = .success [1] := by decide
-- rc_oob=M_failure Subscript
example : (removeColours [5] [1] s0).1 = .failure .Subscript := by decide
-- rc_oob_after_empty=M_success []
example : (removeColours [0, 5] [0] s0).1 = .success [] := by decide
-- aat_none=[Fixed 0; Fixed 1; Stemp]
example : (assignAtempTag [0, 1, 2] pnone 1 s0).2.node_tag = [.Fixed 0, .Fixed 1, .Stemp] := by
  decide
-- aat_pref=[Fixed 0; Fixed 2; Stemp]
example : (assignAtempTag [0, 1, 2] plast 1 s0).2.node_tag = [.Fixed 0, .Fixed 2, .Stemp] := by
  decide
-- aat_stemp=[Fixed 0; Stemp; Stemp]
example : (assignAtempTag [0] pnone 1 s0).2.node_tag = [.Fixed 0, .Stemp, .Stemp] := by decide
-- aat_non_atemp=T
example : assignAtempTag [0, 1, 2] pnone 0 s0 = (.success (), s0) := by decide
-- aat_oob=M_failure Subscript
example : (assignAtempTag [0, 1, 2] pnone 5 s0).1 = .failure .Subscript := by decide
-- aa_all=(M_success (),[Fixed 1; Fixed 0; Fixed 0; Fixed 0])
example : ((assignAtemps 3 [2, 9, 1] pnone s1).1, (assignAtemps 3 [2, 9, 1] pnone s1).2.node_tag) =
    (.success (), [.Fixed 1, .Fixed 0, .Fixed 0, .Fixed 0]) := by decide
-- aa_pref=[Fixed 1; Fixed 2; Fixed 2; Fixed 2]
example : (assignAtemps 3 [] plast s1).2.node_tag = [.Fixed 1, .Fixed 2, .Fixed 2, .Fixed 2] := by
  decide
-- aa_one_colour=[Fixed 1; Fixed 0; Fixed 0; Fixed 0]
example : (assignAtemps 1 [3] pnone s1).2.node_tag = [.Fixed 1, .Fixed 0, .Fixed 0, .Fixed 0] := by
  decide
-- fmc_hit=M_success (SOME 0)
example : (firstMatchCol [1, 0] [1, 0] s0).1 = .success (some 0) := by decide
-- fmc_not_in_ks=M_success NONE
example : (firstMatchCol [5] [0, 1] s0).1 = .success none := by decide
-- fmc_empty=M_success NONE
example : (firstMatchCol [0] [] s0).1 = .success none := by decide
-- fmc_oob=M_failure Subscript
example : (firstMatchCol [0] [36893488147419103232] s0).1 = .failure .Subscript := by decide

end Flapjack.Test.RegAllocColouringParity
