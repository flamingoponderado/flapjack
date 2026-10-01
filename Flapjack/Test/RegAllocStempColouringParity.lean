import Flapjack.Compiler.Backend.RegAlloc.StempColouring
namespace Flapjack.Test.RegAllocStempColouringParity
open Flapjack Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-! Kernel replay of `scripts/hol-probes/reg_alloc_stemp_colouring_probe.out`:
original HOL `tag_col`, `unbound_colour`, `assign_Stemp_tag`, `assign_Stemps`,
`neg_first_match_col` and `neg_biased_pref` rows (the two type rows are compared
in the manifest review). -/

private def s0 : State :=
  { adj_ls := [[1, 2], [0], [0, 3], [2]], node_tag := [.Stemp, .Fixed 5, .Fixed 3, .Stemp],
    degrees := [2, 1, 2, 1], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [],
    avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 2, 3],
    move_related := [false, false, false, false], stack := [] }
private def pnone : Nat → List Nat → M State (Option Nat) StateException :=
  fun _ _ s => (.success none, s)
private def pnine : Nat → List Nat → M State (Option Nat) StateException :=
  fun _ _ s => (.success (some 9), s)

-- st_tag_col=(7,0,0)
example : (tagCol (.Fixed 7), tagCol .Atemp, tagCol .Stemp) = (7, 0, 0) := rfl
-- st_unbound_empty=4
example : unboundColour 4 [] = 4 := rfl
-- st_unbound_gap=5
example : unboundColour 3 [3, 4, 6] = 5 := by decide
-- st_unbound_below=4
example : unboundColour 3 [0, 1, 3, 5] = 4 := by decide
-- st_unbound_dup=4
example : unboundColour 2 [2, 2, 3] = 4 := by decide
-- st_tag_none=[Fixed 4; Fixed 5; Fixed 3; Stemp]
example : (assignStempTag 3 pnone 0 s0).2.node_tag = [.Fixed 4, .Fixed 5, .Fixed 3, .Stemp] := by
  decide +kernel
-- st_tag_pref=[Fixed 9; Fixed 5; Fixed 3; Stemp]
example : (assignStempTag 3 pnine 0 s0).2.node_tag = [.Fixed 9, .Fixed 5, .Fixed 3, .Stemp] := by
  decide +kernel
-- st_tag_non_stemp=T
example : assignStempTag 3 pnone 1 s0 = (.success (), s0) := by decide
-- st_tag_oob=M_failure Subscript
example : (assignStempTag 3 pnone 7 s0).1 = .failure .Subscript := by decide
-- st_all=(M_success (),[Fixed 4; Fixed 5; Fixed 3; Fixed 4])
example : ((assignStemps 3 pnone s0).1, (assignStemps 3 pnone s0).2.node_tag) =
    (.success (), [.Fixed 4, .Fixed 5, .Fixed 3, .Fixed 4]) := by decide +kernel
-- st_all_k_high=[Fixed 6; Fixed 5; Fixed 3; Fixed 6]
example : (assignStemps 6 pnone s0).2.node_tag = [.Fixed 6, .Fixed 5, .Fixed 3, .Fixed 6] := by
  decide +kernel
-- st_neg_first_hit=M_success (SOME 5)
example : (negFirstMatchCol 4 [3] [2, 1] s0).1 = .success (some 5) := by decide
-- st_neg_first_bad=M_success NONE
example : (negFirstMatchCol 4 [5] [1, 2] s0).1 = .success none := by decide
-- st_neg_first_oob=M_failure Subscript
example : (negFirstMatchCol 0 [] [9] s0).1 = .failure .Subscript := by decide
-- st_neg_biased=M_success (SOME 5)
example : (negBiasedPref 4 (sptInsert 0 [2, 1] .ln) 0 [] s0).1 = .success (some 5) := by
  simp [negBiasedPref, s0, getDim, sptLookup, handleSubscript, negFirstMatchCol,
    nodeTagSub, arraySub, mSub, Flapjack.Translator.Monadic.MonadBase.bind,
    Flapjack.Translator.Monadic.MonadBase.ret]
-- st_neg_biased_missing=M_success NONE
example : (negBiasedPref 4 (sptInsert 0 [2, 1] .ln) 3 [] s0).1 = .success none := by
  simp [negBiasedPref, s0, getDim, sptLookup, handleSubscript, negFirstMatchCol, Flapjack.Translator.Monadic.MonadBase.ret,
    Flapjack.Translator.Monadic.MonadBase.bind]
-- st_neg_biased_oob_partner=M_success NONE
example : (negBiasedPref 0 (sptInsert 0 [9, 1] .ln) 0 [] s0).1 = .success none := by
  simp [negBiasedPref, s0, getDim, sptLookup, handleSubscript, negFirstMatchCol,
    nodeTagSub, arraySub, mSub, Flapjack.Translator.Monadic.MonadBase.bind,
    Flapjack.Translator.Monadic.MonadBase.ret]
-- st_neg_biased_out_of_dim=M_success NONE
example : (negBiasedPref 0 (sptInsert 8 [1] .ln) 8 [] s0).1 = .success none := by
  simp [negBiasedPref, s0, getDim, Flapjack.Translator.Monadic.MonadBase.bind,
    Flapjack.Translator.Monadic.MonadBase.ret]

end Flapjack.Test.RegAllocStempColouringParity
