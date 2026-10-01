import Flapjack.HolRef
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.Motive
import Flapjack.Misc.Sptree.UnionAlgebra

namespace Flapjack.WordAlloc
open Flapjack.RegAlloc

/-- Exact returning Call with no exception handler. The only induction
hypothesis is the full original motive for the return program. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "clash_tree_colouring_ok" (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_ReturnNoHandler {width : Nat} [NeZero width]
    (vs : List Nat) (cuts : WordLangCutsetsHOL)
    (ret : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat) (ih : clashTreeGoal ret) :
    clashTreeGoal (.call (some (vs, cuts, ret, l1, l2)) dest args none) := by
  rintro lt f live flive livein flivein ⟨hw, hl, ht, hd, hi, hc⟩
  obtain ⟨hcuts, hret, -⟩ := hw
  simp only [getClashTree, checkClashTree] at hc
  cases hbody : checkClashTree f (getClashTree ret lt) live flive with
  | none => simp only [hbody] at hc; cases hc
  | some pair =>
    obtain ⟨b, fb⟩ := pair
    simp only [hbody] at hc
    cases hreturn : checkCol f (numsetListInsert vs (sptUnion cuts.1 cuts.2)) with
    | none => simp only [hreturn] at hc; cases hc
    | some pair =>
      obtain ⟨r, fr⟩ := pair
      simp only [hreturn] at hc
      obtain ⟨er, injret, -⟩ := checkColInj f _ r fr hreturn
      subst r
      obtain ⟨el, injlive, imglive⟩ := checkColInj f _ livein flivein hc
      subst livein
      obtain ⟨-, -, colret, -, -⟩ := ih lt f live flive b fb
        ⟨hret, hl, ht, hd, hi, hbody⟩
      have hwUnion : sptWf (sptUnion cuts.1 cuts.2) = true := sptWfUnion _ _ hcuts
      refine ⟨sptWfUnion _ _ ⟨hwUnion, sptWf_numsetListInsert .ln rfl args⟩,
        injlive, ?_, by simp only [getLive], imglive⟩
      simp only [colouringOk, sptUnion_numSet_sym cuts.2 cuts.1]
      exact ⟨injlive, injret, colret, trivial⟩

end Flapjack.WordAlloc
