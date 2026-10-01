import Flapjack.HolRef
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.Motive

namespace Flapjack.WordAlloc
open Flapjack.RegAlloc

/-- Flapjack case infrastructure: the original EVERY premise supplies either
projection of an indexed loop entry; an absent entry denotes the empty tree. -/
private theorem loopEntryWf (lt : List (NumSet × NumSet)) (index : Nat)
    (hw : ∀ p, p ∈ lt → sptWf p.1 = true ∧ sptWf p.2 = true) :
    sptWf ((lt[index]?).map Prod.fst |>.getD .ln) = true ∧
    sptWf ((lt[index]?).map Prod.snd |>.getD .ln) = true := by
  cases h : lt[index]? with
  | none => simp
  | some p => simpa using hw p (List.mem_of_getElem? h)

/-- The Break case retains all six original premises and all five conclusions. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "clash_tree_colouring_ok" (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_Break {width : Nat} [NeZero width] (index : Nat) :
    clashTreeGoal (.break index : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨-, -, ht, -, hi, hc⟩
  simp only [getClashTree, checkClashTree] at hc
  obtain ⟨he, hinj, hd⟩ := checkColInj f _ livein flivein hc
  subst livein
  refine ⟨(loopEntryWf lt index ht).2, hinj, ?_, by simp only [getLive], hd⟩
  simpa only [colouringOk, getLive, getWrites, sptUnion] using And.intro hinj hi

/-- The Continue case retains all six original premises and all five conclusions. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "clash_tree_colouring_ok" (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_Continue {width : Nat} [NeZero width] (index : Nat) :
    clashTreeGoal (.continue index : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨-, -, ht, -, hi, hc⟩
  simp only [getClashTree, checkClashTree] at hc
  obtain ⟨he, hinj, hd⟩ := checkColInj f _ livein flivein hc
  subst livein
  refine ⟨(loopEntryWf lt index ht).1, hinj, ?_, by simp only [getLive], hd⟩
  simpa only [colouringOk, getLive, getWrites, sptUnion] using And.intro hinj hi

/-- The Loop case uses only the original body induction hypothesis. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "clash_tree_colouring_ok" (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_Loop {width : Nat} [NeZero width]
    (names exitNames : NumSet) (body : WordLangProgHOL (BitVec width))
    (ih : clashTreeGoal body) : clashTreeGoal (.loop names body exitNames) := by
  rintro lt f live flive livein flivein ⟨hw, -, ht, -, -, hc⟩
  obtain ⟨hn, he, hb⟩ := hw
  simp only [getClashTree, checkClashTree] at hc
  cases hnames : checkCol f names with
  | none => simp only [hnames] at hc; cases hc
  | some pair =>
    obtain ⟨n, fn⟩ := pair
    obtain ⟨en, injn, imgn⟩ := checkColInj f names n fn hnames
    subst n
    simp only [hnames] at hc
    cases hbody : checkClashTree f (getClashTree body ((names, exitNames) :: lt)) names fn with
    | none => simp only [hbody] at hc; cases hc
    | some pair =>
      obtain ⟨b, fb⟩ := pair
      simp only [hbody] at hc
      cases hexit : checkCol f exitNames with
      | none => simp only [hexit] at hc; cases hc
      | some pair =>
        obtain ⟨e, fe⟩ := pair
        simp only [hexit] at hc
        obtain ⟨ee, inje, -⟩ := checkColInj f exitNames e fe hexit
        subst e
        have htNew : ∀ p, p ∈ (names, exitNames) :: lt →
            sptWf p.1 = true ∧ sptWf p.2 = true := by
          intro p hp
          rcases List.mem_cons.mp hp with hp | hp
          · subst p; exact ⟨hn, he⟩
          · exact ht p hp
        obtain ⟨-, -, cb, -, -⟩ := ih _ f names fn b fb
          ⟨hb, hn, htNew, imgn, injn, hbody⟩
        cases Option.some.inj hc
        refine ⟨hn, injn, ?_, by simp only [getLive], imgn⟩
        exact ⟨injn, inje, cb⟩

end Flapjack.WordAlloc
