import Flapjack.Pancake.WordLang

namespace Flapjack

/-- Pointwise implication preserves the actual occurrence predicate over
every expression constructor and its full recursive operator argument list. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml"
  "every_var_exp_mono" (words_as_type_indexed_bitvec)]
theorem everyVarExpMono {width : Nat} [NeZero width] (P : Nat → Bool)
    (expression : WordLangExpHOL (BitVec width)) (Q : Nat → Bool) :
    ((∀ x, P x = true → Q x = true) ∧ everyVarExpHOL P expression = true) →
      everyVarExpHOL Q expression = true := by
  rintro ⟨hmono, hP⟩
  refine WordLangExpHOL.rec
    (motive_1 := fun e : WordLangExpHOL (BitVec width) =>
      everyVarExpHOL P e = true → everyVarExpHOL Q e = true)
    (motive_2 := fun es : List (WordLangExpHOL (BitVec width)) =>
      everyVarExpsHOL P es = true → everyVarExpsHOL Q es = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ expression hP
  · intro value; simp [everyVarExpHOL]
  · intro name; simpa [everyVarExpHOL] using hmono name
  · intro store; simp [everyVarExpHOL]
  · intro address ih; simpa [everyVarExpHOL] using ih
  · intro operator arguments ih; simpa [everyVarExpHOL] using ih
  · intro operator left right ihLeft ihRight h
    simp only [everyVarExpHOL, Bool.and_eq_true] at h ⊢
    exact ⟨ihLeft h.1, ihRight h.2⟩
  · simp [everyVarExpsHOL]
  · intro head tail ihHead ihTail h
    simp only [everyVarExpsHOL, Bool.and_eq_true] at h ⊢
    exact ⟨ihHead h.1, ihTail h.2⟩

end Flapjack
