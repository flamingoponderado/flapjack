import Flapjack.Pancake.WordLang.OccurrencesExact

namespace Flapjack

/-- Pointwise implication preserves the literal key enumeration of both
canonical Spt cut sets, including trees without a well-formedness premise. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "every_name_mono"]
theorem everyNameMono (P : Nat → Bool) (names : WordLangCutsetsHOL)
    (Q : Nat → Bool) :
    ((∀ x, P x = true → Q x = true) ∧ everyNameHOL P names = true) →
      everyNameHOL Q names = true := by
  rintro ⟨hmono, hP⟩
  simp only [everyNameHOL, Bool.and_eq_true, List.all_eq_true] at hP ⊢
  exact ⟨fun x hx => hmono x (hP.1 x hx),
    fun x hx => hmono x (hP.2 x hx)⟩

end Flapjack
