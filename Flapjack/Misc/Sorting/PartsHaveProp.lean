import Flapjack.Misc.Sorting

/-!
# HOL sorting `PARTs_HAVE_PROP`

Exact port of `HOL/src/sort/sortingScript.sml` `PARTs_HAVE_PROP` (684-697) in
the pinned upstream HOL submodule, over the tagged `holPart`. The predicate
`'a -> bool` is a `Bool`-valued function as in `PART_DEF`.
-/

namespace Flapjack

/-- Exact HOL `PARTs_HAVE_PROP` (`sortingScript.sml:684-697`). -/
@[hol "HOL/src/sort/sortingScript.sml" "PARTs_HAVE_PROP"]
theorem holPartsHaveProp {α : Type} :
    ∀ (P : α → Bool) (L A B l1 l2 : List α),
      (A, B) = holPart P L l1 l2 ∧ (∀ x, x ∈ l1 → P x = true) ∧ (∀ x, x ∈ l2 → ¬ P x = true) →
        (∀ z, z ∈ A → P z = true) ∧ (∀ z, z ∈ B → ¬ P z = true) := by
  intro P L
  induction L with
  | nil =>
      rintro A B l1 l2 ⟨h, h1, h2⟩
      simp only [holPart, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨h1, h2⟩
  | cons h t ih =>
      rintro A B l1 l2 ⟨he, h1, h2⟩
      simp only [holPart] at he
      by_cases hp : P h = true
      · rw [if_pos hp] at he
        refine ih A B (h :: l1) l2 ⟨he, ?_, h2⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hp
        · exact h1 x hx
      · rw [if_neg hp] at he
        refine ih A B l1 (h :: l2) ⟨he, h1, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hp
        · exact h2 x hx

end Flapjack
