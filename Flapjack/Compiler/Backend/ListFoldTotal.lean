module

@[expose] public section

/-!
# Shared total-fold facts for the backend passes

The recursion-detection folds of the inlining, handler and tail-recursion
passes all need the same fact: a `foldlM` whose step succeeds at every element
terminates successfully. This is Flapjack proof infrastructure; there is no
separately named HOL original.
-/

namespace Flapjack.Compiler.Backend

/-- Flapjack infrastructure: the recursion-detection fold succeeds whenever
every element has a successful step. No separately named HOL original. -/
theorem foldRec_succeeds {α : Type} (xs : List α) (f : α → Option Bool)
    (init : Bool) (h : ∀ x ∈ xs, ∃ result, f x = some result) :
    ∃ result, xs.foldlM (fun found x => if found then pure true else f x) init = some result := by
  induction xs generalizing init with
  | nil => exact ⟨init, rfl⟩
  | cons x xs ih =>
    cases init with
    | true =>
      obtain ⟨result, hr⟩ := ih true (by intro y hy; exact h y (by simp [hy]))
      exact ⟨result, by simpa using hr⟩
    | false =>
      obtain ⟨value, hv⟩ := h x (by simp)
      obtain ⟨result, hr⟩ := ih value (by intro y hy; exact h y (by simp [hy]))
      exact ⟨result, by simpa [hv] using hr⟩

end Flapjack.Compiler.Backend
