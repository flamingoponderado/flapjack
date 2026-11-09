import Mathlib.Data.Nat.Find

/-!
# A shared bound for finite lists of natural numbers

The data, closure and BVL semantics all need a common upper bound for a finite
list of natural numbers (fresh names, reference indices). This is Flapjack proof
infrastructure; there is no separately named HOL original.
-/

namespace Flapjack.Compiler.Backend

/-- Flapjack infrastructure: a finite list of natural numbers has a common
upper bound. No separately named HOL original. -/
theorem natList_bounded (keys : List Nat) : ∃ bound, ∀ key ∈ keys, key < bound := by
  induction keys with
  | nil => exact ⟨0, by simp⟩
  | cons first rest ih =>
    obtain ⟨bound, h⟩ := ih
    refine ⟨max first bound + 1, ?_⟩
    intro key member
    rcases List.mem_cons.mp member with rfl | member
    · omega
    · have := h key member
      omega

end Flapjack.Compiler.Backend
