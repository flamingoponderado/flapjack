module

public import Flapjack.Compiler.Backend.BackendProps

@[expose] public section

/-! Ordering and addition of optional natural-number bounds. -/
namespace Flapjack.Compiler.Backend.BackendProps

/-- Zero is below every optional bound. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "option_le_SOME_0"]
theorem optionLe_some_zero : ∀ x, optionLe (some 0) x := by
  intro x
  cases x <;> simp [optionLe]

/-- Optional addition is commutative. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "option_add_comm"]
theorem optionAdd_comm (n m : Option Nat) :
    Option.map₂ (· + ·) n m = Option.map₂ (· + ·) m n := by
  cases n <;> cases m <;> simp [Nat.add_comm]

/-- Optional addition is associative. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "option_add_assoc"]
theorem optionAdd_assoc (n m p : Option Nat) :
    Option.map₂ (· + ·) n (Option.map₂ (· + ·) m p) =
      Option.map₂ (· + ·) (Option.map₂ (· + ·) n m) p := by
  cases n <;> cases m <;> cases p <;> simp [Nat.add_assoc]

/-- Adding an optional bound cannot decrease it. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "option_le_add"]
theorem optionLe_add (n m : Option Nat) : optionLe n (Option.map₂ (· + ·) n m) := by
  cases n <;> cases m <;> simp [optionLe]

end Flapjack.Compiler.Backend.BackendProps
