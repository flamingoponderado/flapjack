module

public import Flapjack.Compiler.Backend.BackendProps
public import Flapjack.Misc.MiscThe

@[expose] public section

/-! Ordering and addition of optional natural-number bounds. -/
namespace Flapjack.Compiler.Backend.BackendProps

/-- Exact HOL `the_eqn` (`backendPropsScript.sml:49`): the default for `NONE`,
    the payload for `SOME`. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "the_eqn"]
theorem miscThe_eq {α : Type} (x : α) (y : Option α) :
    Flapjack.miscThe x y = match y with | none => x | some z => z := by
  cases y <;> rfl

/-- Exact HOL `the_F_eq` (`backendPropsScript.sml:55`): `the F opt` holds
    exactly when `opt` is a `SOME` carrying a true value.  HOL's boolean
    equality of the two sides is rendered as an iff, and HOL's `∧ x` over a
    `bool` is `∧ x = true`. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "the_F_eq"]
theorem miscThe_false (opt : Option Bool) :
    Flapjack.miscThe false opt = true ↔ ∃ x : Bool, opt = some x ∧ x = true := by
  cases opt with
  | none => simp [Flapjack.miscThe]
  | some value => cases value <;> simp [Flapjack.miscThe]

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
