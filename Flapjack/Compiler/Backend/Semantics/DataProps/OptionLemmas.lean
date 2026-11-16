module

public import Flapjack.Compiler.Backend.Semantics.DataProps.ResourceCall

@[expose] public section

/-! `dataPropsScript.sml` option lemmas about HOL's `OPTION_MAP2`, rendered as
`Option.map₂`. -/

namespace Flapjack

/-- Exact HOL `OPTION_MAP2_ADD_SOME_0` (`dataPropsScript.sml:87`): adding a
    `SOME 0` leaves the other operand alone. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "OPTION_MAP2_ADD_SOME_0"]
theorem optionMap2_add_some_0 (x : Option Nat) :
    Option.map₂ (· + ·) x (some 0) = x := by
  rcases x with _ | _
  all_goals rfl

/-- Exact HOL `OPTION_MAP2_MAX_CANCEL` (`dataPropsScript.sml:93`). -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "OPTION_MAP2_MAX_CANCEL"]
theorem optionMap2_max_cancel (x y : Option Nat) :
    Option.map₂ max (Option.map₂ max x y) y = Option.map₂ max x y := by
  rcases x with _ | _
  all_goals rcases y with _ | _
  all_goals simp

/-- Exact HOL `OPTION_MAP2_NONE` (`dataPropsScript.sml:101`): either `NONE`
    makes the mapped result `NONE`. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "OPTION_MAP2_NONE"]
theorem optionMap2_none {α β γ : Type} (f : α → β → γ) (x : Option α) (y : Option β) :
    Option.map₂ f none y = none ∧ Option.map₂ f x none = none := by
  rcases y with _ | _
  all_goals rcases x with _ | _
  all_goals simp

/-- HOL's `OPTION_CASE` applied to an `OPTION_MAP` fuses the mapping into the
`SOME` branch; HOL writes `option_CASE` and Lean's `Option.elim` takes the same
three arguments in the same order. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "OPTION_CASE_OPTION_MAP"]
theorem optionElim_optionMap {α β γ : Type} (f : α → β) (a : Option α) (e : γ)
    (g : β → γ) : Option.elim (Option.map f a) e g = Option.elim a e (g ∘ f) := by
  cases a <;> rfl

end Flapjack
