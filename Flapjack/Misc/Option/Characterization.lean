module

public import Flapjack.Misc.Option

@[expose] public section

/-! Equality with HOL's guarded option choice. -/
namespace Flapjack

/-- An option characterized by a predicate equals its guarded choice.
This shared Flapjack helper has no separate HOL declaration. -/
theorem option_eq_holChoice {α : Type} (decoded : Option α) (P : α → Prop)
    (characterization : ∀ x, decoded = some x ↔ P x) : decoded = holOptionSome P := by
  cases choice : holOptionSome P with
  | none =>
    cases result : decoded with
    | none => rfl
    | some value =>
      have valid := (characterization value).mp result
      exact False.elim (holOptionSome_none choice value valid)
  | some value =>
    exact (characterization value).mpr (holOptionSome_some choice)

end Flapjack
