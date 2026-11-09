module

public import Flapjack.Misc.Option.Rel
public import Batteries.Data.List.Basic

@[expose] public section

/-! Indexed lookup for pointwise-related lists. -/
namespace Flapjack

/-- Pointwise related lists have related indexed lookups, including absence.
This is shared Flapjack infrastructure, with no separate HOL declaration. -/
theorem forall₂_lookupRel {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (related : List.Forall₂ R xs ys) (n : Nat) : optionRel R xs[n]? ys[n]? := by
  induction related generalizing n with
  | nil => simp [optionRel]
  | cons head tail ih =>
    cases n with
    | zero => simpa [optionRel] using head
    | succ n => simpa using ih n

/-- A successful indexed lookup has a related result at the same index.
This is shared Flapjack infrastructure, with no separate HOL declaration. -/
theorem forall₂_lookup {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (related : List.Forall₂ R xs ys) (n : Nat) (x : α) (lookup : xs[n]? = some x) :
    ∃ y, ys[n]? = some y ∧ R x y := by
  have rel := forall₂_lookupRel related n
  rw [lookup] at rel
  cases found : ys[n]? with
  | none => simp [found, optionRel] at rel
  | some y => exact ⟨y, rfl, by simpa [found, optionRel] using rel⟩

end Flapjack
