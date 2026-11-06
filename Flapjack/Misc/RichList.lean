import Flapjack.HolRef
import Batteries.Data.List.Basic

/-! List-relation results from HOL rich_list. -/
namespace Flapjack

/-- Replicated lists are pointwise related exactly when a nonzero length
requires the repeated values to be related. -/
@[hol "HOL/src/list/src/rich_listScript.sml" "LIST_REL_REPLICATE_same"]
theorem forall₂_replicate_iff {α β : Type} (relation : α → β → Prop)
    (n : Nat) (x : α) (y : β) :
    List.Forall₂ relation (List.replicate n x) (List.replicate n y) ↔
      (0 < n → relation x y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    constructor
    · intro related _
      cases related with
      | cons head _ => exact head
    · intro related
      have head := related (Nat.zero_lt_succ n)
      exact .cons head (ih.mpr (fun _ => head))

end Flapjack
