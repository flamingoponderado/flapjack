module

public import Flapjack.HolRef
public import Batteries.Data.List.Basic

@[expose] public section

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

/-- The last `n` elements of a list. -/
@[hol "HOL/src/list/src/rich_listScript.sml" "LASTN_def"]
def holLastn {α : Type} (n : Nat) (xs : List α) : List α :=
  (xs.reverse.take n).reverse

/-- A list without its last `n` elements. -/
@[hol "HOL/src/list/src/rich_listScript.sml" "BUTLASTN_def"]
def holButlastn {α : Type} (n : Nat) (xs : List α) : List α :=
  (xs.reverse.drop n).reverse

/-- Splitting off the last `n` elements and appending them back is the
identity (Flapjack proof infrastructure). -/
theorem holButlastn_append_holLastn {α : Type} (n : Nat) (xs : List α) :
    holButlastn n xs ++ holLastn n xs = xs := by
  rw [holButlastn, holLastn, ← List.reverse_append, List.take_append_drop, List.reverse_reverse]

end Flapjack
