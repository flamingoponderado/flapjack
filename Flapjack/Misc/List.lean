module

public import Flapjack.HolRef
public import Batteries.Data.List.Basic

@[expose] public section

/-! List relation results from HOL list. -/
namespace Flapjack

/-- Exact port of HOL `oHD` (`HOL/src/list/src/listScript.sml:5474`): the head
    of a list, if any. -/
@[hol "HOL/src/list/src/listScript.sml" "oHD_def"]
def oHD {α : Type} : List α → Option α
  | [] => none
  | head :: _ => some head

/-- Updating corresponding positions with related values preserves the list relation. -/
@[hol "HOL/src/list/src/listScript.sml" "EVERY2_LUPDATE_same"]
theorem forall₂_set {α β : Type} (relation : α → β → Prop)
    (left : List α) (right : List β) (value : α) (nextValue : β) (index : Nat)
    (premise : relation value nextValue ∧ List.Forall₂ relation left right) :
    List.Forall₂ relation (left.set index value) (right.set index nextValue) := by
  obtain ⟨replacement, related⟩ := premise
  induction related generalizing index with
  | nil => simp
  | cons head tail ih =>
    cases index with
    | zero => simp only [List.set_cons_zero]; exact .cons replacement tail
    | succ n => simp only [List.set_cons_succ]; exact .cons head (ih n)

end Flapjack
