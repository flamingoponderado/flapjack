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

end Flapjack

namespace Flapjack

/-- Original `SPLITP[nocompute]`: split a list at the first element satisfying
`P`. -/
@[hol "HOL/src/list/src/rich_listScript.sml" "SPLITP"]
def splitP {α : Type} (P : α → Bool) : List α → List α × List α
  | [] => ([], [])
  | h :: t =>
    if P h then ([], h :: t)
    else (h :: (splitP P t).1, (splitP P t).2)

/-- Original `SPLITL_def`: split a list at the first element failing `P`. -/
@[hol "HOL/src/list/src/rich_listScript.sml" "SPLITL_def"]
def splitL {α : Type} (P : α → Bool) : List α → List α × List α :=
  splitP (fun x => !(P x))

/-- Original `SPLITP_NIL_FST_IMP`: an empty first component means nothing was
consumed. -/
@[hol "HOL/src/list/src/rich_listScript.sml" "SPLITP_NIL_FST_IMP"]
theorem splitP_nil_fst {α : Type} (P : α → Bool) (ls r : List α) :
    splitP P ls = ([], r) → r = ls := by
  induction ls generalizing r with
  | nil =>
    intro hsplit
    rw [splitP, Prod.mk.injEq] at hsplit
    exact hsplit.2.symm
  | cons h t ih =>
    intro hsplit
    by_cases hp : P h
    · rw [splitP, if_pos hp, Prod.mk.injEq] at hsplit
      exact hsplit.2.symm
    · rw [splitP, if_neg hp, Prod.mk.injEq] at hsplit
      exact absurd hsplit.1 (by simp)

/-- Original `SPLITP_JOIN`: the two components join back to the input. -/
@[hol "HOL/src/list/src/rich_listScript.sml" "SPLITP_JOIN"]
theorem splitP_join {α : Type} (P : α → Bool) (ls l r : List α) :
    splitP P ls = (l, r) → ls = l ++ r := by
  induction ls generalizing l r with
  | nil =>
    intro hsplit
    rw [splitP, Prod.mk.injEq] at hsplit
    rw [← hsplit.1, ← hsplit.2]
    rfl
  | cons h t ih =>
    intro hsplit
    by_cases hp : P h
    · rw [splitP, if_pos hp, Prod.mk.injEq] at hsplit
      rw [← hsplit.1, ← hsplit.2]
      rfl
    · rw [splitP, if_neg hp, Prod.mk.injEq] at hsplit
      have ht : t = (splitP P t).1 ++ (splitP P t).2 := ih _ _ rfl
      rw [← hsplit.1, ← hsplit.2]
      have hcons : h :: t = h :: ((splitP P t).1 ++ (splitP P t).2) :=
        congrArg (List.cons h) ht
      rw [hcons]
      rfl

end Flapjack
