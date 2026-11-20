module

public import Flapjack.Compiler.Backend.ClosLang.Syntax
public import Flapjack.Misc.ListEl
public import Flapjack.HolRef
public import Mathlib.Data.List.Forall2

@[expose] public section

/-! Generic list, product, sum and integer lemmas stated by the original
`closProps` script. -/
namespace Flapjack.Compiler.Backend.ClosProps

/-- A list is empty exactly when its reverse is empty. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "revnil"]
theorem revnil {α : Type} (l : List α) : ([] : List α) = l.reverse ↔ l = [] := by
  cases l with
  | nil => simp
  | cons x xs => simp

/-- Pointwise list relation with a list itself is the universal reflexive
condition. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "LIST_REL_REFL_EVERY"]
theorem listRel_refl_every {α : Type} (l : List α) (R : α → α → Prop) :
    List.Forall₂ R l l ↔ ∀ x ∈ l, R x x := by
  induction l with
  | nil => simp
  | cons x xs ih => simp

/-- Related lists have related last elements when the source list is nonempty. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "LIST_REL_LAST"
  (total_function_inhabitants := [α, β])]
theorem listRel_last {α β : Type} [Nonempty α] [Nonempty β] (P : α → β → Prop)
    (xs : List α) (ys : List β) :
    List.Forall₂ P xs ys ∧ xs ≠ [] → P (holLast xs) (holLast ys) := by
  induction xs generalizing ys with
  | nil =>
    rintro ⟨_, nonempty⟩
    exact absurd rfl nonempty
  | cons x xs ih =>
    rintro ⟨rel, _⟩
    cases ys with
    | nil => cases rel
    | cons y ys =>
      cases xs with
      | nil =>
        cases rel with
        | cons head tail =>
          cases tail
          simpa [holLast] using head
      | cons x' xs' =>
        cases rel with
        | cons head tail =>
          have ysNonempty : ys ≠ [] := by
            intro empty
            rw [empty] at tail
            cases tail
          have step := ih ys ⟨tail, by simp⟩
          simpa [holLast_cons, ysNonempty] using step

/-- A pair's first component equals a value exactly when the pair extends it. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "FST_EQ_LEMMA"]
theorem fst_eq_lemma {α β : Type} (x : α × β) (y : α) :
    x.1 = y ↔ ∃ y1, x = (y, y1) := by
  cases x with
  | mk first second => simp

/-- A pair-destructuring application equals a value exactly when the pair
splits into arguments producing that value. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "pair_lam_lem"]
theorem pair_lam_lem {α β γ : Type} (f : α → β → γ) (v : γ) (z : α × β) :
    (match z with | (x, y) => f x y) = v ↔ ∃ x1 x2, z = (x1, x2) ∧ f x1 x2 = v := by
  cases z with
  | mk first second => simp

/-- A nonnegative integer is a natural number. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "POS_INT_EQ_NUM"]
theorem pos_int_eq_num (i : Int) : (0 : Int) ≤ i ↔ ∃ n : Nat, i = (n : Int) := by
  constructor
  · intro nonneg
    exact ⟨i.toNat, by omega⟩
  · rintro ⟨n, rfl⟩
    simp

/-- A universal predicate over a sum is the conjunction of its injections. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "forall_sum"]
theorem forall_sum {α β : Type} (P : α ⊕ β → Prop) :
    (∀ x : α ⊕ β, P x) ↔ (∀ a : α, P (.inl a)) ∧ ∀ b : β, P (.inr b) := by
  constructor
  · intro all
    exact ⟨fun a => all (.inl a), fun b => all (.inr b)⟩
  · rintro ⟨left, right⟩ x
    cases x with
    | inl a => exact left a
    | inr b => exact right b

end Flapjack.Compiler.Backend.ClosProps
