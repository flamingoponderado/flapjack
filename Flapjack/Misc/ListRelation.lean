module

public import Flapjack.Misc.List
public import Mathlib.Data.List.Forall2

@[expose] public section

/-!
# List relation results over HOL's generated index lists

Counterparts of the `LIST_REL`/`GENLIST` facts from
`cakeml/misc/miscScript.sml`. The `Mathlib.Data.List.Forall2` import lives here
rather than in `Flapjack.Misc.List`: adding it to that widely imported module
changes the global simp set for `List.Forall₂` and breaks unrelated proofs.
-/

namespace Flapjack

/-- Original `LIST_REL_GENLIST_I`: relating the generated index list to a list
is the same as relating every index with the list element there. -/
@[hol "cakeml/misc/miscScript.sml" "LIST_REL_GENLIST_I"
  (total_function_inhabitants := [α])]
theorem listRelGenlistI {α : Type} [Nonempty α] (P : Nat → α → Prop) (xs : List α) :
    List.Forall₂ P (List.range xs.length) xs ↔ ∀ n, n < xs.length → P n (holEl n xs) := by
  rw [List.forall₂_iff_get]
  constructor
  · rintro ⟨hlen, hall⟩ n hn
    rw [holEl_eq_getElem n xs hn]
    have h := hall n (by simpa using hn) hn
    rw [List.get_eq_getElem, List.getElem_range] at h
    exact h
  · intro hall
    refine ⟨by simp, ?_⟩
    intro i h1 h2
    have h := hall i h2
    rw [holEl_eq_getElem i xs h2] at h
    simpa only [List.get_eq_getElem, List.getElem_range] using h

/-- Flapjack infrastructure: on a nonempty list HOL's total `LAST` is the
last element. -/
private theorem holLast_eq_getLast {α : Type} [Nonempty α] {l : List α} (h : l ≠ []) :
    holLast l = l.getLast h := by
  induction l with
  | nil => exact absurd rfl h
  | cons x xs ih =>
    cases xs with
    | nil => simp [holLast, List.getLast]
    | cons y ys =>
      simp only [holLast]
      exact ih (by simp)

/-- Flapjack infrastructure: relation on lists appended with one element. -/
private theorem forall₂_append_singleton {α β : Type} (A : α → β → Prop) :
    ∀ (l1 : List α) (l2 : List β) (x : α) (y : β),
      List.Forall₂ A (l1 ++ [x]) (l2 ++ [y]) ↔ List.Forall₂ A l1 l2 ∧ A x y
  | [], [], _, _ => by simp
  | [], _ :: _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | a :: l1, b :: l2, x, y => by
      simp only [List.cons_append, List.forall₂_cons]
      rw [forall₂_append_singleton A l1 l2 x y]
      simp only [and_assoc]

/-- Original `LIST_REL_FRONT_LAST`: two nonempty lists are related exactly when
their fronts are related and their last elements are related. -/
@[hol "cakeml/misc/miscScript.sml" "LIST_REL_FRONT_LAST"
  (total_function_inhabitants := [α, β])]
theorem listRelFrontLast {α β : Type} [Nonempty α] [Nonempty β] (A : α → β → Prop)
    (l1 : List α) (l2 : List β) (h1 : l1 ≠ []) (h2 : l2 ≠ []) :
    List.Forall₂ A l1 l2 ↔
      List.Forall₂ A l1.dropLast l2.dropLast ∧ A (holLast l1) (holLast l2) := by
  conv_lhs => rw [← List.dropLast_append_getLast h1, ← List.dropLast_append_getLast h2]
  rw [forall₂_append_singleton, holLast_eq_getLast h1, holLast_eq_getLast h2]

/-- Original `LIST_REL_IMP_LAST`: related lists have related last elements. -/
@[hol "cakeml/misc/miscScript.sml" "LIST_REL_IMP_LAST"
  (total_function_inhabitants := [α, β])]
theorem listRelImpLast {α β : Type} [Nonempty α] [Nonempty β] (P : α → β → Prop)
    (xs : List α) (ys : List β) :
    List.Forall₂ P xs ys → (xs ≠ [] ∨ ys ≠ []) → P (holLast xs) (holLast ys) := by
  intro hrel hne
  rcases hne with hx | hy
  · have hy : ys ≠ [] := by
      intro h
      subst h
      cases hrel
      exact absurd rfl hx
    exact ((listRelFrontLast P xs ys hx hy).mp hrel).2
  · have hx : xs ≠ [] := by
      intro h
      subst h
      cases hrel
      exact absurd rfl hy
    exact ((listRelFrontLast P xs ys hx hy).mp hrel).2

end Flapjack
