module

public import Flapjack.HolRef

@[expose] public section

/-!
# Cake `mllist$collate` and `cpn_to_reln`

Lean counterparts of `collate_def`, `collate_equal_thm`, `collate_short_thm`,
`collate_long_thm` and `cpn_to_reln_def` in
`cakeml/basis/pure/mllistScript.sml:521-565`.

HOL's `ordering` is rendered by Lean `Ordering.lt/eq/gt` constructor for
constructor.  `cpn_to_reln` is boolean-valued, so its HOL boolean equation
`f x1 x2 = LESS` is Lean `==`.  HOL `IS_PREFIX` is `List.IsPrefix` (`<+:`).
`collate_cpn_reln_thm` is not ported: it uses HOL `LLEX`, which has no decided
Lean rendering.  `list_compare_def` is HOL's alias for
`ternaryComparisonsTheory.list_compare_def`, ported here clause for clause.
-/

namespace Flapjack.Basis.Pure.MlList

/-- Original `collate_def`: lexicographic comparison of two lists. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "collate_def"]
def collate {α β : Type} (f : α → β → Ordering) : List α → List β → Ordering
  | [], [] => Ordering.eq
  | [], _ :: _ => Ordering.lt
  | _ :: _, [] => Ordering.gt
  | h1 :: t1, h2 :: t2 =>
      if f h1 h2 = Ordering.eq then collate f t1 t2 else f h1 h2

/-- Original `cpn_to_reln_def`: the comparison is `LESS`. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "cpn_to_reln_def"]
def cpnToRel {α β : Type} (f : α → β → Ordering) (x1 : α) (x2 : β) : Bool :=
  f x1 x2 == Ordering.lt

/-- Original `list_compare_def`, HOL's alias for
`ternaryComparisonsTheory.list_compare_def`: lexicographic comparison of two
lists. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "list_compare_def"]
def listCompare {α β : Type} (cmp : α → β → Ordering) : List α → List β → Ordering
  | [], [] => Ordering.eq
  | [], _ :: _ => Ordering.lt
  | _ :: _, [] => Ordering.gt
  | x :: xs, y :: ys =>
      match cmp x y with
      | Ordering.lt => Ordering.lt
      | Ordering.eq => listCompare cmp xs ys
      | Ordering.gt => Ordering.gt

/-- Original `collate_equal_thm`: two equal lists compare equal. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "collate_equal_thm"]
theorem collateEqual {α : Type} (l : List α) (f : α → α → Ordering)
    (h : ∀ x, x ∈ l → f x x = Ordering.eq) : collate f l l = Ordering.eq := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      simp only [collate]
      rw [if_pos (h x (by simp))]
      exact ih (fun y hy => h y (by simp [hy]))

/-- Original `collate_short_thm`: a proper prefix compares `LESS`. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "collate_short_thm"]
theorem collateShort {α : Type} (f : α → α → Ordering) (l1 l2 : List α)
    (h : (∀ x, f x x = Ordering.eq) ∧ l1 ≠ l2 ∧ l1 <+: l2) :
    collate f l1 l2 = Ordering.lt := by
  obtain ⟨h, hne, hpre⟩ := h
  induction l1 generalizing l2 with
  | nil =>
      cases l2 with
      | nil => exact absurd rfl hne
      | cons y ys => rfl
  | cons x xs ih =>
      obtain ⟨t, ht⟩ := hpre
      cases t with
      | nil =>
          simp only [List.append_nil] at ht
          exact absurd ht hne
      | cons y ys =>
          have hl2 : l2 = x :: (xs ++ y :: ys) := by
            rw [← ht, List.cons_append]
          have hne' : xs ≠ xs ++ y :: ys := by
            intro hc
            refine hne ?_
            rw [hl2]
            rw [← hc]
          have hpre' : xs <+: xs ++ y :: ys := ⟨y :: ys, rfl⟩
          rw [hl2]
          simp only [collate]
          rw [if_pos (h x)]
          exact ih _ hne' hpre'

/-- Original `collate_long_thm`: a proper extension compares `GREATER`. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "collate_long_thm"]
theorem collateLong {α : Type} (f : α → α → Ordering) (l1 l2 : List α)
    (h : (∀ x, f x x = Ordering.eq) ∧ l1 ≠ l2 ∧ l2 <+: l1) :
    collate f l1 l2 = Ordering.gt := by
  obtain ⟨h, hne, hpre⟩ := h
  induction l1 generalizing l2 with
  | nil =>
      have hl2 : l2 = [] := List.prefix_nil.mp hpre
      exact absurd hl2.symm hne
  | cons x xs ih =>
      cases l2 with
      | nil => rfl
      | cons y ys =>
          obtain ⟨t, ht⟩ := hpre
          cases t with
          | nil =>
              simp only [List.append_nil] at ht
              exact absurd ht.symm hne
          | cons z zs =>
              simp only [List.cons_append] at ht
              injection ht with hy hxs
              rw [hy]
              have hne' : xs ≠ ys := by
                intro hc
                refine hne ?_
                rw [hy, hc]
              have hpre' : ys <+: xs := ⟨z :: zs, hxs⟩
              simp only [collate]
              rw [if_pos (h x)]
              exact ih _ hne' hpre'

end Flapjack.Basis.Pure.MlList
