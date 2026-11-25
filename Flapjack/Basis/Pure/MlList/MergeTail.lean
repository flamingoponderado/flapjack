module

public import Flapjack.HolRef
public import Flapjack.Misc.Mergesort
public import Flapjack.Basis.Pure.MlList.SortPerm

@[expose] public section

/-!
# `mllist` tail-recursive mergesort: membership, accumulator and correctness

Ports of `cakeml/basis/pure/mllistScript.sml:18-102` and `:140-285`: the
membership, accumulator and correctness theorems for the tail-recursive
mergesort helpers `merge_tail`, `sort2_tail`, `sort3_tail` and
`mergesortN_tail` rendered in `Flapjack.Basis.Pure.MlList`. The helpers
themselves are HOL standard library (`HOL/src/sort/mergesortScript.sml`) and
stay untagged; the non-tail `sort2`, `sort3` and `merge` come from
`Flapjack.Mergesort`. HOL `TAKE` is `List.take` and `MEM` is list membership.
The permutation theorems (`merge_tail_PERM`, `sort2_tail_PERM`,
`sort3_tail_PERM`, `mergesortN_tail_PERM`) are tagged in
`Flapjack.Basis.Pure.MlList.SortPerm`, so the membership facts below follow
from them.
-/

namespace Flapjack.Basis.Pure.MlList

open Flapjack.Mergesort

/-- Exact HOL `sort2_tail_sort2` (`mllistScript.sml:70-77`). -/
@[hol "cakeml/basis/pure/mllistScript.sml" "sort2_tail_sort2"]
theorem sort2TailSort2 {α : Type} :
    ∀ (negate : Bool) (r : α → α → Bool) (x y : α),
      sort2Tail negate r x y = if negate then (sort2 r x y).reverse else sort2 r x y :=
  Mergesort.sort2TailCorrect

/-- Exact HOL `sort3_tail_sort3` (`mllistScript.sml:61-68`). -/
@[hol "cakeml/basis/pure/mllistScript.sml" "sort3_tail_sort3"]
theorem sort3TailSort3 {α : Type} :
    ∀ (negate : Bool) (r : α → α → Bool) (x y z : α),
      sort3Tail negate r x y z = if negate then (sort3 r x y z).reverse else sort3 r x y z :=
  Mergesort.sort3TailCorrect

/-- HOL's `merge_tail` with `negate = true` is the same recursion as with
`negate = false` over the complemented relation. -/
private theorem mergeTailTrueEq {α : Type} (r : α → α → Bool) (l1 l2 acc : List α) :
    mergeTail true r l1 l2 acc = mergeTail false (fun x y => !(r x y)) l1 l2 acc := by
  fun_induction mergeTail true r l1 l2 acc with
  | case1 acc => simp [mergeTail]
  | case2 l acc _ => simp [mergeTail]
  | case3 l acc _ => simp [mergeTail]
  | case4 x l1 y l2 acc hxy ih =>
      simp only [mergeTail] at hxy ih ⊢
      cases h : r x y
      · simp_all
      · simp_all
  | case5 x l1 y l2 acc hxy ih =>
      simp only [mergeTail] at hxy ih ⊢
      cases h : r x y
      · simp_all
      · simp_all

/-- Exact HOL `mergetail_merge` (`mllistScript.sml:79-88`). -/
@[hol "cakeml/basis/pure/mllistScript.sml" "mergetail_merge"]
theorem mergeTailMerge {α : Type} :
    ∀ (negate : Bool) (r : α → α → Bool) (xs ys acc : List α),
      mergeTail negate r xs ys acc =
        if negate then (merge (fun x y => !(r x y)) xs ys).reverse ++ acc
        else (merge r xs ys).reverse ++ acc := by
  intro negate r xs ys acc
  cases negate with
  | false => exact Mergesort.mergeTailCorrect1 false r xs ys acc rfl
  | true =>
      rw [mergeTailTrueEq]
      exact Mergesort.mergeTailCorrect1 false (fun x y => !(r x y)) xs ys acc rfl

/-- Exact HOL `merge_tail_acc` (`mllistScript.sml:90-96`). -/
@[hol "cakeml/basis/pure/mllistScript.sml" "merge_tail_acc"]
theorem mergeTailAcc {α : Type} :
    ∀ (negate : Bool) (r : α → α → Bool) (xs ys acc acc' : List α),
      mergeTail negate r xs ys (acc ++ acc') = mergeTail negate r xs ys acc ++ acc' := by
  intro negate r xs ys acc acc'
  cases negate with
  | false =>
      rw [mergeTailMerge, mergeTailMerge]
      simp [List.append_assoc]
  | true =>
      rw [mergeTailMerge, mergeTailMerge]
      simp [List.append_assoc]

/-- Exact HOL `merge_tail_MEM` (`mllistScript.sml:18-31`); `x` is free in HOL. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "merge_tail_MEM"]
theorem mergeTailMem {α : Type} (x : α) :
    ∀ (negate : Bool) (r : α → α → Bool) (xs ys acc : List α),
      x ∈ mergeTail negate r xs ys acc ↔ x ∈ xs ∨ x ∈ ys ∨ x ∈ acc := by
  intro negate r xs ys acc
  have h : x ∈ (xs ++ ys ++ acc) ↔ x ∈ mergeTail negate r xs ys acc :=
    List.Perm.mem_iff ((holPerm_iff _ _).mp (mergeTailPerm negate r xs ys acc))
  simp only [List.mem_append] at h
  rw [← or_assoc]
  exact h.symm

/-- Exact HOL `mergesortN_tail_MEM` (`mllistScript.sml:33-59`); `x` is free in HOL. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "mergesortN_tail_MEM"]
theorem mergesortNTailMem {α : Type} (x : α) :
    ∀ (negate : Bool) (r : α → α → Bool) (length : Nat) (lst : List α),
      x ∈ mergesortNTail negate r length lst ↔ x ∈ lst.take length := by
  intro negate r length lst
  exact (List.Perm.mem_iff
    ((holPerm_iff _ _).mp (mergesortNTailPerm negate r length lst))).symm

/-- Exact HOL `mergesort_tail_MEM` (`mllistScript.sml:98-102`); `x` is free in HOL. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "mergesort_tail_MEM"]
theorem mergesortTailMem {α : Type} (x : α) :
    ∀ (r : α → α → Bool) (l : List α), x ∈ mergesortTail r l ↔ x ∈ l := by
  intro r l
  rw [mergesortTail, mergesortNTailMem, List.take_length]

end Flapjack.Basis.Pure.MlList
