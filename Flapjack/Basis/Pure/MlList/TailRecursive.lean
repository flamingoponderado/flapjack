module

public import Flapjack.HolRef

@[expose] public section

/-!
# Cake `mllist` tail-recursive list builders

Lean counterparts of `map_rev'`, `map_rev`, `filter_rev'`, `filter_rev`,
`flat_rev'` and `flat_rev` in `cakeml/basis/pure/mllistScript.sml:582-672`,
with the source theorems `map_rev_thm`, `filter_rev_thm` and `flat_rev_thm`.
HOL `REV x acc` is `x.reverse ++ acc`.
-/

namespace Flapjack.Basis.Pure.MlList

/-- Original `map_rev'_def`: tail-recursive map accumulating the result in
reverse order. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "map_rev'_def"]
def mapRev' {α β : Type} (f : α → β) : List α → List β → List β
  | [], acc => acc
  | x :: xs, acc => mapRev' f xs (f x :: acc)

/-- Flapjack infrastructure: the tail-recursive map appends its accumulator. -/
private theorem mapRev'_eq {α β : Type} (f : α → β) (xs : List α) (acc : List β) :
    mapRev' f xs acc = (xs.map f).reverse ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [mapRev']
    rw [ih]
    simp

/-- Original `map_rev_def`: mapping with an empty accumulator. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "map_rev_def"]
def mapRev {α β : Type} (f : α → β) (xs : List α) : List β :=
  mapRev' f xs []

/-- The tail-recursive map is the reversed map of the source list. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "map_rev_thm"]
theorem mapRev_eq_reverse_map {α β : Type} (f : α → β) (xs : List α) :
    mapRev f xs = (xs.map f).reverse := by
  simp [mapRev, mapRev'_eq]

/-- Original `filter_rev'_def`: tail-recursive filter accumulating the kept
elements in reverse order. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "filter_rev'_def"]
def filterRev' {α : Type} (p : α → Bool) : List α → List α → List α
  | [], acc => acc
  | h :: t, acc => if p h then filterRev' p t (h :: acc) else filterRev' p t acc

/-- Flapjack infrastructure: the tail-recursive filter appends its
accumulator. -/
private theorem filterRev'_eq {α : Type} (p : α → Bool) (xs : List α) (acc : List α) :
    filterRev' p xs acc = (xs.filter p).reverse ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons h t ih =>
    simp only [filterRev']
    by_cases keep : p h
    · rw [if_pos keep, List.filter_cons, if_pos keep, ih]
      simp
    · rw [if_neg keep, List.filter_cons, if_neg keep, ih]

/-- Original `filter_rev_def`: filtering with an empty accumulator. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "filter_rev_def"]
def filterRev {α : Type} (p : α → Bool) (xs : List α) : List α :=
  filterRev' p xs []

/-- The tail-recursive filter is the reversed filter of the source list. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "filter_rev_thm"]
theorem filterRev_eq_reverse_filter {α : Type} (p : α → Bool) (xs : List α) :
    filterRev p xs = (xs.filter p).reverse := by
  simp [filterRev, filterRev'_eq]

/-- Original `flat_rev'_def`: tail-recursive flatten accumulating the
concatenation in reverse order. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "flat_rev'_def"]
def flatRev' {α : Type} : List (List α) → List α → List α
  | [], acc => acc
  | x :: xs, acc => flatRev' xs (x.reverse ++ acc)

/-- Flapjack infrastructure: the tail-recursive flatten appends its
accumulator. -/
private theorem flatRev'_eq {α : Type} (xs : List (List α)) (acc : List α) :
    flatRev' xs acc = xs.flatten.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [flatRev']
    rw [ih]
    simp

/-- Original `flat_rev_def`: flattening with an empty accumulator. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "flat_rev_def"]
def flatRev {α : Type} (xs : List (List α)) : List α :=
  flatRev' xs []

/-- The tail-recursive flatten is the reversed flatten of the source list. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "flat_rev_thm"]
theorem flatRev_eq_reverse_flatten {α : Type} (xs : List (List α)) :
    flatRev xs = xs.flatten.reverse := by
  simp [flatRev, flatRev'_eq]

end Flapjack.Basis.Pure.MlList
