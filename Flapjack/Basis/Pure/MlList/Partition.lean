module

public import Flapjack.HolRef

@[expose] public section

/-!
# Cake `mllist$partition`

Lean counterparts of `partition_aux_def`, `partition_def`,
`partition_pos_thm` and `partition_neg_thm` in
`cakeml/basis/pure/mllistScript.sml:413-441`.

The auxiliary function collects the elements satisfying the predicate into
`pos` and the others into `neg`, both reversed, so the two results come back in
source order.  HOL's `FILTER ($~ o f)` is `List.filter` with boolean negation.
-/

namespace Flapjack.Basis.Pure.MlList

/-- Original `partition_aux_def`: accumulate the two classes reversed. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "partition_aux_def"]
def partitionAux {α : Type} (f : α → Bool) : List α → List α → List α → List α × List α
  | [], pos, neg => (pos.reverse, neg.reverse)
  | h :: t, pos, neg =>
      if f h then partitionAux f t (h :: pos) neg else partitionAux f t pos (h :: neg)

/-- Original `partition_def`: split a list by a predicate. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "partition_def"]
def partition {α : Type} (f : α → Bool) (l : List α) : List α × List α :=
  partitionAux f l [] []

private theorem partitionAux_eq {α : Type} (f : α → Bool) (l pos neg : List α) :
    partitionAux f l pos neg =
      (pos.reverse ++ l.filter f, neg.reverse ++ l.filter (fun x => !f x)) := by
  induction l generalizing pos neg with
  | nil => simp [partitionAux]
  | cons h t ih =>
      cases hf : f h with
      | true => simp [partitionAux, hf, ih]
      | false => simp [partitionAux, hf, ih]

/-- Original `partition_pos_thm`: the first component is the filter. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "partition_pos_thm"]
theorem partitionPos {α : Type} (f : α → Bool) (l : List α) :
    (partition f l).1 = l.filter f := by
  simp [partition, partitionAux_eq]

/-- Original `partition_neg_thm`: the second component is the negated filter. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "partition_neg_thm"]
theorem partitionNeg {α : Type} (f : α → Bool) (l : List α) :
    (partition f l).2 = l.filter (fun x => !f x) := by
  simp [partition, partitionAux_eq]

end Flapjack.Basis.Pure.MlList
