import Flapjack.HolRef

/-!
# Cake `mllist$sort`

Lean counterpart of `sort_def` in `cakeml/basis/pure/mllistScript.sml:287-289`:
`sort = mergesort$mergesort_tail`.

The tail-recursive merge sort `mergesort_tail` comes from the HOL standard
library (`HOL/src/sort/mergesortScript.sml:101-159`), outside `cakeml/`.  Its
helpers are rendered below clause for clause without `@[hol]` tags:
`sort2_tail`, `sort3_tail`, `merge_tail` (HOL `REV l acc` is
`l.reverse ++ acc`), `mergesortN_tail` (HOL `DIV2 n` is `n / 2`) and
`mergesort_tail`.  The HOL relation `R : 'a -> 'a -> bool` is a Lean
`α → α → Bool`.  With a non-strict relation the split-and-negate order
matters, so the recursion is kept literal rather than replaced by another
sort.  `Flapjack.RiscV.CakeRegAlloc.cakeSort` is an earlier untagged
rendering of the same HOL function, used by the executable register
allocator.
-/

namespace Flapjack.Basis.Pure.MlList

/-- HOL `mergesort$sort2_tail` (`mergesortScript.sml:101-107`). -/
def sort2Tail {α : Type} (neg : Bool) (r : α → α → Bool) (x y : α) : List α :=
  if r x y != neg then [x, y] else [y, x]

/-- HOL `mergesort$sort3_tail` (`mergesortScript.sml:109-125`). -/
def sort3Tail {α : Type} (neg : Bool) (r : α → α → Bool) (x y z : α) : List α :=
  if r x y != neg then
    if r y z != neg then [x, y, z]
    else if r x z != neg then [x, z, y]
    else [z, x, y]
  else if r y z != neg then
    if r x z != neg then [y, x, z]
    else [y, z, x]
  else [z, y, x]

/-- HOL `mergesort$merge_tail` (`mergesortScript.sml:127-136`). -/
def mergeTail {α : Type} (negate : Bool) (r : α → α → Bool) :
    List α → List α → List α → List α
  | [], [], acc => acc
  | l, [], acc => l.reverse ++ acc
  | [], l, acc => l.reverse ++ acc
  | x :: l1, y :: l2, acc =>
      if r x y != negate then mergeTail negate r l1 (y :: l2) (x :: acc)
      else mergeTail negate r (x :: l1) l2 (y :: acc)
  termination_by l1 l2 _ => l1.length + l2.length
  decreasing_by all_goals simp +arith

/-- HOL `mergesort$mergesortN_tail` (`mergesortScript.sml:138-155`). -/
def mergesortNTail {α : Type} (negate : Bool) (r : α → α → Bool) : Nat → List α → List α
  | 0, _ => []
  | 1, x :: _ => [x]
  | 1, [] => []
  | 2, x :: y :: _ => sort2Tail negate r x y
  | 2, [x] => [x]
  | 2, [] => []
  | 3, x :: y :: z :: _ => sort3Tail negate r x y z
  | 3, [x, y] => sort2Tail negate r x y
  | 3, [x] => [x]
  | 3, [] => []
  | n + 4, l =>
      let len1 := (n + 4) / 2
      let neg := !negate
      mergeTail neg r (mergesortNTail neg r ((n + 4) / 2) l)
        (mergesortNTail neg r (n + 4 - len1) (l.drop len1)) []
  termination_by n _ => n
  decreasing_by
    all_goals
      have hdiv : (n + 4) / 2 < n + 4 := Nat.div_lt_self (by omega) (by decide)
      omega

/-- HOL `mergesort$mergesort_tail` (`mergesortScript.sml:157-159`):
    `mergesort_tail R l = mergesortN_tail F R (LENGTH l) l`. -/
def mergesortTail {α : Type} (r : α → α → Bool) (l : List α) : List α :=
  mergesortNTail false r l.length l

/-- Exact HOL `mllist$sort_def` (`mllistScript.sml:287-289`):
    `sort = mergesort$mergesort_tail`. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "sort_def"]
def sort {α : Type} (r : α → α → Bool) (l : List α) : List α :=
  mergesortTail r l

end Flapjack.Basis.Pure.MlList
