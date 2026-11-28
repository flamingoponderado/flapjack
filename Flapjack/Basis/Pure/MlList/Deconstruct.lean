module

public import Flapjack.HolRef
public import Flapjack.Misc.ListEl

@[expose] public section

/-!
# Cake `mllist` list deconstruction helpers

Lean counterparts of `getItem_def`, `nth_def`, `take_def`, `drop_def`,
`takeUntil_def` and `dropUntil_def` in
`cakeml/basis/pure/mllistScript.sml:337-364`.

`nth l i` is HOL `EL i l`, so it is the total-function rendering `holEl` and
carries the inhabitant instance that renders HOL's unspecified out-of-range
value.  `take` and `drop` are the standard list prefix and suffix operations.
-/

namespace Flapjack.Basis.Pure.MlList

/-- Original `getItem_def`: split a list into its head and tail. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "getItem_def"]
def getItem {α : Type} : List α → Option (α × List α)
  | [] => none
  | h :: t => some (h, t)

/-- Original `nth_def`: list indexing, rendered as the total function `holEl`. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "nth_def"
  (total_function_inhabitants := [α])]
noncomputable def nth {α : Type} [Nonempty α] (l : List α) (i : Nat) : α :=
  holEl i l

/-- Original `take_def`: the first `i` elements. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "take_def"]
def take {α : Type} (l : List α) (i : Nat) : List α :=
  l.take i

/-- Original `drop_def`: the list after the first `i` elements. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "drop_def"]
def drop {α : Type} (l : List α) (i : Nat) : List α :=
  l.drop i

/-- Original `takeUntil_def`: the prefix before the first element satisfying the
predicate. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "takeUntil_def"]
def takeUntil {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => if p x then [] else x :: takeUntil p xs

/-- Original `dropUntil_def`: the list from the first element satisfying the
predicate. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "dropUntil_def"]
def dropUntil {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => if p x then x :: xs else dropUntil p xs

end Flapjack.Basis.Pure.MlList
