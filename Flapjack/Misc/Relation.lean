import Flapjack.HolRef

/-!
# HOL relations `transitive` and `total`

Exact ports of `HOL/src/relation/relationScript.sml` `transitive_def` (21-24)
and `total_def` (56-58),
cited in the pinned upstream HOL submodule. HOL relations `'a -> 'a -> bool`
are rendered as `α → α → Prop`, as for `holSorted`.
-/

namespace Flapjack

/-- Exact HOL `transitive_def` (`relationScript.sml:21-24`):
`transitive R = !x y z. R x y /\ R y z ==> R x z`. -/
@[hol "HOL/src/relation/relationScript.sml" "transitive_def"]
def holTransitive {α : Type} (R : α → α → Prop) : Prop :=
  ∀ x y z, R x y ∧ R y z → R x z

/-- Exact HOL `total_def` (`relationScript.sml:56-58`):
`total R = !x y. R x y \/ R y x`. -/
@[hol "HOL/src/relation/relationScript.sml" "total_def"]
def holTotal {α : Type} (R : α → α → Prop) : Prop :=
  ∀ x y, R x y ∨ R y x

end Flapjack
