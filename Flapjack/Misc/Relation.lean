import Flapjack.HolRef

/-!
# HOL relation `transitive`

Exact port of `HOL/src/relation/relationScript.sml` `transitive_def` (21-24),
cited in the pinned upstream HOL submodule. HOL relations `'a -> 'a -> bool`
are rendered as `α → α → Prop`, as for `holSorted`.
-/

namespace Flapjack

/-- Exact HOL `transitive_def` (`relationScript.sml:21-24`):
`transitive R = !x y z. R x y /\ R y z ==> R x z`. -/
@[hol "HOL/src/relation/relationScript.sml" "transitive_def"]
def holTransitive {α : Type} (R : α → α → Prop) : Prop :=
  ∀ x y z, R x y ∧ R y z → R x z

end Flapjack
