module

public import Flapjack.Misc.Relation

@[expose] public section

/-!
# HOL `irreflexive` and its inverse-image stability

Counterparts of `HOL/src/relation/relationScript.sml`'s `irreflexive_def` and
`cakeml/misc/miscScript.sml`'s `irreflexive_inv_image`. As for `holTransitive`
and `holTotal` in `Flapjack/Misc/Relation.lean`, the HOL relation
`'a -> 'a -> bool` is rendered as `α → α → Prop`, and HOL's `inv_image R f`
(`λx y. R (f x) (f y)`) is Mathlib's `InvImage R f`.
-/

namespace Flapjack

/-- Exact HOL `irreflexive_def` (`relationScript.sml:31-33`):
`irreflexive R = !x. ~R x x`. -/
@[hol "HOL/src/relation/relationScript.sml" "irreflexive_def"]
def holIrreflexive {α : Type} (R : α → α → Prop) : Prop := ∀ x, ¬ R x x

/-- Original `irreflexive_inv_image`: an irreflexive relation stays
irreflexive after pulling it back along any function. -/
@[hol "cakeml/misc/miscScript.sml" "irreflexive_inv_image"]
theorem holIrreflexive_invImage {α β : Type} (R : α → α → Prop) (f : β → α) :
    holIrreflexive R → holIrreflexive (InvImage R f) := by
  intro h x
  exact h (f x)

end Flapjack
