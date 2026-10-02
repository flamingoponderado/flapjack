import Flapjack.HolRef

namespace Flapjack.FiniteMap.Comparison

/-- Literal HOL comparator predicate. Equal may identify distinct keys; no
antisymmetry of key equality or total-order typeclass is imposed. The seven
universally quantified clauses retain their original order and directions. -/
@[hol "HOL/src/finite_maps/comparisonScript.sml" "good_cmp_def"]
def goodCmp {κ : Type} (cmp : κ → κ → Ordering) : Prop :=
  (∀ x, cmp x x = .eq) ∧
  (∀ x y, cmp x y = .eq → cmp y x = .eq) ∧
  (∀ x y, cmp x y = .gt ↔ cmp y x = .lt) ∧
  (∀ x y z, cmp x y = .eq ∧ cmp y z = .lt → cmp x z = .lt) ∧
  (∀ x y z, cmp x y = .lt ∧ cmp y z = .eq → cmp x z = .lt) ∧
  (∀ x y z, cmp x y = .eq ∧ cmp y z = .eq → cmp x z = .eq) ∧
  (∀ x y z, cmp x y = .lt ∧ cmp y z = .lt → cmp x z = .lt)

end Flapjack.FiniteMap.Comparison
