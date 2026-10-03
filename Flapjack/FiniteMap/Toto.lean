import Flapjack.HolRef

namespace Flapjack.FiniteMap.Toto

/-- Original total-order comparison predicate: equality agrees exactly with
key equality, greater/less comparisons reverse, and less is transitive. -/
@[hol "HOL/src/finite_maps/totoScript.sml" "TotOrd"]
def totOrd {α : Type} (comparison : α → α → Ordering) : Prop :=
  (∀ x y, comparison x y = .eq ↔ x = y) ∧
  (∀ x y, comparison x y = .gt ↔ comparison y x = .lt) ∧
  (∀ x y z, comparison x y = .lt ∧ comparison y z = .lt → comparison x z = .lt)

end Flapjack.FiniteMap.Toto
