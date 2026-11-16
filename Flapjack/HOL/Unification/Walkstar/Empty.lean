module

public import Flapjack.HOL.Unification.Walkstar
public import Flapjack.HOL.Unification.Subst.Empty

@[expose] public section

namespace Flapjack.HOL.Unification

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkstarScript.sml" "walkstar_FEMPTY"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem walkstarEmpty {α : Type} : ∀ t : Term α,
    walkstar Flapjack.HolFiniteMapExact.holEmpty t = t := by
  intro t
  induction t with
  | var v =>
    rw [walkstarEq _ wfsEmpty]
    simp only [walk]
    rw [vwalkEq _ wfsEmpty v]
    simp [HolFiniteMapExact.holEmpty, HolFiniteMapExact.empty]
  | pair a b iha ihb =>
    rw [walkstarEq _ wfsEmpty]
    simp [walk, iha, ihb]
  | const c =>
    rw [walkstarEq _ wfsEmpty]
    rfl

end Flapjack.HOL.Unification
