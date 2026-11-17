module

public import Flapjack.HOL.Unification.Subst
public import Flapjack.FiniteMap.EmptyExact

@[expose] public section

namespace Flapjack.HOL.Unification

@[hol "HOL/examples/algorithms/unification/triangular/first-order/substScript.sml" "wfs_FEMPTY"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem wfsEmpty {α : Type} :
    wfs (Flapjack.HolFiniteMapExact.holEmpty : HolFiniteMapExact Nat (Term α)) := by
  constructor
  intro v
  apply Acc.intro
  intro y edge
  simp [vR, HolFiniteMapExact.holEmpty, HolFiniteMapExact.empty] at edge

end Flapjack.HOL.Unification
