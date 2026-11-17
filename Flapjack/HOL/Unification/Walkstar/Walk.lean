module

public import Flapjack.HOL.Unification.Walk.Range

@[expose] public section

namespace Flapjack.HOL.Unification

/-- Canonical map codec roundtrip for normalization after walking. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarWalk_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkstarScript.sml" "walkstar_walk"
  (fmap_as_finite_support_parameters := [s])]
theorem walkstarWalk {α : Type} (s : HolFiniteMapExact Nat (Term α)) (t : Term α)
    (h : wfs s) : walkstar s (walk s t) = walkstar s t := by
  have idem : walk s (walk s t) = walk s t := by
    cases t with
    | var v =>
      change walk s (vwalk s v) = vwalk s v
      cases found : vwalk s v with
      | var u =>
        have absent := vwalkToVar s h v u found
        simpa [walk] using notFdomVwalk s u ⟨h, absent⟩
      | pair l r => rfl
      | const c => rfl
    | pair l r => rfl
    | const c => rfl
  have one := walkstarEq s h t
  have two := walkstarEq s h (walk s t)
  rw [idem] at two
  exact two.trans one.symm

end Flapjack.HOL.Unification
