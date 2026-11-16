module

public import Flapjack.HOL.Unification.Walkstar.Submap
public import Flapjack.HOL.Unification.Walkstar.Walk

@[expose] public section

/-! Properties of first-order unification. -/
namespace Flapjack.HOL.Unification

/-- The smaller substitution uses the canonical map codec. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarWalkSubmap_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

/-- The larger substitution uses the canonical map codec. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarWalkSubmap_sx {α : Type}
    (sx : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).lookup key = sx.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx)).finiteSupport = sx.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sx) = sx :=
  holFmapAsFiniteSupportParamWitness_vR_subst sx key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/unifPropsScript.sml" "walkstar_walk_SUBMAP"
  (fmap_as_finite_support_parameters := [s, sx])]
theorem walkstarWalkSubmap {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (sx : HolFiniteMapExact Nat (Term α)) (t : Term α)
    (h : s.submap sx ∧ wfs sx) : walkstar sx t = walkstar sx (walk s t) := by
  have hs := wfsSubmap sx s ⟨h.2, h.1⟩
  calc
    walkstar sx t = walkstar sx (walkstar s t) := walkstarSubmap s sx t h
    _ = walkstar sx (walkstar s (walk s t)) := by rw [walkstarWalk s t hs]
    _ = walkstar sx (walk s t) := (walkstarSubmap s sx (walk s t) h).symm

end Flapjack.HOL.Unification
