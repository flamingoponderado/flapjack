module

public import Flapjack.Compiler.Inference.Unify.Walkstar.Submap

@[expose] public section

namespace Flapjack.Compiler.Inference.Unify

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tWalkstarIdempotent_s
    (s : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s key

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_walkstar_idempotent"
  (fmap_as_finite_support_parameters := [s])]
theorem tWalkstarIdempotent (s : HolFiniteMapExact Nat InferT) (hw : tWfs s) : ∀ t,
    tWalkstar s (tWalkstar s t) = tWalkstar s t := by
  intro t
  exact (tWalkstarSubmap s s t ⟨HolFiniteMapExact.submap_refl s, hw⟩).symm

end Flapjack.Compiler.Inference.Unify
