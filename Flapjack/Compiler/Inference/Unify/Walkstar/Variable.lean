module

public import Flapjack.Compiler.Inference.Unify.Walkstar.NoVars

@[expose] public section

namespace Flapjack.Compiler.Inference.Unify

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tWalkstarTuvarProps_s
    (s : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s key

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_walkstar_tuvar_props"
  (fmap_as_finite_support_parameters := [s])]
theorem tWalkstarTuvarProps (s : HolFiniteMapExact Nat InferT) (uv : Nat) (h : tWfs s) :
    uv ∉ s.domain ↔ tWalkstar s (.uvar uv) = .uvar uv := by
  constructor
  · intro absent
    have missing : s.lookup uv = none := by
      change ¬ (s.lookup uv ≠ none) at absent
      exact Classical.not_not.mp absent
    rw [walkstarEqn s h (.uvar uv), tWalkEqn.1 s uv, tVwalkEq s h uv, missing]
  · intro eq
    apply tWalkstarVarsNotin s h (.uvar uv) uv
    rw [eq, tVarsEqn.2.2 uv]
    rfl

end Flapjack.Compiler.Inference.Unify
