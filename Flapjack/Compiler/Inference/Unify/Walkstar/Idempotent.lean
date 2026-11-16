module

public import Flapjack.Compiler.Inference.Unify.Walkstar.Variable

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
  apply tWalkstarInd s hw
  intro t ih
  have orig := walkstarEqn s hw t
  cases heq : tWalk s t with
  | varDb n =>
    simp only [heq] at orig
    rw [orig, walkstarEqn s hw (.varDb n), tWalkEqn.2.2 s n]
  | uvar u =>
    simp only [heq] at orig
    have absent : u ∉ s.domain := by
      apply tWalkstarVarsNotin s hw t u
      rw [orig, tVarsEqn.2.2 u]
      rfl
    rw [orig]
    exact (tWalkstarTuvarProps s u hw).mp absent
  | app ts tc =>
    simp only [heq] at orig
    rw [orig, walkstarEqn s hw (.app (ts.map (tWalkstar s)) tc),
      tWalkEqn.2.1 s (ts.map (tWalkstar s)) tc]
    apply congrArg (InferT.app · tc)
    simp only [List.map_map]
    apply List.map_congr_left
    intro a ha
    exact ih ts tc a ⟨heq, ha⟩

end Flapjack.Compiler.Inference.Unify
