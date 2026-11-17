module

public import Flapjack.Compiler.Inference.Unify.Walkstar.Induction
public import Flapjack.Compiler.Inference.Unify.Walk.ToVar

@[expose] public section

namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tWalkstarVarsNotin_s
    (s : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s key

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_walkstar_vars_notin"
  (fmap_as_finite_support_parameters := [s])]
theorem tWalkstarVarsNotin (s : HolFiniteMapExact Nat InferT) (hw : tWfs s) :
    ∀ t x, tVars (tWalkstar s t) x → x ∉ s.domain := by
  apply tWalkstarInd s hw
  intro t ih x hv
  rw [walkstarEqn s hw t] at hv
  cases heq : tWalk s t with
  | varDb n =>
    simp only [heq] at hv
    rw [tVarsEqn.1 n] at hv
    exact hv.elim
  | uvar u =>
    simp only [heq] at hv
    rw [tVarsEqn.2.2 u] at hv
    have xu : x = u := hv
    subst x
    cases t with
    | varDb n =>
      rw [tWalkEqn.2.2 s n] at heq
      cases heq
    | app ts tc =>
      rw [tWalkEqn.2.1 s ts tc] at heq
      cases heq
    | uvar v =>
      rw [tWalkEqn.1 s v] at heq
      exact tVwalkToVar s hw v u heq
  | app ts tc =>
    simp only [heq] at hv
    rw [tVarsEqn.2.1 (ts.map (tWalkstar s)) tc] at hv
    change ∃ p : Nat → Prop,
      (∃ z, z ∈ ts.map (tWalkstar s) ∧ tVars z = p) ∧ p x at hv
    obtain ⟨_, ⟨z, hz, rfl⟩, hx⟩ := hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    exact ih ts tc a ⟨heq, ha⟩ x hx

end Flapjack.Compiler.Inference.Unify
