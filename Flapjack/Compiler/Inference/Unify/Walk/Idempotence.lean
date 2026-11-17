module

public import Flapjack.Compiler.Inference.Unify.Walk.ToVar
public import Flapjack.Compiler.Inference.Unify.Walk.Term

@[expose] public section

/-! Idempotence of inference-type walking. -/
namespace Flapjack.Compiler.Inference.Unify

/-- The source substitution uses the canonical map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tWalkVwalkId_s
    (s : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s key

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_walk_vwalk_id"
  (fmap_as_finite_support_parameters := [s])]
theorem tWalkVwalkId (s : HolFiniteMapExact Nat InferT) (hw : tWfs s) : ∀ n,
    tWalk s (tVwalk s n) = tVwalk s n := by
  intro n
  cases found : tVwalk s n with
  | varDb k => rw [tWalkEqn.2.2]
  | app ts name => rw [tWalkEqn.2.1]
  | uvar v =>
    have absent := tVwalkToVar s hw n v found
    have lookup : s.lookup v = none := by
      change ¬ (s.lookup v ≠ none) at absent
      exact Classical.not_not.mp absent
    rw [tWalkEqn.1, tVwalkEq s hw v, lookup]

/-- The source substitution uses the canonical map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tWalkWalkId_s
    (s : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s key

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_walk_walk_id"
  (fmap_as_finite_support_parameters := [s])]
theorem tWalkWalkId (s : HolFiniteMapExact Nat InferT) (t : InferT) (hw : tWfs s) :
    tWalk s (tWalk s t) = tWalk s t := by
  cases t with
  | varDb k => rw [tWalkEqn.2.2, tWalkEqn.2.2]
  | app ts name => rw [tWalkEqn.2.1, tWalkEqn.2.1]
  | uvar v => rw [tWalkEqn.1]; exact tWalkVwalkId s hw v

end Flapjack.Compiler.Inference.Unify
