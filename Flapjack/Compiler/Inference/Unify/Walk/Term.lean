module

public import Flapjack.Compiler.Inference.Unify.Walk
public import Flapjack.HOL.Unification.Walkstar

@[expose] public section

namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- Decode the first-order walk. This is not tagged as `t_walk_def`: its
    behavior on ill-formed substitutions inherits the model choice at `vwalk`. -/
noncomputable def tWalk (subst : HolFiniteMapExact Nat InferT) (t : InferT) : InferT :=
  decodeInferT (walk (subst.map2 (fun p => encodeInferT p.2)) (encodeInferT t))

/-- The first independently quantified substitution survives the codec. -/
theorem holFmapAsFiniteSupportParamWitness_tWalkEqn_s1
    (s1 : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1)).lookup key = s1.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1)).finiteSupport = s1.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1) = s1 :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s1 key

/-- The second independently quantified substitution survives the codec. -/
theorem holFmapAsFiniteSupportParamWitness_tWalkEqn_s2
    (s2 : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2)).lookup key = s2.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2)).finiteSupport = s2.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2) = s2 :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s2 key

/-- The third independently quantified substitution survives the codec. -/
theorem holFmapAsFiniteSupportParamWitness_tWalkEqn_s3
    (s3 : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s3)).lookup key = s3.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s3)).finiteSupport = s3.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s3) = s3 :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s3 key

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_walk_eqn"
  (fmap_as_finite_support_parameters := [s1, s2, s3])]
theorem tWalkEqn :
    (∀ (s1 : HolFiniteMapExact Nat InferT) v, tWalk s1 (.uvar v) = tVwalk s1 v) ∧
    (∀ (s2 : HolFiniteMapExact Nat InferT) ts tc, tWalk s2 (.app ts tc) = .app ts tc) ∧
    (∀ (s3 : HolFiniteMapExact Nat InferT) n, tWalk s3 (.varDb n) = .varDb n) := by
  constructor
  · intros
    simp [tWalk, walk, encodeInferT, tVwalk]
  constructor
  · intros
    simp [tWalk, walk, encodeInferT, decodeInferT, decodeLeftInverse]
  · intros
    simp [tWalk, walk, encodeInferT, decodeInferT]

end Flapjack.Compiler.Inference.Unify
