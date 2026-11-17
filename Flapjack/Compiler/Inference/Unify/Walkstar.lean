module

public import Flapjack.Compiler.Inference.Unify.Walk.Term

@[expose] public section

/-! Inference-type normalization through the first-order encoding. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- Decode first-order normalization. This is not tagged as `t_walkstar_def`:
    for ill-formed substitutions the first-order model makes a choice not
    constrained by HOL's conditional equation. -/
noncomputable def tWalkstar (s : HolFiniteMapExact Nat InferT) (t : InferT) : InferT :=
  decodeInferT (walkstar (s.map2 (fun p => encodeInferT p.2)) (encodeInferT t))

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_listWalkstar_s
    (s : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s key

@[hol "cakeml/compiler/inference/unifyScript.sml" "ts_walkstar_thm"
  (fmap_as_finite_support_parameters := [s])]
theorem listWalkstar : ∀ ts (s : HolFiniteMapExact Nat InferT), tWfs s →
    decodeInferTs (walkstar (s.map2 (fun p => encodeInferT p.2)) (encodeInferTs ts)) =
      ts.map (tWalkstar s) := by
  intro ts
  induction ts with
  | nil =>
    intro s h
    rw [walkstarEq _ h]
    simp [encodeInferTs, walk, decodeInferTs]
  | cons t ts ih =>
    intro s h
    rw [walkstarEq _ h]
    simp [encodeInferTs, walk, decodeInferTs, tWalkstar, ih s h]

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarEqn_s
    (s : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s key

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_walkstar_eqn"
  (fmap_as_finite_support_parameters := [s])]
theorem walkstarEqn (s : HolFiniteMapExact Nat InferT) (h : tWfs s) : ∀ t,
    tWalkstar s t = match tWalk s t with
      | .uvar v => .uvar v
      | .app ts tc => .app (ts.map (tWalkstar s)) tc
      | .varDb n => .varDb n := by
  intro t
  unfold tWalkstar
  rw [walkstarEq _ h, encodeWalk s h t]
  cases found : tWalk s t with
  | uvar v => simp [encodeInferT, decodeInferT]
  | varDb n => simp [encodeInferT, decodeInferT]
  | app ts tc =>
    simp only [encodeInferT]
    rw [walkstarEq _ h]
    simp only [walk]
    rw [walkstarEq _ h]
    simp only [walk]
    rw [walkstarEq _ h]
    simp [walk, decodeInferT, listWalkstar ts s h, tWalkstar]

/-- The substitution parameter survives the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tWalkstarEqn1_s
    (s : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s key

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_walkstar_eqn1"
  (fmap_as_finite_support_parameters := [s])]
theorem tWalkstarEqn1 (s : HolFiniteMapExact Nat InferT) (idx : Nat)
    (ts : List InferT) (tc : Nat) (h : tWfs s) :
    tWalkstar s (.varDb idx) = .varDb idx ∧
      tWalkstar s (.app ts tc) = .app (ts.map (tWalkstar s)) tc := by
  constructor
  · simpa [tWalkEqn.2.2] using walkstarEqn s h (.varDb idx)
  · simpa [tWalkEqn.2.1] using walkstarEqn s h (.app ts tc)

end Flapjack.Compiler.Inference.Unify

