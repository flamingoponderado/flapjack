module

public import Flapjack.Compiler.Inference.Unify.Substitution
public import Flapjack.HOL.Unification.Walk

@[expose] public section

/-! Inference-type variable walking through the first-order encoding. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- Decode the first-order walker. This is not tagged as `t_vwalk_def` because
    its behavior when the substitution is not well formed inherits the model
    choice documented at `vwalk`; no HOL correspondence is claimed there. -/
noncomputable def tVwalk (subst : HolFiniteMapExact Nat InferT) (v : Nat) : InferT :=
  decodeInferT (vwalk (subst.map2 (fun p => encodeInferT p.2)) v)

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tVwalkEq_subst
    (subst : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).lookup key = subst.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).finiteSupport = subst.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst) = subst :=
  holFmapAsFiniteSupportParamWitness_tVR_subst subst key

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_vwalk_eqn"
  (fmap_as_finite_support_parameters := [subst])]
theorem tVwalkEq (subst : HolFiniteMapExact Nat InferT) (h : tWfs subst) : ∀ v,
    tVwalk subst v = match subst.lookup v with
      | none => .uvar v
      | some (.uvar u) => tVwalk subst u
      | some (.app ts tc) => .app ts tc
      | some (.varDb n) => .varDb n := by
  intro v
  unfold tVwalk
  rw [vwalkEq _ h v]
  simp only [HolFiniteMapExact.lookup_map2]
  cases found : subst.lookup v with
  | none => simp [decodeInferT]
  | some t =>
    cases t with
    | uvar u => simp [encodeInferT]
    | varDb n => simp [encodeInferT, decodeInferT]
    | app ts tc => simp [encodeInferT, decodeInferT, decodeLeftInverse]

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_encodeVwalk_subst
    (subst : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).lookup key = subst.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).finiteSupport = subst.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst) = subst :=
  holFmapAsFiniteSupportParamWitness_tVR_subst subst key

@[hol "cakeml/compiler/inference/unifyScript.sml" "encode_vwalk"
  (fmap_as_finite_support_parameters := [subst])]
theorem encodeVwalk (subst : HolFiniteMapExact Nat InferT) (h : tWfs subst) : ∀ v,
    vwalk (subst.map2 (fun p => encodeInferT p.2)) v = encodeInferT (tVwalk subst v) := by
  intro v
  induction v using h.induction with
  | h v ih =>
    rw [vwalkEq _ h v, tVwalkEq subst h v]
    simp only [HolFiniteMapExact.lookup_map2]
    cases found : subst.lookup v with
    | none => simp [encodeInferT]
    | some t =>
      cases t with
      | uvar n =>
        simp only [Option.map_some, encodeInferT]
        apply ih n
        simp [vR, found, encodeInferT, vars]
      | varDb n => simp [encodeInferT]
      | app ts tc => simp [encodeInferT]

end Flapjack.Compiler.Inference.Unify
