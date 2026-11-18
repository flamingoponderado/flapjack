module

public import Flapjack.Compiler.Inference.InferProps.DeBruijn.Walk
public import Flapjack.Compiler.Inference.Unify.Walkstar.Induction

@[expose] public section

/-! Normalization commutes with inference-type de Bruijn shifts. -/
namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.Unify

private theorem shiftListMap (n : Nat) (ts : List InferT) :
    inferDeBruijnIncList n ts = ts.map (inferDeBruijnInc n) := by
  induction ts with
  | nil => simp [inferDeBruijnIncList]
  | cons t ts ih => simp [inferDeBruijnIncList, ih]

/-- The substitution parameter survives the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarInc_s
    (s : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s key

/-- Shifting every substitution value commutes with inference-type normalization. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "walkstar_inc"
  (fmap_as_finite_support_parameters := [s])]
theorem walkstarInc (n : Nat) (s : HolFiniteMapExact Nat InferT) (t : InferT) (h : tWfs s) :
    tWalkstar (s.map2 (fun p => inferDeBruijnInc n p.2)) (inferDeBruijnInc n t) =
      inferDeBruijnInc n (tWalkstar s t) := by
  induction t using tWalkstarInd s h with
  | _ t ih =>
    rw [walkstarEqn _ (incWfs n s h), walkstarEqn s h t, walkInc s n t h]
    cases found : tWalk s t with
    | uvar v => simp [inferDeBruijnInc]
    | varDb v => simp [inferDeBruijnInc]
    | app ts tc =>
      simp only [inferDeBruijnInc, shiftListMap, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ih ts tc a ⟨found, ha⟩

/-- The substitution parameter survives the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarInc2_s
    (s : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s key

/-- The variable case of normalization/shift commutation. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "walkstar_inc2"
  (fmap_as_finite_support_parameters := [s])]
theorem walkstarInc2 (n : Nat) (s : HolFiniteMapExact Nat InferT) (v : Nat) (h : tWfs s) :
    tWalkstar (s.map2 (fun p => inferDeBruijnInc n p.2)) (.uvar v) =
      inferDeBruijnInc n (tWalkstar s (.uvar v)) := by
  simpa [inferDeBruijnInc] using walkstarInc n s (.uvar v) h

end Flapjack.Compiler.Inference.InferProps
