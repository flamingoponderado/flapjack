module

public import Flapjack.Compiler.Inference.InferProps.DeBruijn.WellFounded
public import Flapjack.Compiler.Inference.Unify.Walk

@[expose] public section

/-! Variable walking commutes with inference-type de Bruijn shifts. -/
namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- The substitution parameter survives the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_vwalkInc_s
    (s : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s key

/-- Shifting every substitution value commutes with variable walking. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "vwalk_inc"
  (fmap_as_finite_support_parameters := [s])]
theorem vwalkInc (s : HolFiniteMapExact Nat InferT) (n v : Nat) (h : tWfs s) :
    tVwalk (s.map2 (fun p => inferDeBruijnInc n p.2)) v =
      inferDeBruijnInc n (tVwalk s v) := by
  induction v using ((tWfsEqn s).1 h).induction with
  | h v ih =>
    rw [tVwalkEq _ (incWfs n s h) v, tVwalkEq s h v]
    simp only [HolFiniteMapExact.lookup_map2]
    cases found : s.lookup v with
    | none => simp [inferDeBruijnInc]
    | some t =>
      cases t with
      | varDb k => simp [inferDeBruijnInc]
      | app ts tc => simp [inferDeBruijnInc]
      | uvar u =>
        simp only [Option.map_some, inferDeBruijnInc]
        apply ih u
        rw [tVREqn]
        simp [found, tVars, encodeInferT, vars]

end Flapjack.Compiler.Inference.InferProps
