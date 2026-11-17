module

public import Flapjack.Compiler.Inference.EnvRel
public import Flapjack.Compiler.Inference.Unify.Walkstar

@[expose] public section

/-! Substitution and conversion after inference normalization. -/
namespace Flapjack.Compiler.Inference.EnvRel
open Flapjack.TypeSystemHOL Flapjack.Compiler.Inference.Unify
  Flapjack.Compiler.Inference.InferProps

mutual
/-- Structural induction for substitution after inference normalization. -/
private theorem dbSubstInferSubstSwapType (t : SemanticT) (tvs : Nat)
    (s : HolFiniteMapExact Nat InferT) (subst : List InferT)
    (hw : tWfs s) (h : checkFreevars tvs [] t = true) :
    convertT (tWalkstar s (Infer.inferDeBruijnSubst subst (unconvertT t))) =
      deBruijnSubst 0 (subst.map (convertT ∘ tWalkstar s)) t := by
  cases t with
  | var name => simp [checkFreevars] at h
  | varDb k =>
    by_cases hk : k < subst.length
    · simp [unconvertT, Infer.inferDeBruijnSubst, deBruijnSubst, hk]
    · simp [unconvertT, Infer.inferDeBruijnSubst, deBruijnSubst, hk,
        (tWalkstarEqn1 s (k - subst.length) [] 0 hw).1, convertT]
  | app ts tc =>
    have hl : checkFreevarsList tvs [] ts = true := by simpa [checkFreevars] using h
    simp [unconvertT, Infer.inferDeBruijnSubst, deBruijnSubst,
      (tWalkstarEqn1 s 0 _ tc hw).2, convertTEqn.2,
      dbSubstInferSubstSwapList ts tvs s subst hw hl]
termination_by sizeOf t

/-- List recursion for substitution after inference normalization. -/
private theorem dbSubstInferSubstSwapList (ts : List SemanticT) (tvs : Nat)
    (s : HolFiniteMapExact Nat InferT) (subst : List InferT)
    (hw : tWfs s) (h : checkFreevarsList tvs [] ts = true) :
    (Infer.inferDeBruijnSubstList subst (unconvertTList ts)).map (convertT ∘ tWalkstar s) =
      deBruijnSubstList 0 (subst.map (convertT ∘ tWalkstar s)) ts := by
  cases ts with
  | nil => simp [unconvertTList, Infer.inferDeBruijnSubstList, deBruijnSubstList]
  | cons t ts =>
    simp only [checkFreevarsList, Bool.and_eq_true] at h
    simp [unconvertTList, Infer.inferDeBruijnSubstList, deBruijnSubstList,
      dbSubstInferSubstSwapType t tvs s subst hw h.1,
      dbSubstInferSubstSwapList ts tvs s subst hw h.2]
termination_by sizeOf ts
end

/-- The inference substitution survives the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_dbSubstInferSubstSwap3_s
    (s : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad
        (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad
        (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad
        (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s key

@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "db_subst_infer_subst_swap3"
  (fmap_as_finite_support_parameters := [s])]
theorem dbSubstInferSubstSwap3 (t : SemanticT) (tvs : Nat)
    (s : HolFiniteMapExact Nat InferT) (subst : List InferT)
    (h : tWfs s ∧ checkFreevars tvs [] t = true) :
    convertT (tWalkstar s (Infer.inferDeBruijnSubst subst (unconvertT t))) =
      deBruijnSubst 0 (subst.map (convertT ∘ tWalkstar s)) t :=
  dbSubstInferSubstSwapType t tvs s subst h.1 h.2

end Flapjack.Compiler.Inference.EnvRel
