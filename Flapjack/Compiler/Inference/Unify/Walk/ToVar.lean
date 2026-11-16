module

public import Flapjack.Compiler.Inference.Unify.Walk
public import Flapjack.HOL.Unification.Walk.ToVar

@[expose] public section

namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- The canonical inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tVwalkToVar_subst
    (subst : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).lookup key = subst.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).finiteSupport = subst.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst) = subst :=
  holFmapAsFiniteSupportParamWitness_tVR_subst subst key

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_vwalk_to_var"
  (fmap_as_finite_support_parameters := [subst])]
theorem tVwalkToVar (subst : HolFiniteMapExact Nat InferT) (h : tWfs subst) : ∀ v u,
    tVwalk subst v = .uvar u → u ∉ subst.domain := by
  intro v u eq
  have he : vwalk (subst.map2 (fun p => encodeInferT p.2)) v = .var u := by
    rw [encodeVwalk subst h v, eq]
    simp [encodeInferT]
  have absent := vwalkToVar (subst.map2 (fun p => encodeInferT p.2)) h v u he
  change ¬ ((subst.map2 (fun p => encodeInferT p.2)).lookup u ≠ none) at absent
  change ¬ (subst.lookup u ≠ none)
  intro present
  apply absent
  simp only [HolFiniteMapExact.lookup_map2]
  cases found : subst.lookup u with
  | none => exact (present found).elim
  | some t => simp

end Flapjack.Compiler.Inference.Unify
