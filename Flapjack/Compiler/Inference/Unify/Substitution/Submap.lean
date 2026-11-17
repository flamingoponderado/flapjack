module

public import Flapjack.Compiler.Inference.Unify.Substitution

@[expose] public section

namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- The smaller inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tWfsSubmap_s1
    (s1 : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1)).lookup key = s1.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1)).finiteSupport = s1.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1) = s1 :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s1 key

/-- The larger inference substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tWfsSubmap_s2
    (s2 : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2)).lookup key = s2.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2)).finiteSupport = s2.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2) = s2 :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s2 key

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_wfs_SUBMAP"
  (fmap_as_finite_support_parameters := [s1, s2])]
theorem tWfsSubmap (s1 : HolFiniteMapExact Nat InferT)
    (s2 : HolFiniteMapExact Nat InferT) (h : tWfs s2 ∧ s1.submap s2) : tWfs s1 := by
  apply wfsSubmap _ _
  constructor
  · exact h.1
  · intro key value found
    simp only [HolFiniteMapExact.lookup_map2] at found ⊢
    cases hk : s1.lookup key with
    | none => simp [hk] at found
    | some t =>
      have hk2 := h.2 key t hk
      simpa [hk, hk2] using found

end Flapjack.Compiler.Inference.Unify
