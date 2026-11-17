module

public import Flapjack.Compiler.Inference.Unify.Walkstar.Encoding
public import Flapjack.Compiler.Inference.Unify.Substitution.Submap
public import Flapjack.HOL.Unification.Walkstar.Submap

@[expose] public section

namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- The smaller inference substitution survives the canonical map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tWalkstarSubmap_s1
    (s1 : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1)).lookup key = s1.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1)).finiteSupport = s1.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1) = s1 :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s1 key

/-- The larger inference substitution survives the canonical map codec. -/
theorem holFmapAsFiniteSupportParamWitness_tWalkstarSubmap_s2
    (s2 : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2)).lookup key = s2.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2)).finiteSupport = s2.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2) = s2 :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s2 key

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_walkstar_SUBMAP"
  (fmap_as_finite_support_parameters := [s1, s2])]
theorem tWalkstarSubmap (s1 : HolFiniteMapExact Nat InferT)
    (s2 : HolFiniteMapExact Nat InferT) (t : InferT)
    (h : s1.submap s2 ∧ tWfs s2) : tWalkstar s2 t = tWalkstar s2 (tWalkstar s1 t) := by
  have hs1 : tWfs s1 := tWfsSubmap s1 s2 ⟨h.2, h.1⟩
  have mapped : (s1.map2 (fun p => encodeInferT p.2)).submap
      (s2.map2 (fun p => encodeInferT p.2)) := by
    intro key value found
    simp only [HolFiniteMapExact.lookup_map2] at found ⊢
    cases hk : s1.lookup key with
    | none => simp [hk] at found
    | some x =>
      have hk2 := h.1 key x hk
      simpa [hk, hk2] using found
  change decodeInferT (walkstar (s2.map2 (fun p => encodeInferT p.2)) (encodeInferT t)) =
    decodeInferT (walkstar (s2.map2 (fun p => encodeInferT p.2)) (encodeInferT (tWalkstar s1 t)))
  rw [← encodeWalkstar s1 t hs1]
  congr 1
  exact walkstarSubmap _ _ _ ⟨mapped, h.2⟩

end Flapjack.Compiler.Inference.Unify
