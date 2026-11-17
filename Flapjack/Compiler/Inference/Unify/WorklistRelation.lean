module

public import Flapjack.Compiler.Inference.Unify.ComputationalWf
public import Flapjack.Compiler.Inference.Unify.WorklistBag
public import Flapjack.HOL.Unification.Walkstar.Relation
public import Flapjack.HOL.Unification.Subst.Vars

@[expose] public section

/-! The original paired-list unifier termination relation. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- Source-shaped worklist relation. It remains untagged because the computed
    `sp2fm` maps occur in its body, outside the scope of the current
    result-observation qualifier, which requires a producer in the signature. -/
def worklistR
    (child parent : Spt InferT × List (List InferT × List InferT)) : Prop :=
  cwfs child.1 ∧ cwfs parent.1 ∧ (sp2fm parent.1).submap (sp2fm child.1) ∧
    Set.Subset
      (Set.union (substVars ((sp2fm child.1).map2 (fun p => encodeInferT p.2)))
        (cplistVars child.2))
      (Set.union (substVars ((sp2fm parent.1).map2 (fun p => encodeInferT p.2)))
        (cplistVars parent.2)) ∧
    (Relation.TransGen
        (bagMultisetStep (walkstarR (sp2fm (sptMap encodeInferT child.1))))
        (pflat child.2) (pflat parent.2) ∨
      (pflat child.2 = pflat parent.2 ∧ child.2.length < parent.2.length))

/-- The canonical substitution survives the finite-map codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarRTrans_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "cakeml/compiler/inference/unifyScript.sml" "walkstarR_trans"
  (fmap_as_finite_support_parameters := [s])]
theorem walkstarRTrans {α β : Type} (s : HolFiniteMapExact Nat (Term β))
    (t1 t2 t3 : Term α) (h : walkstarR s t1 t2 ∧ walkstarR s t2 t3) :
    walkstarR s t1 t3 := by
  rcases h with ⟨h12, h23⟩
  rcases h12 with h12 | ⟨e12, n12⟩
  · rcases h23 with h23 | ⟨e23, _⟩
    · exact Or.inl (h12.trans h23)
    · exact Or.inl (e23 ▸ h12)
  · rcases h23 with h23 | ⟨e23, n23⟩
    · exact Or.inl (e12 ▸ h23)
    · exact Or.inr ⟨e12.trans e23, Nat.lt_trans n12 n23⟩

end Flapjack.Compiler.Inference.Unify
