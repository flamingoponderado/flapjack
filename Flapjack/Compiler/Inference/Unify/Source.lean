module

public import Flapjack.HOL.Unification.Rmfmap.Sunify
public import Flapjack.Compiler.Inference.Unify.Unification.Choice
public import Flapjack.Compiler.Inference.Unify.ComputationalWf
public import Flapjack.Compiler.Inference.Unify.ListUnification

@[expose] public section

/-! Source-shaped sparse inference unification. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- Source-shaped choice model, untagged pending review of its nested
    option-wrapped finite-map result. -/
noncomputable def cunifyModel (s : Spt InferT) (a b : InferT) : Option (Spt InferT) :=
  (sunifyModel (sptMap encodeInferT s) (encodeInferT a) (encodeInferT b)).map (sptMap decodeInferT)

private theorem sparseEncode (s : Spt InferT) :
    sp2fm (sptMap encodeInferT s) = encodeSubst (sp2fm s) := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  exact sptLookup_sptMap encodeInferT s key

private theorem sparseDecode (s : HolFiniteMapExact Nat (Term Atom)) :
    sp2fm (sptMap decodeInferT (fm2sp s)) = decodeSubst s := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  change sptLookup key (sptMap decodeInferT (fm2sp s)) = (decodeSubst s).lookup key
  rw [sptLookup_sptMap]
  simp [lookupFm2sp, decodeSubst, HolFiniteMapExact.lookup_map2]

/-- The source-shaped sparse result projects to the inference unifier on
    well-formed input. This is Lean correspondence infrastructure, not the
    full HOL transfer theorem. -/
theorem cunifyModelMap (s : Spt InferT) (a b : InferT) (hw : cwfs s) :
    (cunifyModel s a b).map sp2fm = tUnifyModel (sp2fm s) a b := by
  have hws : tWfs (sp2fm s) := by
    change wfs (encodeSubst (sp2fm s))
    rw [← sparseEncode]
    exact hw.1
  rw [← tUnifyModelEqSpecified _ _ _ hws]
  simp only [cunifyModel, sunifyModel, Option.map_map, sparseEncode]
  cases h : specifiedUnify (encodeSubst (sp2fm s)) (encodeInferT a) (encodeInferT b) with
  | none => rfl
  | some result =>
    simp only [Option.map_some, Option.some.injEq]
    exact sparseDecode result

private theorem sourceWf (s out : Spt InferT) (a b : InferT) (h : cunifyModel s a b = some out) :
    sptWf out = true := by
  unfold cunifyModel sunifyModel at h
  cases hr : specifiedUnify (sp2fm (sptMap encodeInferT s)) (encodeInferT a) (encodeInferT b) with
  | none => simp [hr] at h
  | some fm =>
    simp only [hr, Option.map_some, Option.some.injEq] at h
    subst out
    rw [sptWfMap]
    exact wfFm2sp _

@[hol "cakeml/compiler/inference/unifyScript.sml" "cunify_preserves_cwfs"]
theorem cunifyPreservesCwfsModel (s : Spt InferT) (a b : InferT) (out : Spt InferT)
    (h : cwfs s ∧ cunifyModel s a b = some out) : cwfs out := by
  have hmodel : tUnifyModel (sp2fm s) a b = some (sp2fm out) := by
    rw [← cunifyModelMap s a b h.1, h.2]
    rfl
  have hw : tWfs (sp2fm s) := by
    change wfs (encodeSubst (sp2fm s))
    rw [← sparseEncode]
    exact h.1.1
  have hout := tUnifyModelWfs (sp2fm s) a b (sp2fm out) ⟨hw, hmodel⟩
  constructor
  · change wfs (sp2fm (sptMap encodeInferT out))
    rw [sparseEncode]
    exact hout
  · exact sourceWf s out a b h.2

end Flapjack.Compiler.Inference.Unify
