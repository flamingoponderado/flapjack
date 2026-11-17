module

public import Flapjack.HOL.Unification.Rmfmap.Sunify
public import Flapjack.Compiler.Inference.Unify.ComputationalWf
public import Flapjack.Compiler.Inference.Unify.ListUnification

@[expose] public section

/-! Source-shaped sparse inference unification. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- Source-shaped choice model. It remains untagged because agreement with
    HOL's selected unifier outside the well-formedness guard is not established;
    the finite-map representation is internal to the sparse-tree result. -/
noncomputable def cunifyModel (s : Spt InferT) (a b : InferT) : Option (Spt InferT) :=
  (sunifyModel (sptMap encodeInferT s) (encodeInferT a) (encodeInferT b)).map (sptMap decodeInferT)

/-- The sparse-tree encoding projects to the encoded finite map. This
    specialization is infrastructure for the source unifier proofs. -/
theorem sparseEncode (s : Spt InferT) :
    sp2fm (sptMap encodeInferT s) = encodeSubst (sp2fm s) := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  exact sptLookup_sptMap encodeInferT s key

/-- The sparse-tree decoding projects to the decoded finite map. This is
    source-unifier proof infrastructure rather than a separate HOL theorem. -/
theorem sparseDecode (s : HolFiniteMapExact Nat (Term Atom)) :
    sp2fm (sptMap decodeInferT (fm2sp s)) = decodeSubst s := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  change sptLookup key (sptMap decodeInferT (fm2sp s)) = (decodeSubst s).lookup key
  rw [sptLookup_sptMap]
  simp [lookupFm2sp, decodeSubst, HolFiniteMapExact.lookup_map2]

/-- The source-shaped sparse result projects to the Lean inference model
    on all inputs. This is Lean correspondence infrastructure, not the full
    HOL transfer theorem. -/
theorem cunifyModelMap (s : Spt InferT) (a b : InferT) :
    (cunifyModel s a b).map sp2fm = tUnifyModel (sp2fm s) a b := by
  simp only [cunifyModel, sunifyModel, tUnifyModel, Option.map_map, sparseEncode]
  cases h : specifiedUnify (encodeSubst (sp2fm s)) (encodeInferT a) (encodeInferT b) with
  | none => rfl
  | some result =>
    simp only [Option.map_some, Option.some.injEq]
    exact sparseDecode result

/-- Every successful source-shaped unifier result is a well-formed sparse
    tree. This Lean helper supports exact equality of converted trees. -/
theorem cunifyModelTreeWf (s out : Spt InferT) (a b : InferT) (h : cunifyModel s a b = some out) :
    sptWf out = true := by
  unfold cunifyModel sunifyModel at h
  cases hr : specifiedUnify (sp2fm (sptMap encodeInferT s)) (encodeInferT a) (encodeInferT b) with
  | none => simp [hr] at h
  | some fm =>
    simp only [hr, Option.map_some, Option.some.injEq] at h
    subst out
    rw [sptWfMap]
    exact wfFm2sp _

end Flapjack.Compiler.Inference.Unify
