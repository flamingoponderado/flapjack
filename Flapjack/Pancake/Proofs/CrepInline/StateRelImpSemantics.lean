import Flapjack.HolRef
import Flapjack.Pancake.Proofs.CrepInline.InlineProgCorrect

/-!
# crep_inline: `state_rel_imp_semantics` group

Ports of the final crep_inline semantic-preservation group
(`cakeml/pancake/proofs/crep_inlineProofScript.sml:3263-3452`, bead
`flapjack-2de.4` and its children): `fst_map_3_f` and
`compile_inline_distinct` (bead `.1`).
-/

namespace Flapjack

namespace CrepInlineStateRelImpSemantics

open CrepInlineCanonical

variable {width : Nat} [NeZero width]

/-- Canonical roundtrip witness for the `inl_fs` parameter qualifier. -/
theorem holFmapAsFiniteSupportParamWitness_fstMap3F_inl_fs
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width)) (key : CrepInlineMapHOLName) :
    (CrepInlineMapBroad.ofBroad (CrepInlineMapBroad.toBroad inl_fs)).lookup key =
        inl_fs.lookup key ∧
      (CrepInlineMapBroad.ofBroad (CrepInlineMapBroad.toBroad inl_fs)).finiteSupport =
        inl_fs.finiteSupport ∧
      CrepInlineMapBroad.ofBroad (CrepInlineMapBroad.toBroad inl_fs) = inl_fs :=
  holFmapAsFiniteSupportParamWitness_compileInlProgHOLExact_inl_fs inl_fs key

/-- Canonical roundtrip witness for the `inl_fs` parameter qualifier. -/
theorem holFmapAsFiniteSupportParamWitness_compileInlineDistinct_inl_fs
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width)) (key : CrepInlineMapHOLName) :
    (CrepInlineMapBroad.ofBroad (CrepInlineMapBroad.toBroad inl_fs)).lookup key =
        inl_fs.lookup key ∧
      (CrepInlineMapBroad.ofBroad (CrepInlineMapBroad.toBroad inl_fs)).finiteSupport =
        inl_fs.finiteSupport ∧
      CrepInlineMapBroad.ofBroad (CrepInlineMapBroad.toBroad inl_fs) = inl_fs :=
  holFmapAsFiniteSupportParamWitness_compileInlProgHOLExact_inl_fs inl_fs key

/-- Exact HOL `fst_map_3_f` (`crep_inlineProofScript.sml:3263-3264`):
    `∀inl_fs x. FST x = (FST o (λ(name, params, body).
      (name, params, inline_prog (inl_fs \\\\ name) body))) x`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "fst_map_3_f"
  (fmap_as_finite_support_parameters := [inl_fs]) (words_as_type_indexed_bitvec)]
theorem fstMap3F
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (x : CrepInlineMapHOLName × List Nat × CrepProgHOL width) :
    x.1 = (Prod.fst ∘ fun (triple : CrepInlineMapHOLName × List Nat × CrepProgHOL width) =>
      (triple.1, triple.2.1, inlineProgHOLExact (inl_fs.erase triple.1) triple.2.2)) x := rfl

/-- Exact HOL `compile_inline_distinct` (`crep_inlineProofScript.sml:3270-3272`):
    `ALL_DISTINCT (MAP FST crep_code) ⇒
     ALL_DISTINCT (MAP FST (compile_inl_prog inl_fs crep_code))`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "compile_inline_distinct"
  (fmap_as_finite_support_parameters := [inl_fs]) (words_as_type_indexed_bitvec)]
theorem compileInlineDistinct
    (crep_code : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width))
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width)) :
    (crep_code.map Prod.fst).Nodup →
      ((compileInlProgHOLExact inl_fs crep_code).map Prod.fst).Nodup := by
  intro h
  simpa [compileInlProgHOLExact, List.map_map, Function.comp_def] using h

end CrepInlineStateRelImpSemantics

end Flapjack
