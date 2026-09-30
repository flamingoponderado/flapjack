import Flapjack.HolRef
import Flapjack.Pancake.Proofs.CrepInline.InlineProgCorrect

/-!
# crep_inline: `state_rel_imp_semantics` group

Ports of the final crep_inline semantic-preservation group
(`cakeml/pancake/proofs/crep_inlineProofScript.sml:3263-3452`, bead
`flapjack-2de.4` and its children): `fst_map_3_f` and
`compile_inline_distinct` (bead `.1`) and `evaluate_call_same_result_state`
(bead `.2`).
-/

namespace Flapjack

namespace CrepInlineStateRelImpSemantics

open CrepInlineCanonical

namespace EvaluateCallSameSupport
/-- Canonical carrier roundtrip re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end EvaluateCallSameSupport

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


open CrepInlineExact CrepInlineCallCase in
/-- Exact HOL `evaluate_call_same_result_state`
    (`crep_inlineProofScript.sml:3284-3294`): a top-level tail call has the
    same result on related states, with `state_rel_code` related post-states.
    Proof: `inline_prog` with the empty inline bag leaves the call unchanged, so
    the reviewed `callNonInlined` applies, with its callee premise supplied by
    the accepted `inline_prog_correct` motive; the handler premise is vacuous
    for `Call NONE`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_call_same_result_state"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code, inl_fs])
  (words_as_type_indexed_bitvec)]
theorem evaluateCallSameResultStateExact {σ : Type}
    (e : Flapjack.Basis.Pure.MlString.MlString) (args : List (CrepExpHOL width))
    (s : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width))
    (s' t : CrepSemHOLState width σ)
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width)) :
    evalCrepSemHOLProgExact s (.call none e args) = (r, s') ∧
      crepInlineStateRelCodeExact s t ∧
      HolFiniteMapExact.submap inl_fs s.code ∧
      crepInlineLocalsStrongRelExact s t ∧
      crepInlineCodeInlRelExact inl_fs s t ∧
      r ≠ some .error →
    (evalCrepSemHOLProgExact t (.call none e args)).1 =
        (evalCrepSemHOLProgExact s (.call none e args)).1 ∧
      crepInlineStateRelCodeExact (evalCrepSemHOLProgExact s (.call none e args)).2
        (evalCrepSemHOLProgExact t (.call none e args)).2 := by
  rintro ⟨hev, hsr, hsub, hls, hci, hne⟩
  have hpath : ¬ inlinedPath (HolFiniteMapExact.empty : InlMap width) none e := by
    rintro ⟨h, _⟩; simp [HolFiniteMapExact.empty] at h
  obtain ⟨t', ht', hrel, _, _⟩ := callNonInlined none e args s
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc _ _ _ _ => by cases hc)
    (fun _ _ prog nl _ _ _ _ _ => inlineMotive prog _)
    r s' inl_fs t HolFiniteMapExact.empty hpath hev hne hsub
    (fun _ _ h => by simp [HolFiniteMapExact.empty] at h) hsr hls hci
  rw [inlineProgHOLExact_call_nonInlined _ _ _ _ hpath] at ht'
  simp only [inlineCaltyp] at ht'
  rw [ht', hev]
  exact ⟨rfl, hrel⟩

end CrepInlineStateRelImpSemantics

end Flapjack
