import Flapjack.HolRef
import Flapjack.Pancake.Proofs.CrepInline.InlineProgCorrect
import Flapjack.Pancake.CrepToLoop.Proofs.CodeRel2
import Flapjack.Pancake.Semantics.CrepSem.CrepObservationalSemantics

/-!
# crep_inline: `state_rel_imp_semantics` group

Ports of the final crep_inline semantic-preservation group
(`cakeml/pancake/proofs/crep_inlineProofScript.sml:3263-3452`, bead
`flapjack-2de.4` and its children): `fst_map_3_f` and
`compile_inline_distinct` (bead `.1`), `evaluate_call_same_result_state`
(bead `.2`) `state_rel_imp_semantics_local` (bead `.3`) and
`state_rel_imp_semantics` (bead `flapjack-2de.4`).
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

/-- Local support: `code_inl_rel` for the code maps of `compile_inl_prog`. -/
theorem codeInl_of_alist {σ : Type} (s t : CrepSemHOLState width σ)
    (crep_code : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width))
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (hd : (crep_code.map Prod.fst).Nodup)
    (hs : s.code = alistToFmapCodeExact crep_code)
    (ht : t.code = alistToFmapCodeExact (compileInlProgHOLExact inl_fs crep_code)) :
    CrepInlineExact.crepInlineCodeInlRelExact inl_fs s t := by
  intro fname args prog hlk
  rw [hs] at hlk
  have hmem : (fname, args, prog) ∈ crep_code :=
    flookup_fupdateList_reverse_mem' crep_code fname (args, prog) hlk
  refine ⟨inl_fs.erase fname, CrepInlineCallCase.submap_erase _ _, ?_⟩
  rw [ht]
  exact flookup_fupdateList_reverse_of_mem _ fname (args, inlineProgHOLExact (inl_fs.erase fname) prog)
    (compileInlineDistinct crep_code inl_fs hd)
    (List.mem_map.mpr ⟨(fname, args, prog), hmem, rfl⟩)

/-- Local support: at every clock where the source entry call does not end in
    `Error`, the target entry call agrees in result and FFI state. -/
theorem entry_agree {σ : Type} (s t : CrepSemHOLState width σ) (start : Flapjack.Basis.Pure.MlString.MlString)
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (hsr : CrepInlineExact.crepInlineStateRelCodeExact s t)
    (hls : CrepInlineExact.crepInlineLocalsStrongRelExact s t)
    (hsub : HolFiniteMapExact.submap inl_fs s.code)
    (hci : CrepInlineExact.crepInlineCodeInlRelExact inl_fs s t) (k : Nat)
    (hne : (evalCrepSemHOLProgExact { s with clock := k } (.call none start [])).1 ≠ some .error) :
    (evalCrepSemHOLProgExact { t with clock := k } (.call none start [])).1 =
        (evalCrepSemHOLProgExact { s with clock := k } (.call none start [])).1 ∧
      (evalCrepSemHOLProgExact { t with clock := k } (.call none start [])).2.ffi =
        (evalCrepSemHOLProgExact { s with clock := k } (.call none start [])).2.ffi := by
  obtain ⟨a, b, c, d, _, f, g, h, i⟩ := hsr
  have hsrk : CrepInlineExact.crepInlineStateRelCodeExact { s with clock := k } { t with clock := k } :=
    ⟨a, b, c, d, rfl, f, g, h, i⟩
  obtain ⟨h1, h2⟩ := evaluateCallSameResultStateExact start [] { s with clock := k }
    (evalCrepSemHOLProgExact { s with clock := k } (.call none start [])).1
    (evalCrepSemHOLProgExact { s with clock := k } (.call none start [])).2
    { t with clock := k } inl_fs ⟨rfl, hsrk, hsub, hls, hci, hne⟩
  exact ⟨h1, h2.2.2.2.2.2.2.1.symm⟩

/-- Local support: if `semantics s start ≠ Fail` then no clock gives `Error`. -/
theorem noError_of_notFail {σ : Type} (s : CrepSemHOLState width σ) (start : Flapjack.Basis.Pure.MlString.MlString)
    (h : crepSemantics s start ≠ .fail) (k : Nat) :
    (evalCrepSemHOLProgExact { s with clock := k } (.call none start [])).1 ≠ some .error := by
  intro he
  apply h
  unfold crepSemantics
  simp only [crepEntryProgram]
  refine if_pos ?_
  exact ⟨k, by rw [he]; trivial⟩

theorem ite_fail_congr (C C' : Prop) [Decidable C] [Decidable C'] (a b : HolBehaviour)
    (hC : C ↔ C') (hab : a = b) :
    (if C then HolBehaviour.fail else a) = (if C' then HolBehaviour.fail else b) := by
  subst hab
  by_cases h : C
  · rw [if_pos h, if_pos (hC.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hC.mpr h'))]

theorem sem_tail_congr {P Q : HolBehaviour → Prop} {x y : HolLList HolIoEvent}
    (hPQ : P = Q) (hxy : x = y) :
    (match holOptionSome P with
     | some r => r
     | none => HolBehaviour.diverge x) =
    (match holOptionSome Q with
     | some r => r
     | none => HolBehaviour.diverge y) := by
  subst hPQ; subst hxy; rfl

open CrepInlineExact in
/-- Exact HOL `state_rel_imp_semantics_local` (`crep_inlineProofScript.sml:3309-3318`).
    `alist_to_fmap` is the reviewed `alistToFmapCodeExact` adapter and
    `semantics` the tagged crepSem `semantics_def`.  Proof: `code_inl_rel`
    follows from the code equations (`codeInl_of_alist`, with
    `compile_inline_distinct`).  Because `semantics s start ≠ Fail`, no clock
    gives `Error`, so `evaluate_call_same_result_state` equates results and FFI
    states clock by clock.  All three branches of `semantics_def` then agree
    pointwise. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "state_rel_imp_semantics_local"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code, inl_fs])
  (words_as_type_indexed_bitvec)]
theorem stateRelImpSemanticsLocalExact {σ : Type}
    (s t : CrepSemHOLState width σ)
    (crep_code : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width))
    (start : Flapjack.Basis.Pure.MlString.MlString)
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (ns : List Nat) (prog : CrepProgHOL width) :
    crepInlineStateRelCodeExact s t ∧ crepInlineLocalsStrongRelExact s t ∧
      (crep_code.map Prod.fst).Nodup ∧
      s.code = alistToFmapCodeExact crep_code ∧
      HolFiniteMapExact.submap inl_fs s.code ∧
      t.code = alistToFmapCodeExact (compileInlProgHOLExact inl_fs crep_code) ∧
      s.code.lookup start = some (ns, prog) ∧
      crepSemantics s start ≠ .fail →
    crepSemantics t start = crepSemantics s start := by
  classical
  rintro ⟨hsr, hls, hd, hs, hsub, ht, _, hnf⟩
  have hci := codeInl_of_alist s t crep_code inl_fs hd hs ht
  have hB := fun k => entry_agree s t start inl_fs hsr hls hsub hci k (noError_of_notFail s start hnf k)
  unfold crepSemantics
  simp only [crepEntryProgram]
  refine ite_fail_congr _ _ _ _ ?_ (sem_tail_congr ?_ ?_)
  · constructor
    · rintro ⟨k, hk⟩; exact ⟨k, by rw [← (hB k).1]; exact hk⟩
    · rintro ⟨k, hk⟩; exact ⟨k, by rw [(hB k).1]; exact hk⟩
  · funext res
    apply propext
    constructor
    · rintro ⟨k, t', r, outcome, hk, hm, hres⟩
      obtain ⟨e1, e2⟩ := hB k
      rw [hk] at e1 e2
      refine ⟨k, (evalCrepSemHOLProgExact { s with clock := k } (.call none start [])).2, r,
        outcome, Prod.ext e1.symm rfl, hm, ?_⟩
      rw [hres]; simp only at e2; rw [e2]
    · rintro ⟨k, t', r, outcome, hk, hm, hres⟩
      obtain ⟨e1, e2⟩ := hB k
      rw [hk] at e1 e2
      refine ⟨k, (evalCrepSemHOLProgExact { t with clock := k } (.call none start [])).2, r,
        outcome, Prod.ext e1 rfl, hm, ?_⟩
      rw [hres]; simp only at e2; rw [e2]
  · congr 1
    funext l
    apply propext
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, by rw [(hB k).2]⟩
    · rintro ⟨k, rfl⟩; exact ⟨k, by rw [(hB k).2]⟩

open CrepInlineExact in
/-- Exact HOL `state_rel_imp_semantics` (`crep_inlineProofScript.sml:3440-3448`):
    the crep_inline pass `compile_inl_top` preserves observational semantics.
    Proof as HOL's: unfold `compile_inl_top_def` and apply
    `state_rel_imp_semantics_local` with
    `inl_fs = alist_to_fmap (FILTER (λ(x,y). MEM x inl_fname) crep_code)`, whose
    `SUBMAP` into `s.code` follows from `ALL_DISTINCT (MAP FST crep_code)`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "state_rel_imp_semantics"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem stateRelImpSemanticsExact {σ : Type}
    (s t : CrepSemHOLState width σ)
    (crep_code : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width))
    (start : Flapjack.Basis.Pure.MlString.MlString)
    (inl_fname : List CrepInlineMapHOLName)
    (ns : List Nat) (prog : CrepProgHOL width) :
    crepInlineStateRelCodeExact s t ∧ crepInlineLocalsStrongRelExact s t ∧
      (crep_code.map Prod.fst).Nodup ∧
      s.code = alistToFmapCodeExact crep_code ∧
      t.code = alistToFmapCodeExact (compileInlTopHOLExact inl_fname crep_code) ∧
      s.code.lookup start = some (ns, prog) ∧
      crepSemantics s start ≠ .fail →
    crepSemantics t start = crepSemantics s start := by
  rintro ⟨hsr, hls, hd, hs, ht, hlk, hnf⟩
  have ht' : t.code = alistToFmapCodeExact (compileInlProgHOLExact
      (alistToFmapHOLExact (crep_code.filter fun triple => inl_fname.contains triple.1))
      crep_code) := by
    rw [ht, compileInlTopHOLExact]
    rw [compileInlProgHOLExactWithSupport_eq_compileInlProgHOLExact]
  refine stateRelImpSemanticsLocalExact s t crep_code start _ ns prog
    ⟨hsr, hls, hd, hs, fun k v h => ?_, ht', hlk, hnf⟩
  rw [hs]
  have hm := flookup_fupdateList_reverse_mem' _ k v h
  exact flookup_fupdateList_reverse_of_mem crep_code k v hd (List.mem_filter.mp hm).1

end CrepInlineStateRelImpSemantics

end Flapjack
