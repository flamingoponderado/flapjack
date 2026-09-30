import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanToCrep.StateRelImpSemantics
import Flapjack.Pancake.Proofs.CrepInline.StateRelImpSemantics

/-!
# pan_to_crep: the final `state_rel_imp_semantics`

HOL `pan_to_crepProofScript.sml:5005-5041` (bead `flapjack-pxn.18.4.4.1`): the
whole pan_to_crep pass (`compile_to_crep` followed by crep_inline's
`compile_inl_top`) preserves observational semantics; and its declarations
form `state_rel_imp_semantics_decls` (`:5042-5053`).  As in HOL, it composes
the accepted `state_rel_imp_semantics_to_crep` (with the target code replaced by
the un-inlined Crep code) and crep_inline's `state_rel_imp_semantics`.
-/

namespace Flapjack

namespace PanToCrepStateRelImpSemanticsTop

open Flapjack.Pancake.PanLang

/-- Local support: a Crep entry whose name is absent from the code map fails. -/
theorem crepSemantics_fail_of_lookup_none {width : Nat} [NeZero width] {σ : Type}
    (t : CrepSemHOLState width σ) (start : Flapjack.Basis.Pure.MlString.MlString)
    (h : t.code.lookup start = none) : crepSemantics t start = .fail := by
  unfold crepSemantics
  simp only [crepEntryProgram]
  refine if_pos ⟨0, ?_⟩
  rw [evalCrepSemHOLProgExact_call_holShape]
  simp [lookupCodeFiniteHOL, h]

namespace StateRelImpSemanticsTopWitnesses
/-- Same-module canonical witness for the PanSem finite-map carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Same-module canonical witness for the Crep finite-map carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end StateRelImpSemanticsTopWitnesses

/-- Exact HOL `state_rel_imp_semantics` (`pan_to_crepProofScript.sml:5005-5016`):
    the pan_to_crep `compile_prog` (`compile_to_crep` then crep_inline's
    `compile_inl_top`) preserves semantics.  `alist_to_fmap` is rendered as in the
    accepted `state_rel_imp_semantics_to_crep`.  Proof as HOL's:
    `state_rel_imp_semantics_to_crep` at `t with code := alist_to_fmap crep_code`,
    then crep_inline `state_rel_imp_semantics`; an absent entry would make the
    Crep semantics `Fail`, contradicting the source hypothesis. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_imp_semantics"
  (fmap_as_finite_support_relation :=
    [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals,
      PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes,
      CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem stateRelImpSemanticsPanToCrep {width : Nat} {σ : Type} [NeZero width] :
    ∀ (s : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
      (pan_code : List (DeclHOL width)) (start : MlS),
      panToCrepStateRelFiniteExact s t ∧
        ((functionsHOL pan_code).map Prod.fst).Nodup ∧
        s.code = HolFiniteMapExact.empty.updateList (functionsHOL pan_code).reverse ∧
        t.code = HolFiniteMapExact.empty.updateList (compileProgDeclsHOLW pan_code).reverse ∧
        s.locals = HolFiniteMapExact.empty ∧
        (∀ entry ∈ functionsHOL pan_code, localisedProgHOL entry.2.2.1 = true) ∧
        sizeOfEidsHOL pan_code < 2 ^ width ∧
        (∀ key, (s.eshapes.lookup key).isSome =
          ((getEidsFromDeclsHOL pan_code).lookup key).isSome) ∧
        PanSemStateFiniteExact.semantics s start ≠ .fail →
      crepSemantics t start = PanSemStateFiniteExact.semantics s start := by
  intro s t pan_code start ⟨hsr, hdist, hscode, htcode, hloc, hlocal, hsize, hdom, hfail⟩
  have h1 := stateRelImpSemanticsToCrep s
    { t with code := HolFiniteMapExact.empty.updateList (compileToCrepExactHOLW pan_code).reverse }
    pan_code start ⟨hsr, hdist, hscode, rfl, hloc, hlocal, hsize, hdom, hfail⟩
  rw [← h1]
  have hnf : crepSemantics
      { t with code := HolFiniteMapExact.empty.updateList (compileToCrepExactHOLW pan_code).reverse }
      start ≠ .fail := by rw [h1]; exact hfail
  rcases hlk : (HolFiniteMapExact.empty.updateList (compileToCrepExactHOLW pan_code).reverse).lookup
      start with _ | ⟨ns, prog⟩
  · exact absurd (crepSemantics_fail_of_lookup_none _ start hlk) hnf
  exact CrepInlineStateRelImpSemantics.stateRelImpSemanticsExact _ t
    (compileToCrepExactHOLW pan_code) start
    ((functionsHOL (pan_code.filter inlinableHOL)).map Prod.fst) ns prog
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl,
      firstCompileToCrepAllDistinctExact pan_code hdist, rfl, htcode, hlk, hnf⟩

/-- Exact HOL `state_rel_imp_semantics_decls` (`pan_to_crepProofScript.sml:5042-5053`).
    Proof: compose the accepted `state_rel_imp_semantics_decls_to_crep` (at
    `t with code := alist_to_fmap crep_code`) with crep_inline
    `state_rel_imp_semantics`.  This is the same composition as the top-level
    theorem; HOL instead reduces to `state_rel_imp_semantics` via the
    declaration evaluator, which the accepted `_to_crep` theorem already
    covers.  Same statement. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_imp_semantics_decls"
  (fmap_as_finite_support_relation :=
    [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals,
      PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes,
      CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem stateRelImpSemanticsDeclsPanToCrep {width : Nat} {σ : Type} [NeZero width] :
    ∀ (s : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
      (pan_code : List (DeclHOL width)) (start : MlS),
      panToCrepStateRelFiniteExact { s with structs := [] } t ∧
        ((functionsHOL pan_code).map Prod.fst).Nodup ∧
        s.code = HolFiniteMapExact.empty ∧
        t.code = HolFiniteMapExact.empty.updateList (compileProgDeclsHOLW pan_code).reverse ∧
        s.locals = HolFiniteMapExact.empty ∧
        s.eshapes = HolFiniteMapExact.empty ∧
        (∀ entry ∈ functionsHOL pan_code, localisedProgHOL entry.2.2.1 = true) ∧
        pan_code.all (fun x => isFunctionHOL x || isExnDeclHOL x) = true ∧
        sizeOfEidsHOL pan_code < 2 ^ width ∧
        PanSemStateFiniteExact.semanticsDecls s start pan_code ≠ .fail →
      crepSemantics t start = PanSemStateFiniteExact.semanticsDecls s start pan_code := by
  intro s t pan_code start ⟨hsr, hdist, hscode, htcode, hloc, hesh, hlocal, hall, hsize, hfail⟩
  have h1 := stateRelImpSemanticsDeclsToCrep s
    { t with code := HolFiniteMapExact.empty.updateList (compileToCrepExactHOLW pan_code).reverse }
    pan_code start ⟨hsr, hdist, hscode, rfl, hloc, hesh, hlocal, hall, hsize, hfail⟩
  rw [← h1]
  have hnf : crepSemantics
      { t with code := HolFiniteMapExact.empty.updateList (compileToCrepExactHOLW pan_code).reverse }
      start ≠ .fail := by rw [h1]; exact hfail
  rcases hlk : (HolFiniteMapExact.empty.updateList (compileToCrepExactHOLW pan_code).reverse).lookup
      start with _ | ⟨ns, prog⟩
  · exact absurd (crepSemantics_fail_of_lookup_none _ start hlk) hnf
  exact CrepInlineStateRelImpSemantics.stateRelImpSemanticsExact _ t
    (compileToCrepExactHOLW pan_code) start
    ((functionsHOL (pan_code.filter inlinableHOL)).map Prod.fst) ns prog
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl,
      firstCompileToCrepAllDistinctExact pan_code hdist, rfl, htcode, hlk, hnf⟩

end PanToCrepStateRelImpSemanticsTop

end Flapjack
