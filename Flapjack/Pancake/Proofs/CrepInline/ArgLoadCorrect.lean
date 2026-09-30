import Flapjack.Pancake.Proofs.CrepInline.ArgLoadStrong

namespace Flapjack.CrepInlineExact

namespace ArgLoadCorrectSupport
/-- Same-module canonical carrier roundtrip for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end ArgLoadCorrectSupport

/-- Exact HOL arg_load_correct: the definition is the two unchanged nested
declaration blocks, so accepted strong_all supplies the existential run and
result-sensitive locals facts. No successful target evaluation is assumed. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "arg_load_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code, t])
  (words_as_type_indexed_bitvec)]
theorem argLoadCorrectExact {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (es : List (CrepExpHOL width))
    (vals : List (HolWordLab width)) (vs : List Nat)
    (t : HolFiniteMapExact Nat (HolWordLab width)) (p : CrepProgHOL width)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (tmp_vars : List Nat) :
      es.mapM (evalCrepSemHOLExp s) = some vals ∧
        vs.length = vals.length ∧
        vs.Nodup ∧
        t.submap s.locals ∧
        evalCrepSemHOLProgExact { s with locals := t.updateListEq (vs.zip vals) } p = (r, s') ∧
        (∀ v, v ∈ vs ∨ v ∈ tmp_vars → crepHolFdom t.lookup v = false) ∧
        r ≠ some .error ∧
        tmp_vars.Nodup ∧ tmp_vars.length = vs.length ∧
        (∀ x, x ∈ tmp_vars → x ∉ vs) ∧
        (∀ x, x ∈ tmp_vars → x ∉ (es.map crepExpVarsHOL).flatten) →
      ∃ t', evalCrepSemHOLProgExact s
          (argLoadHOLExact tmp_vars es vs p) =
          (r, t') ∧
        crepInlineStateRelExact s' t' ∧
        (match (generalizing := false) r with
         | none =>
             crepHolSubmap (crepHolFdiff s.locals.lookup (crepHolFdom t.lookup)) t'.locals.lookup ∧
             ((vs.zip (vs.map (fun n => s.locals.lookup n))).foldl
               HolFiniteMapExact.resVarEq s'.locals).submap t'.locals
         | some (.break _) =>
             crepHolSubmap (crepHolFdiff s.locals.lookup (crepHolFdom t.lookup)) t'.locals.lookup ∧
             ((vs.zip (vs.map (fun n => s.locals.lookup n))).foldl
               HolFiniteMapExact.resVarEq s'.locals).submap t'.locals
         | some (.continue _) =>
             crepHolSubmap (crepHolFdiff s.locals.lookup (crepHolFdom t.lookup)) t'.locals.lookup ∧
             ((vs.zip (vs.map (fun n => s.locals.lookup n))).foldl
               HolFiniteMapExact.resVarEq s'.locals).submap t'.locals
         | some .error => False
         | _ => True) := by
  intro h
  obtain ⟨u, hu, hrel, hcase⟩ :=
    generalSimulateArgLoadStrongAllExact s es vals vs t p r s' tmp_vars h
  refine ⟨u, ?_, hrel, ?_⟩
  · simpa only [argLoadHOLExact] using hu
  · cases r with
    | none => exact hcase
    | some result => cases result <;> exact hcase

end Flapjack.CrepInlineExact
