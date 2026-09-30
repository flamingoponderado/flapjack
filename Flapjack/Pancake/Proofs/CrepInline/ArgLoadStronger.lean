import Flapjack.Pancake.Proofs.CrepInline.ArgLoadCorrect

namespace Flapjack.CrepInlineExact

namespace ArgLoadStrongerSupport
/-- Same-module canonical carrier roundtrip for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end ArgLoadStrongerSupport

/-- Flapjack-specific pointwise restriction support for the stronger proof.
This is the lookup-function specialization of the finite-map argument, rather
than a separate port of HOL's unrestricted EQ_FDOM_SUBMAP declaration. -/
private theorem restrictedEqOfSubmapFdom {β : Type}
    (left right : Nat → Option β) (mask : Nat → Bool)
    (hsub : crepHolSubmap (crepHolFdiff left mask) right)
    (hdom : crepHolFdom left = crepHolFdom right) :
    crepHolFdiff left mask = crepHolFdiff right mask := by
  funext key
  by_cases hm : mask key = true
  · simp only [crepHolFdiff, hm, if_true]
  · simp only [crepHolFdiff, if_neg hm]
    cases hl : left key with
    | some value =>
        exact (hsub key value (by simp only [crepHolFdiff, if_neg hm, hl])).symm
    | none =>
        have hd := congrFun hdom key
        cases hr : right key with
        | none => rfl
        | some value => simp [crepHolFdom, hl, hr] at hd

/-- Original arg_load_stronger: accepted arg_load_correct supplies the run;
the original continuing-result domain theorem upgrades the outside-map submap
to equality. All guards and restored-local facts remain unchanged. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "arg_load_stronger"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code, t])
  (words_as_type_indexed_bitvec)]
theorem argLoadStrongerExact {width : Nat} [NeZero width] {σ : Type}
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
             crepHolFdiff s.locals.lookup (crepHolFdom t.lookup) =
               crepHolFdiff t'.locals.lookup (crepHolFdom t.lookup) ∧
             ((vs.zip (vs.map (fun n => s.locals.lookup n))).foldl
               HolFiniteMapExact.resVarEq s'.locals).submap t'.locals
         | some (.break _) =>
             crepHolFdiff s.locals.lookup (crepHolFdom t.lookup) =
               crepHolFdiff t'.locals.lookup (crepHolFdom t.lookup) ∧
             ((vs.zip (vs.map (fun n => s.locals.lookup n))).foldl
               HolFiniteMapExact.resVarEq s'.locals).submap t'.locals
         | some (.continue _) =>
             crepHolFdiff s.locals.lookup (crepHolFdom t.lookup) =
               crepHolFdiff t'.locals.lookup (crepHolFdom t.lookup) ∧
             ((vs.zip (vs.map (fun n => s.locals.lookup n))).foldl
               HolFiniteMapExact.resVarEq s'.locals).submap t'.locals
         | some .error => False
         | _ => True) := by
  intro h
  obtain ⟨u, hu, hrel, hcase⟩ := argLoadCorrectExact s es vals vs t p r s' tmp_vars h
  refine ⟨u, hu, hrel, ?_⟩
  have strengthen
      (hr : r = none ∨ (∃ n, r = some (.break n)) ∨ (∃ n, r = some (.continue n)))
      (hs : crepHolSubmap (crepHolFdiff s.locals.lookup (crepHolFdom t.lookup)) u.locals.lookup) :
      crepHolFdiff s.locals.lookup (crepHolFdom t.lookup) =
        crepHolFdiff u.locals.lookup (crepHolFdom t.lookup) := by
    exact restrictedEqOfSubmapFdom _ _ _ hs
      (evaluateLocalsSameFdom'Exact (argLoadHOLExact tmp_vars es vs p) s r u ⟨hu, hr⟩)
  cases r with
  | none => exact ⟨strengthen (Or.inl rfl) hcase.1, hcase.2⟩
  | some result =>
      cases result with
      | «break» n => exact ⟨strengthen (Or.inr (Or.inl ⟨n, rfl⟩)) hcase.1, hcase.2⟩
      | «continue» n => exact ⟨strengthen (Or.inr (Or.inr ⟨n, rfl⟩)) hcase.1, hcase.2⟩
      | error => exact hcase
      | _ => trivial

end Flapjack.CrepInlineExact
