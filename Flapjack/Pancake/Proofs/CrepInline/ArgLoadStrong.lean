import Flapjack.Pancake.Proofs.CrepInline.NestedDecsSublocals

/-!
# crep_inline general argument-load strong correctness

Counterpart of crep_inlineProofScript.sml:1223-1287. The proof composes the
reviewed sublocals declaration theorem twice: the inner block starts with
`t` extended by temporary bindings, and the outer block starts with the
original caller. Both runs and the FDIFF preservation are derived internally.
-/

namespace Flapjack.CrepInlineExact

namespace ArgLoadStrongSupport
/-- Canonical carrier roundtrip re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end ArgLoadStrongSupport

/-- Exact strong argument-load theorem with HOL's continuing-result guard. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "general_simulate_arg_load_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code, t])
  (words_as_type_indexed_bitvec)]
theorem generalSimulateArgLoadStrongExact {width : Nat} [NeZero width] {σ : Type}
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
        (match (generalizing := false) r with
         | none => True
         | some (.break _) => True
         | some (.continue _) => True
         | _ => False) ∧
        tmp_vars.Nodup ∧ tmp_vars.length = vs.length ∧
        (∀ x, x ∈ tmp_vars → x ∉ vs) ∧
        (∀ x, x ∈ tmp_vars → x ∉ (es.map crepExpVarsHOL).flatten) →
      ∃ t', evalCrepSemHOLProgExact s
          (nestedDecsHOL tmp_vars es (nestedDecsHOL vs (tmp_vars.map CrepExpHOL.var) p)) =
          (r, t') ∧
        crepInlineStateRelExact s' t' ∧
        crepHolSubmap (crepHolFdiff s.locals.lookup (crepHolFdom t.lookup)) t'.locals.lookup := by
  classical
  intro ⟨hes, hlen, hnd, hsub, hev, hfresh, hcont, htnd, htlen, hdisj, hfree⟩
  let middle : CrepSemHOLState width σ := {s with locals := t.updateListEq (tmp_vars.zip vals)}
  have hbase : t.submap middle.locals :=
    CrepInlineUpdateListLocals.submapDiffListExact t tmp_vars vals (by omega) htnd
      (fun v hv => hfresh v (Or.inr hv))
  have hvals : (tmp_vars.map CrepExpHOL.var).mapM (evalCrepSemHOLExp middle) = some vals := by
    rw [← lookupLocalsEqMapVarsHOL tmp_vars middle]
    exact CrepInlineTransformEoc.mapM_updateListEq_zip t tmp_vars vals htnd (by omega)
  have hrun : evalCrepSemHOLProgExact {middle with locals := t.updateListEq (vs.zip vals)} p =
      (r, s') := hev
  obtain ⟨u, hu, hrel, _⟩ := nestedDecsEvaluateSublocalsStrongExact vs
    (tmp_vars.map CrepExpHOL.var) p middle r s' vals t
    ⟨hvals, by simp; omega, hnd,
      (fun v hv e he => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
        simp only [crepExpVarsHOL, List.mem_singleton]
        rintro rfl
        exact hdisj v hx hv),
      (fun v hv => hfresh v (Or.inl hv)), hrun, hbase, hcont⟩
  have hlenes : tmp_vars.length = es.length := by
    have := opt_mmap_length_eq es (evalCrepSemHOLExp s) vals hes
    omega
  obtain ⟨target, htarget, hrel2, hdiff⟩ := nestedDecsEvaluateSublocalsStrongExact tmp_vars es
    (nestedDecsHOL vs (tmp_vars.map CrepExpHOL.var) p) s r u vals t
    ⟨hes, hlenes, htnd,
      (fun v hv e he hm => hfree v hv (List.mem_flatten.2
        ⟨_, List.mem_map.2 ⟨e, he, rfl⟩, hm⟩)),
      (fun v hv => hfresh v (Or.inr hv)), hu, hsub, hcont⟩
  refine ⟨target, htarget, ?_, hdiff⟩
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10⟩ := hrel
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10⟩ := hrel2
  exact ⟨a1.trans b1,a2.trans b2,a3.trans b3,a4.trans b4,a5.trans b5,
    a6.trans b6,a7.trans b7,a8.trans b8,a9.trans b9,a10.trans b10⟩

/-- HOL's conjunction of the strong FDIFF result and restored-locals result.
All eleven guards remain those of the original theorem (1288-1319). The two
accepted predecessor theorems produce the same deterministic evaluator run;
projection of the result-pair equality identifies their existential states.
No target evaluation or post-state relation is assumed. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "general_simulate_arg_load_strong_1"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code, t])
  (words_as_type_indexed_bitvec)]
theorem generalSimulateArgLoadStrong1Exact {width : Nat} [NeZero width] {σ : Type}
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
        (match (generalizing := false) r with
         | none => True
         | some (.break _) => True
         | some (.continue _) => True
         | _ => False) ∧
        tmp_vars.Nodup ∧ tmp_vars.length = vs.length ∧
        (∀ x, x ∈ tmp_vars → x ∉ vs) ∧
        (∀ x, x ∈ tmp_vars → x ∉ (es.map crepExpVarsHOL).flatten) →
      ∃ t', evalCrepSemHOLProgExact s
          (nestedDecsHOL tmp_vars es (nestedDecsHOL vs (tmp_vars.map CrepExpHOL.var) p)) =
          (r, t') ∧
        crepInlineStateRelExact s' t' ∧
        crepHolSubmap (crepHolFdiff s.locals.lookup (crepHolFdom t.lookup)) t'.locals.lookup ∧
        ((vs.zip (vs.map (fun n => s.locals.lookup n))).foldl
          HolFiniteMapExact.resVarEq s'.locals).submap t'.locals := by
  intro h
  obtain ⟨u, hu, hrel, hdiff⟩ :=
    generalSimulateArgLoadStrongExact s es vals vs t p r s' tmp_vars h
  obtain ⟨v, hv, _, hrestore⟩ :=
    generalSimulateArgLoadPreserveLocalsExact s es vals vs t p r s' tmp_vars h
  have huv : u = v := congrArg Prod.snd (hu.symm.trans hv)
  cases huv
  exact ⟨u, hu, hrel, hdiff, hrestore⟩

end Flapjack.CrepInlineExact
