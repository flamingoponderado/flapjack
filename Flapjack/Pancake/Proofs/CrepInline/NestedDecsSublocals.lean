import Flapjack.Pancake.Proofs.CrepInline.ArgLoad

/-!
# crep_inline `nested_decs_evaluate_sublocals_strong`

Counterpart of `cakeml/pancake/proofs/crep_inlineProofScript.sml:907-981`
(bead `flapjack-pxn.18.5.5.44.5`).  `FDIFF s.locals (FDOM t) SUBMAP t'.locals`
is `crepHolSubmap (crepHolFdiff s.locals.lookup (crepHolFdom t.lookup))
t'.locals.lookup`, the rendering used by the other crep_inline ports; `v ∉ FDOM
t` is `crepHolFdom t.lookup v = false`.  The proof is a pointwise version of
HOL's, from the same lemmas (`evaluate_state_locals_rel_strong`,
`evaluate_nested_decs_locals_nested_res_var`, `evaluate_locals_same_fdom'`).
-/

namespace Flapjack.CrepInlineExact

namespace NestedDecsSublocalsSupport
/-- Canonical carrier roundtrip re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end NestedDecsSublocalsSupport

/-- Exact HOL `nested_decs_evaluate_sublocals_strong`
    (`crep_inlineProofScript.sml:907-981`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "nested_decs_evaluate_sublocals_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code, t])
  (words_as_type_indexed_bitvec)]
theorem nestedDecsEvaluateSublocalsStrongExact {width : Nat} [NeZero width] {σ : Type}
    (vs : List Nat) (es : List (CrepExpHOL width)) (p : CrepProgHOL width)
    (s : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width))
    (s' : CrepSemHOLState width σ) (vals : List (HolWordLab width))
    (t : HolFiniteMapExact Nat (HolWordLab width)) :
      es.mapM (evalCrepSemHOLExp s) = some vals ∧
        vs.length = es.length ∧
        vs.Nodup ∧
        (∀ v, v ∈ vs → ∀ e, e ∈ es → v ∉ crepExpVarsHOL e) ∧
        (∀ v, v ∈ vs → crepHolFdom t.lookup v = false) ∧
        evalCrepSemHOLProgExact { s with locals := t.updateListEq (vs.zip vals) } p = (r, s') ∧
        t.submap s.locals ∧
        (match (generalizing := false) r with
         | none => True
         | some (.break _) => True
         | some (.continue _) => True
         | _ => False) →
      ∃ t', evalCrepSemHOLProgExact s (nestedDecsHOL vs es p) = (r, t') ∧
        crepInlineStateRelExact s' t' ∧
        crepHolSubmap (crepHolFdiff s.locals.lookup (crepHolFdom t.lookup)) t'.locals.lookup := by
  classical
  intro ⟨hes, hlen, hnd, hfresh, hdomt, hev, hsub, hcont⟩
  have hdisj3 : r = none ∨ (∃ n, r = some (.break n)) ∨ (∃ n, r = some (.continue n)) := by
    rcases r with _ | ⟨_ | _ | n | n | vs | ex | ev⟩ <;> first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl ⟨_, rfl⟩)
      | exact Or.inr (Or.inr ⟨_, rfl⟩)
      | exact hcont.elim
  have hne : r ≠ some .error := by rintro rfl; simp at hdisj3
  have hlk : ∀ (m : HolFiniteMapExact Nat (HolWordLab width)) (k : Nat),
      k ∉ vs → (m.updateListEq (vs.zip vals)).lookup k = m.lookup k := by
    intro m k hk
    rw [HolFiniteMapExact.lookup_updateListEq]
    apply FLOOKUP_FUPDATE_LIST_HOL_not_mem
    intro hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
    exact hk (List.of_mem_zip he).1
  have hsub1 : (t.updateListEq (vs.zip vals)).submap (s.locals.updateListEq (vs.zip vals)) := by
    intro k v hk
    simp only [HolFiniteMapExact.lookup_updateListEq] at hk ⊢
    exact submap_updateList _ _ _ hsub k v hk
  obtain ⟨u, hevu, hrelu, hpost⟩ := evaluateStateLocalsRelStrongExact p _ r s'
    { s with locals := s.locals.updateListEq (vs.zip vals) } ⟨hev, hne, hsub1, ⟨rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  have hext : crepInlineLocalsExtRelExact { s with locals := t.updateListEq (vs.zip vals) } s'
      { s with locals := s.locals.updateListEq (vs.zip vals) } u := by
    rcases hdisj3 with rfl | ⟨n, rfl⟩ | ⟨n, rfl⟩ <;> exact hpost.2
  have hlenv : vs.length = vals.length := by
    have := opt_mmap_length_eq es (evalCrepSemHOLExp s) vals hes
    omega
  obtain ⟨t', hevt, hrelt, ht'⟩ := evaluateNestedDecsLocalsNestedResVarExact vs es p s r u vals
    hes hlen hnd hfresh hevu
  refine ⟨t', hevt, stateRel_trans hrelu hrelt, ?_⟩
  intro k v hk
  simp only [crepHolFdiff] at hk
  by_cases htk : crepHolFdom t.lookup k = true
  · simp [htk] at hk
  · simp only [htk, Bool.false_eq_true, if_false] at hk
    rw [ht']
    by_cases hkv : k ∈ vs
    · rw [flookup_res_var_is_mem_zip_eq_exact vs k u.locals s.locals hkv]; exact hk
    · have hlenm : vs.length = (vs.map fun n => s.locals.lookup n).length := by simp
      rw [flookupResVarDistinctZipEqHOL vs _ u.locals k ⟨hlenm, hkv⟩]
      have hx := congrFun hext k
      have hdom := congrFun (evaluateLocalsSameFdom'Exact p _ r s' ⟨hev, hdisj3⟩) k
      have hd0 : crepHolFdom (t.updateListEq (vs.zip vals)).lookup k = false := by
        simp only [crepHolFdom] at htk ⊢
        rw [hlk _ _ hkv]
        simpa using htk
      simp only [crepHolFdiff] at hx
      rw [hd0, ← hdom, hd0] at hx
      simp only [Bool.false_eq_true, if_false] at hx
      rw [← hx, hlk _ _ hkv]
      exact hk

end Flapjack.CrepInlineExact
