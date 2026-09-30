import Flapjack.Pancake.Proofs.CrepInline.EvaluateStateLocals.Assembly
import Flapjack.Pancake.Proofs.CrepInline.NestedDecs
import Flapjack.Pancake.Proofs.CrepInline.UpdateListLocals
import Flapjack.Pancake.Proofs.CrepInline.TransformEoc.Call

/-!
# crep_inline `general_simulate_arg_load_correct`

Counterpart of `cakeml/pancake/proofs/crep_inlineProofScript.sml:985-1060`
(bead `flapjack-pxn.18.5.5.45.1`).  As in HOL, the proof moves the run of `p`
from `t |++ ZIP (vs, vals)` to `s.locals |++ ZIP (tmp_vars, vals) |++ ZIP (vs,
vals)` by `evaluate_state_locals_rel` twice, then reassembles the two nested
declaration blocks by `nested_decs_evaluate`.  Renderings: `SUBMAP` is
`HolFiniteMapExact.submap`, `v ∉ FDOM t` is `crepHolFdom t.lookup v = false`
(as in the tagged `SUBMAP_DIFF_LIST`), `ALL_DISTINCT` is `List.Nodup`,
`MAP Var` is `List.map CrepExpHOL.var`, `nested_decs` is `nestedDecsHOL`.
-/

namespace Flapjack.CrepInlineExact

namespace ArgLoadSupport
/-- Canonical carrier roundtrip re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end ArgLoadSupport

/-- Local support: `state_rel` is transitive. -/
private theorem stateRel_trans {width : Nat} [NeZero width] {σ : Type}
    {a b c : CrepSemHOLState width σ} (h1 : crepInlineStateRelExact a b)
    (h2 : crepInlineStateRelExact b c) : crepInlineStateRelExact a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := h2
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, a6.trans b6,
    a7.trans b7, a8.trans b8, a9.trans b9, a10.trans b10⟩

/-- Local support: states differing only in locals are `state_rel`-related. -/
private theorem stateRel_withLocals {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (l1 l2 : HolFiniteMapExact Nat (HolWordLab width)) :
    crepInlineStateRelExact { s with locals := l1 } { s with locals := l2 } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact HOL `general_simulate_arg_load_correct` (`crep_inlineProofScript.sml:985-1060`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "general_simulate_arg_load_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code, t])
  (words_as_type_indexed_bitvec)]
theorem generalSimulateArgLoadCorrectExact {width : Nat} [NeZero width] {σ : Type}
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
          (nestedDecsHOL tmp_vars es (nestedDecsHOL vs (tmp_vars.map CrepExpHOL.var) p)) =
          (r, t') ∧
        crepInlineStateRelExact s' t' := by
  classical
  intro ⟨hes, hlen, hnd, hsub, hev, hfresh, hne, htnd, htlen, hdisj, hfree⟩
  -- step 1: t |++ vs ⊑ (t |++ tmp_vars) |++ vs
  have hsub1 : (t.updateListEq (vs.zip vals)).submap
      ((t.updateListEq (tmp_vars.zip vals)).updateListEq (vs.zip vals)) := by
    intro k v hk
    simp only [HolFiniteMapExact.lookup_updateListEq] at hk ⊢
    exact submap_updateList _ _ _
      (CrepInlineUpdateListLocals.submapDiffListExact t tmp_vars vals (by omega) htnd
        (fun v hv => hfresh v (Or.inr hv))) k v hk
  obtain ⟨t1, hev1, hrel1, _⟩ := evaluateStateLocalsRelExact p _ r s'
    { s with locals := (t.updateListEq (tmp_vars.zip vals)).updateListEq (vs.zip vals) } hev hne
    ⟨hsub1, stateRel_withLocals s _ _⟩
  -- step 2: (t |++ tmp_vars) |++ vs ⊑ (s.locals |++ tmp_vars) |++ vs
  have hsub2 : ((t.updateListEq (tmp_vars.zip vals)).updateListEq (vs.zip vals)).submap
      ((s.locals.updateListEq (tmp_vars.zip vals)).updateListEq (vs.zip vals)) := by
    intro k v hk
    simp only [HolFiniteMapExact.lookup_updateListEq] at hk ⊢
    exact submap_updateList _ _ _ (submap_updateList _ _ _ hsub) k v hk
  have hne1 : r ≠ some .error := hne
  obtain ⟨t2, hev2, hrel2, _⟩ := evaluateStateLocalsRelExact p _ r t1
    { s with locals := (s.locals.updateListEq (tmp_vars.zip vals)).updateListEq (vs.zip vals) }
    hev1 hne1 ⟨hsub2, stateRel_withLocals s _ _⟩
  -- step 3: the inner block, at s with locals |++ tmp_vars
  let s1 : CrepSemHOLState width σ := { s with locals := s.locals.updateListEq (tmp_vars.zip vals) }
  have hvals : (tmp_vars.map CrepExpHOL.var).mapM (evalCrepSemHOLExp s1) = some vals := by
    rw [← lookupLocalsEqMapVarsHOL tmp_vars s1]
    exact CrepInlineTransformEoc.mapM_updateListEq_zip s.locals tmp_vars vals htnd (by omega)
  obtain ⟨t3, hev3, hrel3⟩ := nestedDecsEvaluateExact vs (tmp_vars.map CrepExpHOL.var) p s1 r t2 vals
    hvals (by simp; omega) hnd
    (fun v hv e he => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
      simp only [crepExpVarsHOL, List.mem_singleton]
      rintro rfl
      exact hdisj v hx hv)
    hev2 hne
  -- step 4: the outer block, at s
  have hlenes : tmp_vars.length = es.length := by
    have := opt_mmap_length_eq es (evalCrepSemHOLExp s) vals hes
    omega
  obtain ⟨t4, hev4, hrel4⟩ := nestedDecsEvaluateExact tmp_vars es _ s r t3 vals hes hlenes htnd
    (fun v hv e he hm => hfree v hv (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨e, he, rfl⟩, hm⟩))
    hev3 hne
  exact ⟨t4, hev4, stateRel_trans hrel1 (stateRel_trans hrel2 (stateRel_trans hrel3 hrel4))⟩

end Flapjack.CrepInlineExact
