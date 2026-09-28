import Flapjack.Pancake.CrepToLoop.Proofs.RelationsExact
import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

/-!
# crep_to_loop `comp_exp_preserves_eval`, split by HOL's `eval_ind` cases

Pieces of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
`comp_exp_preserves_eval` (772-1239) over the exact carriers
(bead `flapjack-pxn.18.5.6.33.15`).  HOL proves the theorem by
`ho_match_mp_tac crepSemTheory.eval_ind` and marks its cases with `>~`; each
Lean piece below is one such case, carrying every HOL hypothesis and the HOL
conclusion with the expression fixed to that constructor (plus induction
hypotheses for sub-expressions where the case has any).  HOL's quantifier order
`∀s e v t ctxt tmp l p le ntmp nl` is kept, with the constructor payload in
place of `e`.  `wlab_wloc` is the tagged `wlabWlocExact`; `state_rel`,
`mem_rel`, `globals_rel`, `code_rel` and `locals_rel` are the tagged exact
relations.  The assembling theorem is tracked on bead
`flapjack-pxn.18.5.6.33.15.8`.
-/

namespace Flapjack

/-! Owning carriers of the finite maps the statements traverse; same-module
witnesses for the `fmap_as_finite_support_relation` qualifier. -/
namespace CrepToLoopCompExpPreservesEvalWitnesses

theorem holFmapAsFiniteSupportRelationWitness_CrepToLoopContextExact
    (context : CrepToLoopContextExact) :
    CrepToLoopContextExact.ofBroad (CrepToLoopContextExact.toBroad context) = context :=
  CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CrepSemBroadState.ofBroad_toBroad state

theorem holFmapAsFiniteSupportRelationWitness_LoopSemStateFiniteExact
    {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.LoopEvaluateFiniteSupport.holFmapAsFiniteSupportWitness

end CrepToLoopCompExpPreservesEvalWitnesses

private theorem wlabWlocHOL_eq_exact {width : Nat} [NeZero width] (v : HolWordLab width) :
    wlabWlocHOL v = wlabWlocExact v := by
  cases v; rfl

/-- `comp_exp_preserves_eval`, case `Const w` (`crep_to_loopProofScript.sml:772-786`
    statement; case proof at the `Const w` marker). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_preserves_eval"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_comp_exp_preserves_eval_const {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) [DecidablePred s.memaddrs] (w : BitVec width)
      (v : HolWordLab width) (t : LoopSemStateFiniteExact width σ)
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet),
      evalCrepSemHOLExp s (.const w) = some v ∧
        crepToLoopStateRelExact s t ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        crepToLoopCodeRelExact ctxt s.code t.code ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
        compileExpHOLExact ctxt tmp l (.const w) = (p, le, ntmp, nl) ∧
        ctxt.vmax < tmp →
      ∃ (ck : Nat) (st : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL p)
            { t with clock := t.clock + ck } = (none, st) ∧
        LoopSemStateFiniteExact.eval st le = some (wlabWlocExact v) ∧
        crepToLoopStateRelExact s st ∧
        crepToLoopMemRelHOLExact s.memory st.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals st.globals ∧
        crepToLoopCodeRelExact ctxt s.code st.code ∧
        crepToLoopLocalsRelExact ctxt nl s.locals st.locals := by
  intro s _ w v t ctxt tmp l p le ntmp nl ⟨he, hs, hm, hg, hc, hl, hcomp, _⟩
  simp only [compileExpHOLExact, Prod.mk.injEq] at hcomp
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hcomp
  refine ⟨0, t, by simp [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate], ?_, hs, hm, hg, hc, hl⟩
  simp only [evalCrepSemHOLExp, Option.some.injEq] at he
  subst he
  simp [LoopSemStateFiniteExact.eval, wlabWlocExact]

/-- `comp_exp_preserves_eval`, case `Var vname` (`crep_to_loopProofScript.sml:772-786`
    statement; case proof at the `Var vname` marker). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_preserves_eval"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_comp_exp_preserves_eval_var {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) [DecidablePred s.memaddrs] (vname : Nat)
      (v : HolWordLab width) (t : LoopSemStateFiniteExact width σ)
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet),
      evalCrepSemHOLExp s (.var vname) = some v ∧
        crepToLoopStateRelExact s t ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        crepToLoopCodeRelExact ctxt s.code t.code ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
        compileExpHOLExact ctxt tmp l (.var vname) = (p, le, ntmp, nl) ∧
        ctxt.vmax < tmp →
      ∃ (ck : Nat) (st : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL p)
            { t with clock := t.clock + ck } = (none, st) ∧
        LoopSemStateFiniteExact.eval st le = some (wlabWlocExact v) ∧
        crepToLoopStateRelExact s st ∧
        crepToLoopMemRelHOLExact s.memory st.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals st.globals ∧
        crepToLoopCodeRelExact ctxt s.code st.code ∧
        crepToLoopLocalsRelExact ctxt nl s.locals st.locals := by
  intro s _ vname v t ctxt tmp l p le ntmp nl ⟨he, hs, hm, hg, hc, hl, hcomp, _⟩
  simp only [compileExpHOLExact, Prod.mk.injEq] at hcomp
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hcomp
  refine ⟨0, t, by simp [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate], ?_, hs, hm, hg, hc, hl⟩
  simp only [evalCrepSemHOLExp] at he
  obtain ⟨n, h1, _, h3⟩ := hl.2.2.2 vname v he
  simp [LoopSemStateFiniteExact.eval, h1, h3, wlabWlocHOL_eq_exact]

/-- `comp_exp_preserves_eval`, case `LoadGlob gadr` (`crep_to_loopProofScript.sml:772-786`
    statement; case proof at the `LoadGlob gadr` marker). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_preserves_eval"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_comp_exp_preserves_eval_loadGlob {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) [DecidablePred s.memaddrs] (gadr : BitVec 5)
      (v : HolWordLab width) (t : LoopSemStateFiniteExact width σ)
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet),
      evalCrepSemHOLExp s (.loadGlob gadr) = some v ∧
        crepToLoopStateRelExact s t ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        crepToLoopCodeRelExact ctxt s.code t.code ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
        compileExpHOLExact ctxt tmp l (.loadGlob gadr) = (p, le, ntmp, nl) ∧
        ctxt.vmax < tmp →
      ∃ (ck : Nat) (st : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL p)
            { t with clock := t.clock + ck } = (none, st) ∧
        LoopSemStateFiniteExact.eval st le = some (wlabWlocExact v) ∧
        crepToLoopStateRelExact s st ∧
        crepToLoopMemRelHOLExact s.memory st.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals st.globals ∧
        crepToLoopCodeRelExact ctxt s.code st.code ∧
        crepToLoopLocalsRelExact ctxt nl s.locals st.locals := by
  intro s _ gadr v t ctxt tmp l p le ntmp nl ⟨he, hs, hm, hg, hc, hl, hcomp, _⟩
  simp only [compileExpHOLExact, Prod.mk.injEq] at hcomp
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hcomp
  refine ⟨0, t, by simp [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate], ?_, hs, hm, hg, hc, hl⟩
  simp only [evalCrepSemHOLExp] at he
  simp [LoopSemStateFiniteExact.eval, hg gadr v he]

/-- `comp_exp_preserves_eval`, case `BaseAddr` (`crep_to_loopProofScript.sml:772-786`
    statement; case proof at the `BaseAddr` marker). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_preserves_eval"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_comp_exp_preserves_eval_baseAddr {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) [DecidablePred s.memaddrs]
      (v : HolWordLab width) (t : LoopSemStateFiniteExact width σ)
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet),
      evalCrepSemHOLExp s (.baseAddr) = some v ∧
        crepToLoopStateRelExact s t ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        crepToLoopCodeRelExact ctxt s.code t.code ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
        compileExpHOLExact ctxt tmp l (.baseAddr) = (p, le, ntmp, nl) ∧
        ctxt.vmax < tmp →
      ∃ (ck : Nat) (st : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL p)
            { t with clock := t.clock + ck } = (none, st) ∧
        LoopSemStateFiniteExact.eval st le = some (wlabWlocExact v) ∧
        crepToLoopStateRelExact s st ∧
        crepToLoopMemRelHOLExact s.memory st.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals st.globals ∧
        crepToLoopCodeRelExact ctxt s.code st.code ∧
        crepToLoopLocalsRelExact ctxt nl s.locals st.locals := by
  intro s _ v t ctxt tmp l p le ntmp nl ⟨he, hs, hm, hg, hc, hl, hcomp, _⟩
  simp only [compileExpHOLExact, Prod.mk.injEq] at hcomp
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hcomp
  refine ⟨0, t, by simp [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate], ?_, hs, hm, hg, hc, hl⟩
  simp only [evalCrepSemHOLExp, Option.some.injEq] at he
  subst he
  simp [LoopSemStateFiniteExact.eval, wlabWlocExact, hs.2.2.2.2.2.1]

/-- `comp_exp_preserves_eval`, case `TopAddr` (`crep_to_loopProofScript.sml:772-786`
    statement; case proof at the `TopAddr` marker). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_preserves_eval"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_comp_exp_preserves_eval_topAddr {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) [DecidablePred s.memaddrs]
      (v : HolWordLab width) (t : LoopSemStateFiniteExact width σ)
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet),
      evalCrepSemHOLExp s (.topAddr) = some v ∧
        crepToLoopStateRelExact s t ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        crepToLoopCodeRelExact ctxt s.code t.code ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
        compileExpHOLExact ctxt tmp l (.topAddr) = (p, le, ntmp, nl) ∧
        ctxt.vmax < tmp →
      ∃ (ck : Nat) (st : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL p)
            { t with clock := t.clock + ck } = (none, st) ∧
        LoopSemStateFiniteExact.eval st le = some (wlabWlocExact v) ∧
        crepToLoopStateRelExact s st ∧
        crepToLoopMemRelHOLExact s.memory st.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals st.globals ∧
        crepToLoopCodeRelExact ctxt s.code st.code ∧
        crepToLoopLocalsRelExact ctxt nl s.locals st.locals := by
  intro s _ v t ctxt tmp l p le ntmp nl ⟨he, hs, hm, hg, hc, hl, hcomp, _⟩
  simp only [compileExpHOLExact, Prod.mk.injEq] at hcomp
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hcomp
  refine ⟨0, t, by simp [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate], ?_, hs, hm, hg, hc, hl⟩
  simp only [evalCrepSemHOLExp, Option.some.injEq] at he
  subst he
  simp [LoopSemStateFiniteExact.eval, wlabWlocExact, hs.2.2.2.2.2.2]

end Flapjack
