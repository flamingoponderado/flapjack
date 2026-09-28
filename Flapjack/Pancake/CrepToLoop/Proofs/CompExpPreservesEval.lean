import Flapjack.Pancake.CrepToLoop.Proofs.RelationsExact
import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate
import Flapjack.Pancake.Semantics.LoopProps.EvalExact
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqExact
import Flapjack.Pancake.Semantics.ByteAlignBridge
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpOutRel

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

/-- Flapjack-only abbreviation (no HOL declaration) of the
    `comp_exp_preserves_eval` statement at a fixed source state `s` and
    expression `e`, i.e. the `eval_ind` induction hypothesis HOL's case proofs
    receive for a sub-expression.  Only used as an antecedent of the case
    pieces; every piece states its own conclusion in full. -/
def crepToLoopCompExpPreservesEvalAt {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) [DecidablePred s.memaddrs] (e : CrepExpHOL width) : Prop :=
  ∀ (v : HolWordLab width) (t : LoopSemStateFiniteExact width σ)
    (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
    (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet),
    evalCrepSemHOLExp s e = some v ∧
      crepToLoopStateRelExact s t ∧
      crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
      crepToLoopCodeRelExact ctxt s.code t.code ∧
      crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
      compileExpHOLExact ctxt tmp l e = (p, le, ntmp, nl) ∧
      ctxt.vmax < tmp →
    ∃ (ck : Nat) (st : LoopSemStateFiniteExact width σ),
      LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL p)
          { t with clock := t.clock + ck } = (none, st) ∧
      LoopSemStateFiniteExact.eval st le = some (wlabWlocExact v) ∧
      crepToLoopStateRelExact s st ∧
      crepToLoopMemRelHOLExact s.memory st.memory s.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s.globals st.globals ∧
      crepToLoopCodeRelExact ctxt s.code st.code ∧
      crepToLoopLocalsRelExact ctxt nl s.locals st.locals

/-- `comp_exp_preserves_eval`, case `Load e` (`crep_to_loopProofScript.sml:772-786`
    statement; case proof at 982-995), with the `eval_ind` hypothesis for the
    address sub-expression `e`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_preserves_eval"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_comp_exp_preserves_eval_load {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) [DecidablePred s.memaddrs] (e : CrepExpHOL width),
      crepToLoopCompExpPreservesEvalAt s e →
    ∀ (v : HolWordLab width) (t : LoopSemStateFiniteExact width σ)
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet),
      evalCrepSemHOLExp s (.load e) = some v ∧
        crepToLoopStateRelExact s t ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        crepToLoopCodeRelExact ctxt s.code t.code ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
        compileExpHOLExact ctxt tmp l (.load e) = (p, le, ntmp, nl) ∧
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
  intro s _ e ih v t ctxt tmp l p le ntmp nl ⟨he, hs, hm, hg, hc, hl, hcomp, hv⟩
  cases hea : evalCrepSemHOLExp s e with
  | none => simp [evalCrepSemHOLExp, hea] at he
  | some a =>
    cases a with
    | word w =>
      simp only [evalCrepSemHOLExp, hea] at he
      by_cases hd : s.memaddrs w
      · simp [hd] at he
        subst he
        rcases hA : compileExpHOLExact ctxt tmp l e with ⟨c, val, m, o⟩
        rw [compileExpHOLExact, hA] at hcomp
        simp only [Prod.mk.injEq] at hcomp
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hcomp
        obtain ⟨ck, st, h1, h2, h3, h4, h5, h6, h7⟩ :=
          ih (.word w) t ctxt tmp l c val m o ⟨hea, hs, hm, hg, hc, hl, hA, hv⟩
        refine ⟨ck, st, h1, ?_, h3, h4, h5, h6, h7⟩
        have hdom : st.mdomain w = true := (congrFun h3.1 w) ▸ hd
        simp only [LoopSemStateFiniteExact.eval, h2, wlabWlocExact,
          LoopSemStateFiniteExact.memLoad, hdom, if_true]
        exact congrArg some (h4 w hd).symm
      · simp [if_neg hd] at he

/-- Flapjack bridge (no HOL declaration; HOL's LoadByte case unfolds
    `panSem$mem_load_byte_def` and `wordSem$mem_load_byte_aux_def` inline): under
    `mem_rel` and the `state_rel` domain equation, a Crep byte load succeeds on
    the Loop side with the same byte, widened identically. -/
private theorem memLoadByte_bridge {width : Nat} [NeZero width]
    (smem : BitVec width → HolWordLab width) (dom : BitVec width → Prop) [DecidablePred dom]
    (tmem : BitVec width → WordLocW width) (tdom : BitVec width → Bool)
    (be : Bool) (a : BitVec width) (byte : UInt8)
    (hdom : dom = fun x => tdom x = true) (hm : crepToLoopMemRelHOLExact smem tmem dom)
    (h : panMemLoadByteHOL smem dom be a = some byte) :
    ∃ b, memLoadByteAuxExact tmem tdom be a = some b ∧
      b.setWidth width = BitVec.ofNat width byte.toNat := by
  unfold panMemLoadByteHOL at h
  cases hv : smem (panByteAlignHOL a) with
  | word val =>
    simp only [hv] at h
    by_cases hd : dom (panByteAlignHOL a)
    · rw [if_pos hd, Option.some.injEq] at h
      subst h
      have hmv := hm _ hd
      rw [hv] at hmv
      have htd : tdom (panByteAlignHOL a) = true := by subst hdom; exact hd
      refine ⟨getByteHOL8 a val be, ?_, ?_⟩
      · unfold memLoadByteAuxExact
        rw [riscvByteAlignHOL_eq_panByteAlignHOL, ← hmv]
        simp [wlabWlocExact, htd]
      · rw [panGetByteHOL_eq_riscvGetByteHOL]
        apply BitVec.eq_of_toNat_eq
        simp [getByteHOL8, riscvGetByteHOL, byteIndexHOL]
    · rw [if_neg hd] at h
      cases h

/-- Flapjack helper (no HOL declaration): HOL's LoadByte/Load32 cases close the
    `domain l ⊆ domain t_locals` conjunct under `insert tmp' () l` with
    `SUBSET_INSERT_RIGHT`; this is that step for the exact `locals_rel`. -/
private theorem locals_rel_insert_domain {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (o : NumSet)
    (sl : HolFiniteMapExact Nat (HolWordLab width)) (tl : Spt (WordLocW width)) (m : Nat)
    (h : crepToLoopLocalsRelExact ctxt o sl tl) (hm : sptMem m tl) :
    crepToLoopLocalsRelExact ctxt (sptInsert m () o) sl tl := by
  refine ⟨h.1, h.2.1, fun k hk => ?_, fun vn val hv => ?_⟩
  · rcases (sptMem_sptInsert k m () o).mp hk with rfl | hk
    · exact hm
    · exact h.2.2.1 k hk
  · obtain ⟨n, h1, h2, h3⟩ := h.2.2.2 vn val hv
    exact ⟨n, h1, (sptMem_sptInsert n m () o).mpr (Or.inr h2), h3⟩

/-- `comp_exp_preserves_eval`, case `LoadByte e` (`crep_to_loopProofScript.sml:772-786`
    statement; case proof at 996-1035), with the `eval_ind` hypothesis for the
    address sub-expression `e`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_preserves_eval"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_comp_exp_preserves_eval_loadByte {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) [DecidablePred s.memaddrs] (e : CrepExpHOL width),
      crepToLoopCompExpPreservesEvalAt s e →
    ∀ (v : HolWordLab width) (t : LoopSemStateFiniteExact width σ)
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet),
      evalCrepSemHOLExp s (.loadByte e) = some v ∧
        crepToLoopStateRelExact s t ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        crepToLoopCodeRelExact ctxt s.code t.code ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
        compileExpHOLExact ctxt tmp l (.loadByte e) = (p, le, ntmp, nl) ∧
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
  intro s _ e ih v t ctxt tmp l p le ntmp nl ⟨he, hs, hm, hg, hc, hl, hcomp, hv⟩
  cases hea : evalCrepSemHOLExp s e with
  | none => simp [evalCrepSemHOLExp, hea] at he
  | some a =>
    cases a with
    | word w =>
      cases hb : panMemLoadByteHOL s.memory s.memaddrs s.be w with
      | none => simp [evalCrepSemHOLExp, hea, hb] at he
      | some byte =>
        have hv' : v = .word (BitVec.ofNat width byte.toNat) := by
          simp [evalCrepSemHOLExp, hea, hb] at he; exact he.symm
        subst hv'
        rcases hA : compileExpHOLExact ctxt tmp l e with ⟨c, val, m, o⟩
        have hout := (compileExpHOLExact_out_rel ctxt tmp l e).2.1
        rw [hA] at hout
        rw [compileExpHOLExact, hA] at hcomp
        simp only [Prod.mk.injEq] at hcomp
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hcomp
        obtain ⟨ck, st, h1, h2, h3, h4, h5, h6, h7⟩ :=
          ih (.word w) t ctxt tmp l c val m o ⟨hea, hs, hm, hg, hc, hl, hA, hv⟩
        obtain ⟨b, hbl, hbw⟩ :=
          memLoadByte_bridge s.memory s.memaddrs st.memory st.mdomain s.be w byte h3.1 h4 hb
        rw [h3.2.2.2.1] at hbl
        have hvm : ctxt.vmax < m := Nat.lt_of_lt_of_le hv hout
        refine ⟨ck, LoopSemStateFiniteExact.setVar m (.word (b.setWidth width))
            (LoopSemStateFiniteExact.setVar m (.word w) st), ?_, ?_, h3, h4, h5, h6, ?_⟩
        · rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none c _ st _ h1]
          simp [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq,
            LoopSemStateFiniteExact.evaluate, h2, LoopSemStateFiniteExact.setVar, wlabWlocExact,
            sptLookup_sptInsert, hbl]
        · simp [LoopSemStateFiniteExact.eval, LoopSemStateFiniteExact.setVar,
            sptLookup_sptInsert, wlabWlocExact, hbw]
        · refine locals_rel_insert_domain ctxt o s.locals _ m
            (crepToLoopLocalsRelExact_insert_gt_vmax ctxt o s.locals _ m _
              (crepToLoopLocalsRelExact_insert_gt_vmax ctxt o s.locals _ m _ h7 hvm) hvm) ?_
          simp [sptMem, sptDomain, LoopSemStateFiniteExact.setVar,
            sptLookup_sptInsert]

end Flapjack
