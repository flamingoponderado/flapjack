import Flapjack.Pancake.CrepToLoop.Proofs.RelationsExact
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpOutRel
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpLeTmpDomain
import Flapjack.Pancake.CrepToLoop.Proofs.LoopEvaluateHelpers
import Flapjack.Pancake.Semantics.LoopProps.CompSyntaxOkEvalExact
import Flapjack.Pancake.Semantics.LoopProps.EvalExact
import Flapjack.Pancake.Semantics.LoopProps.UnassignedVarsExact
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

This module currently carries the `Cmp` case only (bead
`flapjack-pxn.18.5.6.33.15.5`); the other `eval_ind` cases are added by their
own beads.  Its declaration is intentionally left untagged until the tagged
`crepSem$eval_def` evaluator interface is exact (bead
`flapjack-pxn.18.5.6.33.15.9`); `open Classical` keeps this case's own type free
of the spurious `DecidablePred` premise meanwhile.
-/

namespace Flapjack

open LoopSemStateFiniteExact

open Classical

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

/-- Flapjack-only abbreviation (no HOL declaration) of the
    `comp_exp_preserves_eval` statement at a fixed source state `s` and
    expression `e`, i.e. the `eval_ind` induction hypothesis HOL's case proofs
    receive for a sub-expression.  Only used as an antecedent of the case
    pieces; every piece states its own conclusion in full. -/
def crepToLoopCompExpPreservesEvalAt {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (e : CrepExpHOL width) : Prop :=
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

/-- Flapjack-only exact counterpart of Cake's
    `eval_some_var_cexp_local_lookup` (`crepPropsScript.sml:835`) over the exact
    `evalCrepSemHOLExp` evaluator and `crepExpVarsHOL`: a successfully evaluated
    source expression binds every variable occurring in it.  This is the
    `var_cexp` premise source for `compile_exp_le_tmp_domain` in the Cmp case. -/
private theorem evalCrepSemHOLExp_exists_locals_of_mem_vars {width : Nat} [NeZero width]
    {σ : Type} (state : CrepSemHOLState width σ) :
    ∀ (expression : CrepExpHOL width) (value : HolWordLab width) (name : Nat),
      evalCrepSemHOLExp state expression = some value →
      name ∈ crepExpVarsHOL expression → ∃ w, state.locals.lookup name = some w := by
  intro expression
  refine CrepExpHOL.rec
    (motive_1 := fun expression =>
      ∀ (value : HolWordLab width) (name : Nat),
        evalCrepSemHOLExp state expression = some value →
        name ∈ crepExpVarsHOL expression → ∃ w, state.locals.lookup name = some w)
    (motive_2 := fun expressions =>
      ∀ (values : List (HolWordLab width)) (name : Nat),
        expressions.mapM (evalCrepSemHOLExp state) = some values →
        name ∈ crepExpVarsHOLList expressions → ∃ w, state.locals.lookup name = some w)
    (fun _ value name _ hmem => by simp [crepExpVarsHOL] at hmem)
    (fun variableName value name heval hmem => by
      simp only [crepExpVarsHOL, List.mem_singleton] at hmem
      subst hmem
      exact ⟨value, by simpa only [evalCrepSemHOLExp] using heval⟩)
    (fun address ih value name heval hmem => by
      have hmem' : name ∈ crepExpVarsHOL address := by simpa [crepExpVarsHOL] using hmem
      cases haddr : evalCrepSemHOLExp state address with
      | none => simp only [evalCrepSemHOLExp, haddr] at heval; simp at heval
      | some a => exact ih a name haddr hmem')
    (fun address ih value name heval hmem => by
      have hmem' : name ∈ crepExpVarsHOL address := by simpa [crepExpVarsHOL] using hmem
      cases haddr : evalCrepSemHOLExp state address with
      | none => simp only [evalCrepSemHOLExp, haddr] at heval; simp at heval
      | some a => exact ih a name haddr hmem')
    (fun address ih value name heval hmem => by
      have hmem' : name ∈ crepExpVarsHOL address := by simpa [crepExpVarsHOL] using hmem
      cases haddr : evalCrepSemHOLExp state address with
      | none => simp only [evalCrepSemHOLExp, haddr] at heval; simp at heval
      | some a => exact ih a name haddr hmem')
    (fun _ value name _ hmem => by simp [crepExpVarsHOL] at hmem)
    (fun _ args ih value name heval hmem => by
      cases hm : args.mapM (evalCrepSemHOLExp state) with
      | none => simp only [evalCrepSemHOLExp, hm] at heval; simp at heval
      | some values => exact ih values name hm hmem)
    (fun _ args ih value name heval hmem => by
      cases hm : args.mapM (evalCrepSemHOLExp state) with
      | none => simp only [evalCrepSemHOLExp, hm] at heval; simp at heval
      | some values => exact ih values name hm hmem)
    (fun _ left right ihl ihr value name heval hmem => by
      rw [crepExpVarsHOL, List.mem_append] at hmem
      rcases hmem with hl | hr
      · cases hleft : evalCrepSemHOLExp state left with
        | none => simp only [evalCrepSemHOLExp, hleft] at heval; simp at heval
        | some lv => exact ihl lv name hleft hl
      · cases hright : evalCrepSemHOLExp state right with
        | none => simp only [evalCrepSemHOLExp, hright] at heval; simp at heval
        | some rv => exact ihr rv name hright hr)
    (fun _ left right ihl ihr value name heval hmem => by
      rw [crepExpVarsHOL, List.mem_append] at hmem
      rcases hmem with hl | hr
      · cases hleft : evalCrepSemHOLExp state left with
        | none => simp only [evalCrepSemHOLExp, hleft] at heval; simp at heval
        | some lv => exact ihl lv name hleft hl
      · cases hright : evalCrepSemHOLExp state right with
        | none => simp only [evalCrepSemHOLExp, hright] at heval; simp at heval
        | some rv => exact ihr rv name hright hr)
    (fun value name _ hmem => by simp [crepExpVarsHOL] at hmem)
    (fun value name _ hmem => by simp [crepExpVarsHOL] at hmem)
    (fun values name hm hmem => by simp [crepExpVarsHOLList] at hmem)
    (fun head tail ihHead ihTail values name hm hmem => by
      simp only [List.mapM_cons] at hm
      cases hhead : evalCrepSemHOLExp state head with
      | none => rw [hhead] at hm; simp at hm
      | some hv =>
        cases htail : tail.mapM (evalCrepSemHOLExp state) with
        | none => rw [hhead, htail] at hm; simp at hm
        | some tvs =>
          obtain rfl : values = hv :: tvs := by
            rw [hhead, htail] at hm
            exact (Option.some.inj hm).symm
          rw [crepExpVarsHOLList, List.mem_append] at hmem
          rcases hmem with hh | ht
          · exact ihHead hv name hhead hh
          · exact ihTail tvs name htail ht)
    expression

/-- `cut_state`'s subset guard for a live set whose only keys outside `locals`
    are the two freshly inserted registers `k₁`/`k₂`. -/
private theorem sptSubsetLive_of_live_insert {α β : Type} {live : Spt α} {locals : Spt β}
    (ka kb : Nat) (va vb : β)
    (h : ∀ n, sptMem n live → n ≠ ka → n ≠ kb → sptMem n locals) :
    sptSubsetLive live (sptInsert ka va (sptInsert kb vb locals)) := by
  intro n hn
  by_cases h1 : n = ka
  · rw [h1]
    exact (sptMem_sptInsert ka ka va (sptInsert kb vb locals)).mpr (Or.inl rfl)
  · by_cases h2 : n = kb
    · rw [h2]
      exact (sptMem_sptInsert kb ka va (sptInsert kb vb locals)).mpr
        (Or.inr ((sptMem_sptInsert kb kb vb locals).mpr (Or.inl rfl)))
    · exact (sptMem_sptInsert n ka va (sptInsert kb vb locals)).mpr
        (Or.inr ((sptMem_sptInsert n kb vb locals).mpr (Or.inr (h n hn h1 h2))))

/-- Flapjack-only evaluation of the `prog_if` tail `[Assign condition le;
    Assign rightRegister re; If ...]` that the `.cmp` compiler emits.  Given the
    two materialized values, the fresh registers distinct, the right value not
    reading `condition`, the live set already contained in the locals, and a
    nonzero clock, it runs to a state whose clock is the input clock minus one
    (the `cut_res` decrement) and whose `condition` local is the observed
    comparison result.  All fields except `locals`/`clock` are untouched. -/
private theorem evaluate_progIfTail {width : Nat} [NeZero width] {σ : Type}
    (operator : Cmp) (condition rightRegister : Nat)
    (leftValue rightValue : HolLoopExp width) (live : NumSet)
    (w1 w2 : BitVec width) (s : LoopSemStateFiniteExact width σ)
    (hcond : condition ≠ rightRegister)
    (hleft : LoopSemStateFiniteExact.eval s leftValue = some (.word w1))
    (hright : LoopSemStateFiniteExact.eval s rightValue = some (.word w2))
    (hnotmem : condition ∉ holLoopLocalsTouched rightValue)
    (hsubmem : ∀ n, sptMem n live → n ≠ condition → n ≠ rightRegister → sptMem n s.locals)
    (hcondmem : sptMem condition live)
    (hclock : s.clock ≠ 0) :
    ∃ st : LoopSemStateFiniteExact width σ,
      LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL
        [HolLoopProg.assign condition leftValue,
         HolLoopProg.assign rightRegister rightValue,
         HolLoopProg.ite operator condition (.reg rightRegister)
           (HolLoopProg.assign condition (.const 1))
           (HolLoopProg.assign condition (.const 0)) live]) s = (none, st) ∧
      LoopSemStateFiniteExact.eval st (.var condition) =
        some (.word (Compiler.Encoders.Asm.wordCmpResultHOL operator w1 w2)) ∧
      st.clock = s.clock - 1 ∧
      st.memory = s.memory ∧ st.mdomain = s.mdomain ∧ st.shMdomain = s.shMdomain ∧
      st.be = s.be ∧ st.ffi = s.ffi ∧ st.baseAddr = s.baseAddr ∧
      st.topAddr = s.topAddr ∧ st.code = s.code ∧ st.globals = s.globals ∧
      (∀ x, sptMem x live → x ≠ condition → x ≠ rightRegister →
        sptLookup x st.locals = sptLookup x s.locals) ∧
      (∀ x, sptMem x live → sptMem x st.locals) := by
  let s1 : LoopSemStateFiniteExact width σ := LoopSemStateFiniteExact.setVar condition (.word w1) s
  let s2 : LoopSemStateFiniteExact width σ := LoopSemStateFiniteExact.setVar rightRegister (.word w2) s1
  have hE1 : LoopSemStateFiniteExact.evaluate (.assign condition leftValue) s = (none, s1) := by
    simp only [LoopSemStateFiniteExact.evaluate, hleft, s1]
  have hright1 : LoopSemStateFiniteExact.eval s1 rightValue = some (.word w2) := by
    have h := LoopSemStateFiniteExact.locals_touched_eq_eval_eq s rightValue s1
      ⟨rfl, rfl, rfl, rfl, rfl, fun n hn => by
        have hne : n ≠ condition := fun hc => hnotmem (hc ▸ hn)
        simp only [s1, LoopSemStateFiniteExact.setVar,
          sptLookup_sptInsert_ne condition n (.word w1) s.locals hne]⟩
    exact h.trans hright
  have hE2 : LoopSemStateFiniteExact.evaluate (.assign rightRegister rightValue) s1 = (none, s2) := by
    simp only [LoopSemStateFiniteExact.evaluate, hright1, s2]
  have hlookCond : sptLookup condition s2.locals = some (.word w1) := by
    simp [s2, s1, LoopSemStateFiniteExact.setVar, sptLookup_sptInsert, hcond]
  have hlookReg : sptLookup rightRegister s2.locals = some (.word w2) := by
    simp [s2, LoopSemStateFiniteExact.setVar, sptLookup_sptInsert]
  by_cases hb : Compiler.Encoders.Asm.wordCmpHOL operator w1 w2
  · let s3 : LoopSemStateFiniteExact width σ := LoopSemStateFiniteExact.setVar condition (.word 1) s2
    let st : LoopSemStateFiniteExact width σ :=
      LoopSemStateFiniteExact.decClock { s3 with locals := sptInter s3.locals live }
    have hs3 : sptSubsetLive live s3.locals := by
      simp only [s3, s2, s1, LoopSemStateFiniteExact.setVar]
      exact sptSubsetLive_of_live_insert condition rightRegister (.word 1) (.word w2)
        (fun n hn h1 h2 =>
          (sptMem_sptInsert n condition (.word w1) s.locals).mpr
            (Or.inr (hsubmem n hn h1 h2)))
    have hcut : LoopSemStateFiniteExact.cutRes live
        (LoopSemStateFiniteExact.evaluate (.assign condition (.const 1)) s2) = (none, st) := by
      have hev3 : LoopSemStateFiniteExact.evaluate (.assign condition (.const 1)) s2 = (none, s3) := by
        simp only [LoopSemStateFiniteExact.evaluate, LoopSemStateFiniteExact.eval, s3]
      have hcutclock : ({ s3 with locals := sptInter s3.locals live } :
          LoopSemStateFiniteExact width σ).clock ≠ 0 := by
        simp only [s3, LoopSemStateFiniteExact.setVar]
        exact hclock
      rw [hev3]
      dsimp only [LoopSemStateFiniteExact.cutRes]
      rw [LoopSemStateFiniteExact.cutState_of_subset live s3 hs3]
      dsimp only
      rw [if_neg hcutclock]
    have hite : LoopSemStateFiniteExact.evaluate
        (.ite operator condition (.reg rightRegister)
          (.assign condition (.const 1)) (.assign condition (.const 0)) live) s2 = (none, st) := by
      rw [LoopSemStateFiniteExact.evaluate]
      simp only [hlookCond, hlookReg, LoopSemStateFiniteExact.getVarImm_reg]
      rw [if_pos hb]
      exact hcut
    have hseq : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL
        [HolLoopProg.assign condition leftValue,
         HolLoopProg.assign rightRegister rightValue,
         HolLoopProg.ite operator condition (.reg rightRegister)
           (HolLoopProg.assign condition (.const 1))
           (HolLoopProg.assign condition (.const 0)) live]) s = (none, st) := by
      simp only [loopNestedSeqHOL]
      rw [LoopSemStateFiniteExact.evaluate]
      rw [LoopSemStateFiniteExact.fix_clock_evaluate, hE1]
      dsimp only
      rw [LoopSemStateFiniteExact.evaluate]
      rw [LoopSemStateFiniteExact.fix_clock_evaluate, hE2]
      dsimp only
      rw [LoopSemStateFiniteExact.evaluate]
      rw [LoopSemStateFiniteExact.fix_clock_evaluate, hite]
      dsimp only
      simp only [LoopSemStateFiniteExact.evaluate]
    have hval : LoopSemStateFiniteExact.eval st (.var condition) =
        some (.word (Compiler.Encoders.Asm.wordCmpResultHOL operator w1 w2)) := by
      have hwr : Compiler.Encoders.Asm.wordCmpResultHOL operator w1 w2 = 1 := by simp [Compiler.Encoders.Asm.wordCmpResultHOL, hb]
      rw [hwr]
      simp only [st, s3, LoopSemStateFiniteExact.decClock, LoopSemStateFiniteExact.eval,
        LoopSemStateFiniteExact.setVar, sptLookup_sptInter]
      rw [if_pos (by simpa only [sptMem, sptDomain] using hcondmem)]
      simp [sptLookup_sptInsert]
    have hfields : st.memory = s.memory ∧ st.mdomain = s.mdomain ∧
        st.shMdomain = s.shMdomain ∧ st.be = s.be ∧ st.ffi = s.ffi ∧
        st.baseAddr = s.baseAddr ∧ st.topAddr = s.topAddr ∧ st.code = s.code ∧
        st.globals = s.globals := by
      simp only [st, s3, s2, s1, LoopSemStateFiniteExact.decClock,
        LoopSemStateFiniteExact.setVar]
      simp
    have hclock' : st.clock = s.clock - 1 := by
      simp only [st, LoopSemStateFiniteExact.decClock, s3, s2, s1,
        LoopSemStateFiniteExact.setVar]
    have hpres : ∀ x, sptMem x live → x ≠ condition → x ≠ rightRegister →
        sptLookup x st.locals = sptLookup x s.locals := by
      intro x hxmem hxc hxr
      simp only [st, LoopSemStateFiniteExact.decClock, s3, s2, s1,
        LoopSemStateFiniteExact.setVar, sptLookup_sptInter]
      rw [if_pos (by simpa only [sptMem, sptDomain] using hxmem)]
      rw [sptLookup_sptInsert_ne condition x (WordLocW.word (1 : BitVec width)) _ hxc,
        sptLookup_sptInsert_ne rightRegister x (WordLocW.word w2) _ hxr,
        sptLookup_sptInsert_ne condition x (WordLocW.word w1) _ hxc]
    have hdom : ∀ x, sptMem x live → sptMem x st.locals := by
      intro x hx
      have hs3x : sptMem x s3.locals := hs3 x hx
      rw [sptMem_iff_lookup] at hs3x ⊢
      obtain ⟨vv, hvv⟩ := hs3x
      exact ⟨vv, by
        simp only [st, LoopSemStateFiniteExact.decClock, sptLookup_sptInter]
        rw [if_pos (by simpa only [sptMem, sptDomain] using hx)]
        exact hvv⟩
    exact ⟨st, hseq, hval, hclock', hfields.1, hfields.2.1, hfields.2.2.1,
      hfields.2.2.2.1, hfields.2.2.2.2.1, hfields.2.2.2.2.2.1,
      hfields.2.2.2.2.2.2.1, hfields.2.2.2.2.2.2.2.1, hfields.2.2.2.2.2.2.2.2, hpres, hdom⟩
  · let s3 : LoopSemStateFiniteExact width σ := LoopSemStateFiniteExact.setVar condition (.word 0) s2
    let st : LoopSemStateFiniteExact width σ :=
      LoopSemStateFiniteExact.decClock { s3 with locals := sptInter s3.locals live }
    have hs3 : sptSubsetLive live s3.locals := by
      simp only [s3, s2, s1, LoopSemStateFiniteExact.setVar]
      exact sptSubsetLive_of_live_insert condition rightRegister (.word 0) (.word w2)
        (fun n hn h1 h2 =>
          (sptMem_sptInsert n condition (.word w1) s.locals).mpr
            (Or.inr (hsubmem n hn h1 h2)))
    have hcut : LoopSemStateFiniteExact.cutRes live
        (LoopSemStateFiniteExact.evaluate (.assign condition (.const 0)) s2) = (none, st) := by
      have hev3 : LoopSemStateFiniteExact.evaluate (.assign condition (.const 0)) s2 = (none, s3) := by
        simp only [LoopSemStateFiniteExact.evaluate, LoopSemStateFiniteExact.eval, s3]
      have hcutclock : ({ s3 with locals := sptInter s3.locals live } :
          LoopSemStateFiniteExact width σ).clock ≠ 0 := by
        simp only [s3, LoopSemStateFiniteExact.setVar]
        exact hclock
      rw [hev3]
      dsimp only [LoopSemStateFiniteExact.cutRes]
      rw [LoopSemStateFiniteExact.cutState_of_subset live s3 hs3]
      dsimp only
      rw [if_neg hcutclock]
    have hite : LoopSemStateFiniteExact.evaluate
        (.ite operator condition (.reg rightRegister)
          (.assign condition (.const 1)) (.assign condition (.const 0)) live) s2 = (none, st) := by
      rw [LoopSemStateFiniteExact.evaluate]
      simp only [hlookCond, hlookReg, LoopSemStateFiniteExact.getVarImm_reg]
      rw [if_neg hb]
      exact hcut
    have hseq : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL
        [HolLoopProg.assign condition leftValue,
         HolLoopProg.assign rightRegister rightValue,
         HolLoopProg.ite operator condition (.reg rightRegister)
           (HolLoopProg.assign condition (.const 1))
           (HolLoopProg.assign condition (.const 0)) live]) s = (none, st) := by
      simp only [loopNestedSeqHOL]
      rw [LoopSemStateFiniteExact.evaluate]
      rw [LoopSemStateFiniteExact.fix_clock_evaluate, hE1]
      dsimp only
      rw [LoopSemStateFiniteExact.evaluate]
      rw [LoopSemStateFiniteExact.fix_clock_evaluate, hE2]
      dsimp only
      rw [LoopSemStateFiniteExact.evaluate]
      rw [LoopSemStateFiniteExact.fix_clock_evaluate, hite]
      dsimp only
      simp only [LoopSemStateFiniteExact.evaluate]
    have hval : LoopSemStateFiniteExact.eval st (.var condition) =
        some (.word (Compiler.Encoders.Asm.wordCmpResultHOL operator w1 w2)) := by
      have hwr : Compiler.Encoders.Asm.wordCmpResultHOL operator w1 w2 = 0 := by simp [Compiler.Encoders.Asm.wordCmpResultHOL, hb]
      rw [hwr]
      simp only [st, s3, LoopSemStateFiniteExact.decClock, LoopSemStateFiniteExact.eval,
        LoopSemStateFiniteExact.setVar, sptLookup_sptInter]
      rw [if_pos (by simpa only [sptMem, sptDomain] using hcondmem)]
      simp [sptLookup_sptInsert]
    have hfields : st.memory = s.memory ∧ st.mdomain = s.mdomain ∧
        st.shMdomain = s.shMdomain ∧ st.be = s.be ∧ st.ffi = s.ffi ∧
        st.baseAddr = s.baseAddr ∧ st.topAddr = s.topAddr ∧ st.code = s.code ∧
        st.globals = s.globals := by
      simp only [st, s3, s2, s1, LoopSemStateFiniteExact.decClock,
        LoopSemStateFiniteExact.setVar]
      simp
    have hclock' : st.clock = s.clock - 1 := by
      simp only [st, LoopSemStateFiniteExact.decClock, s3, s2, s1,
        LoopSemStateFiniteExact.setVar]
    have hpres : ∀ x, sptMem x live → x ≠ condition → x ≠ rightRegister →
        sptLookup x st.locals = sptLookup x s.locals := by
      intro x hxmem hxc hxr
      simp only [st, LoopSemStateFiniteExact.decClock, s3, s2, s1,
        LoopSemStateFiniteExact.setVar, sptLookup_sptInter]
      rw [if_pos (by simpa only [sptMem, sptDomain] using hxmem)]
      rw [sptLookup_sptInsert_ne condition x (WordLocW.word (0 : BitVec width)) _ hxc,
        sptLookup_sptInsert_ne rightRegister x (WordLocW.word w2) _ hxr,
        sptLookup_sptInsert_ne condition x (WordLocW.word w1) _ hxc]
    have hdom : ∀ x, sptMem x live → sptMem x st.locals := by
      intro x hx
      have hs3x : sptMem x s3.locals := hs3 x hx
      rw [sptMem_iff_lookup] at hs3x ⊢
      obtain ⟨vv, hvv⟩ := hs3x
      exact ⟨vv, by
        simp only [st, LoopSemStateFiniteExact.decClock, sptLookup_sptInter]
        rw [if_pos (by simpa only [sptMem, sptDomain] using hx)]
        exact hvv⟩
    exact ⟨st, hseq, hval, hclock', hfields.1, hfields.2.1, hfields.2.2.1,
      hfields.2.2.2.1, hfields.2.2.2.2.1, hfields.2.2.2.2.2.1,
      hfields.2.2.2.2.2.2.1, hfields.2.2.2.2.2.2.2.1, hfields.2.2.2.2.2.2.2.2, hpres, hdom⟩

/-- `comp_exp_preserves_eval`, case `Cmp operator left right`
    (`crep_to_loopProofScript.sml:772-786` statement; case proof at 1128-1239):
    the `eval_ind` hypotheses for the two operand sub-expressions plus the HOL
    conclusion.  The statement has exactly HOL's hypotheses: `open Classical`
    discharges the instance that the mis-tagged `evalCrepSemHOLExp` currently
    takes, so no `DecidablePred s.memaddrs` premise appears in the theorem type
    (cf. `#print`).

    The `@[hol]` tag is intentionally WITHDRAWN pending
    `flapjack-pxn.18.5.6.33.15.9`, which removes that instance from the tagged
    `crepSem$eval_def` interface.  Until then this declaration depends on a
    not-yet-exact tagged evaluator, so it is not tagged even though its own type
    is premise-free.  Re-tag once the evaluator interface is corrected. -/
theorem crepToLoop_comp_exp_preserves_eval_cmp {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) (operator : Cmp)
      (left right : CrepExpHOL width),
      crepToLoopCompExpPreservesEvalAt s left →
      crepToLoopCompExpPreservesEvalAt s right →
    ∀ (v : HolWordLab width) (t : LoopSemStateFiniteExact width σ)
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet),
      evalCrepSemHOLExp s (.cmp operator left right) = some v ∧
        crepToLoopStateRelExact s t ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        crepToLoopCodeRelExact ctxt s.code t.code ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
        compileExpHOLExact ctxt tmp l (.cmp operator left right) = (p, le, ntmp, nl) ∧
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
  intro s operator left right ihL ihR
  intro v t ctxt tmp l p le ntmp nl
  rintro ⟨he, hs, hm, hg, hc, hl, hcomp, hv⟩
  cases hL : evalCrepSemHOLExp s left with
  | none => simp [evalCrepSemHOLExp, hL] at he
  | some lv =>
    cases lv with
    | word w1 =>
      cases hR : evalCrepSemHOLExp s right with
      | none => simp [evalCrepSemHOLExp, hL, hR] at he
      | some rv =>
        cases rv with
        | word w2 =>
          simp only [evalCrepSemHOLExp, hL, hR] at he
          simp at he
          subst he
          rcases hA : compileExpHOLExact ctxt tmp l left with ⟨lc, lval, lnext, llive⟩
          rcases hB : compileExpHOLExact ctxt lnext llive right with ⟨rc, rval, rnext, rlive⟩
          rw [compileExpHOLExact] at hcomp
          simp only [hA, hB, Prod.mk.injEq] at hcomp
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hcomp
          obtain ⟨ck1, stL, hL1, hL2, hsL, hmL, hgL, hcL, hlL⟩ :=
            ihL (.word w1) t ctxt tmp l lc lval lnext llive ⟨hL, hs, hm, hg, hc, hl, hA, hv⟩
          simp only [wlabWlocExact] at hL2
          have hle_tmp : tmp ≤ lnext := by
            have := compileExpHOLExact_tmp_le ctxt tmp l left; rw [hA] at this; exact this
          have hle_tmp2 : lnext ≤ rnext := by
            have := compileExpHOLExact_tmp_le ctxt lnext llive right; rw [hB] at this; exact this
          obtain ⟨ck2, stR, hR1, hR2, hsR, hmR, hgR, hcR, hlR⟩ :=
            ihR (.word w2) stL ctxt lnext llive rc rval rnext rlive
              ⟨hR, hsL, hmL, hgL, hcL, hlL, hB, by omega⟩
          simp only [wlabWlocExact] at hR2
          obtain ⟨hOutL1, hOutL2, hOutL3⟩ :=
            compile_exp_out_rel ctxt tmp l left lc lval lnext llive hA
          obtain ⟨hOutR1, hOutR2, hOutR3⟩ :=
            compile_exp_out_rel ctxt lnext llive right rc rval rnext rlive hB
          obtain ⟨hlLdistinct, hlLmax, hlLdom, hlLlookup⟩ :=
            crepToLoopLocalsRelExact_intro ctxt l s.locals t.locals hl
          have hvarsL : ∀ n, n ∈ crepExpVarsHOL left →
              ∃ m, ctxt.vars.lookup n = some m ∧ sptMem m l := by
            intro n hn
            obtain ⟨w, hw⟩ := evalCrepSemHOLExp_exists_locals_of_mem_vars s left (.word w1) n hL hn
            obtain ⟨m, hm', hmem', _⟩ := hlLlookup n w hw
            exact ⟨m, hm', hmem'⟩
          have hvarsR : ∀ n, n ∈ crepExpVarsHOL right →
              ∃ m, ctxt.vars.lookup n = some m ∧ sptMem m llive := by
            intro n hn
            obtain ⟨w, hw⟩ := evalCrepSemHOLExp_exists_locals_of_mem_vars s right (.word w2) n hR hn
            obtain ⟨m, hm', hmem', _⟩ := hlLlookup n w hw
            refine ⟨m, hm', ?_⟩
            have := compileExpHOLExact_domain_mono ctxt tmp l left m hmem'
            rw [hA] at this
            exact this
          have hleLeft : ∀ n, n ∈ holLoopLocalsTouched lval →
              n < lnext ∧ sptMem n (cutSetsHOL l (loopNestedSeqHOL lc)) := by
            intro n hn
            obtain ⟨h1, h2⟩ := compile_exp_le_tmp_domain ctxt tmp l left lc lval lnext llive n
              ⟨hlLmax, hA, hv, hvarsL, hn⟩
            exact ⟨h1, by rw [← hOutL3]; exact h2⟩
          have hleRight : ∀ n, n ∈ holLoopLocalsTouched rval →
              n < rnext ∧ sptMem n rlive :=
            fun n hn => compile_exp_le_tmp_domain ctxt lnext llive right rc rval rnext rlive n
              ⟨hlLmax, hB, by omega, hvarsR, hn⟩
          have hboundL : ∀ n, n ∈ holLoopAssignedVars (loopNestedSeqHOL lc) → n < lnext :=
            fun n hn =>
              (comp_exp_assigned_vars_tmp_bound ctxt tmp l left lc lval lnext llive n
                ⟨hA, hn⟩).2
          have hboundR : ∀ n, n ∈ holLoopAssignedVars (loopNestedSeqHOL rc) → lnext ≤ n :=
            fun n hn =>
              (comp_exp_assigned_vars_tmp_bound ctxt lnext llive right rc rval rnext rlive n
                ⟨hB, hn⟩).1
          have hrc_syntax :
              compSyntaxOkHOL (cutSetsHOL l (loopNestedSeqHOL lc)) (loopNestedSeqHOL rc) = true := by
            rw [← hOutL3]; exact hOutR1
          have hL1' : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL lc)
              {t with clock := ck1 + t.clock} = (none, stL) := by
            simpa only [Nat.add_comm] using hL1
          have hR1' : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL rc)
              {stL with clock := ck2 + stL.clock} = (none, stR) := by
            simpa only [Nat.add_comm] using hR1
          have hleftR : LoopSemStateFiniteExact.eval stR lval = some (.word w1) :=
            nested_seq_pure_evaluation lc rc t stR stL l lnext lval (.word w1) ck1 ck2
              ⟨hL1', hR1', hOutL1, hrc_syntax, hboundL, hboundR, hleLeft, hL2⟩
          let stL' : LoopSemStateFiniteExact width σ := { stL with clock := stL.clock + (ck2 + 1) }
          let stR' : LoopSemStateFiniteExact width σ := { stR with clock := stR.clock + 1 }
          have hL1'' : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL lc)
              {t with clock := t.clock + (ck1 + (ck2 + 1))} = (none, stL') := by
            have h := LoopSemStateFiniteExact.evaluate_add_clock_eq (loopNestedSeqHOL lc)
              {t with clock := t.clock + ck1} none stL (ck2 + 1) hL1 (by simp)
            simpa only [with_clock_with_clock, Nat.add_assoc, stL'] using h
          have hR1'' : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL rc) stL' = (none, stR') := by
            have h := LoopSemStateFiniteExact.evaluate_add_clock_eq (loopNestedSeqHOL rc)
              {stL with clock := stL.clock + ck2} none stR 1 hR1 (by simp)
            simpa only [with_clock_with_clock, Nat.add_assoc, stL', stR'] using h
          have hLR : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL (lc ++ rc))
              {t with clock := t.clock + (ck1 + (ck2 + 1))} = (none, stR') := by
            rw [LoopSemStateFiniteExact.evaluate_none_nested_seq_append lc _ stL' rc hL1'']
            exact hR1''
          have hleftR' : LoopSemStateFiniteExact.eval stR' lval = some (.word w1) := by
            simpa only [stR', LoopSemStateFiniteExact.eval_upd_clock_eq] using hleftR
          have hrightR' : LoopSemStateFiniteExact.eval stR' rval = some (.word w2) := by
            simpa only [stR', LoopSemStateFiniteExact.eval_upd_clock_eq] using hR2
          have hnotmem : (rnext + 1) ∉ holLoopLocalsTouched rval := by
            intro hmem
            have := (hleRight (rnext + 1) hmem).1
            omega
          have hsubmem : ∀ n, sptMem n (sptListInsert [rnext + 1, rnext + 2] rlive) →
              n ≠ rnext + 1 → n ≠ rnext + 2 → sptMem n stR'.locals := by
            intro n hn h1 h2
            have hdec : n = rnext + 2 ∨ n = rnext + 1 ∨ sptMem n rlive := by
              simpa only [sptListInsert, sptMem_sptInsert, or_assoc] using hn
            rcases hdec with h | h | hr
            · exact absurd h h2
            · exact absurd h h1
            · simpa only [stR'] using hlR.2.2.1 n hr
          have hcondmem : sptMem (rnext + 1) (sptListInsert [rnext + 1, rnext + 2] rlive) := by
            simp [sptListInsert, sptMem_sptInsert]
          have hclockR' : stR'.clock ≠ 0 := by
            simp only [stR']; omega
          obtain ⟨st, htail, hval, hclock, hmem', hmd', hsh', hbe', hffi', hba', hta',
            hcode', hglob', hpres, hdom⟩ :=
            evaluate_progIfTail operator (rnext + 1) (rnext + 2) lval rval
              (sptListInsert [rnext + 1, rnext + 2] rlive) w1 w2 stR'
              (by omega) hleftR' hrightR' hnotmem hsubmem hcondmem hclockR'
          refine ⟨ck1 + (ck2 + 1), st, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [progIfHOLExact]
            rw [LoopSemStateFiniteExact.evaluate_none_nested_seq_append (lc ++ rc) _ stR' _ hLR, htail]
          · simpa only [wlabWlocExact] using hval
          · rw [crepToLoopStateRelExact]
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simpa only [hmd', stR'] using hsR.1
            · simpa only [hsh', stR'] using hsR.2.1
            · have hc : st.clock = stR.clock := by
                rw [hclock]; simp only [stR']; omega
              rw [hc]; exact hsR.2.2.1
            · simpa only [hbe', stR'] using hsR.2.2.2.1
            · simpa only [hffi', stR'] using hsR.2.2.2.2.1
            · simpa only [hba', stR'] using hsR.2.2.2.2.2.1
            · simpa only [hta', stR'] using hsR.2.2.2.2.2.2
          · simpa only [hmem', stR'] using hmR
          · simpa only [hglob', stR'] using hgR
          · simpa only [hcode', stR'] using hcR
          · rw [crepToLoopLocalsRelExact_iff]
            refine ⟨hlR.1, hlR.2.1, fun n hn => hdom n hn, ?_⟩
            intro vname value hlook
            obtain ⟨n, hvar, hnrlive, hnlook⟩ := hlR.2.2.2 vname value hlook
            have hnlive : sptMem n (sptListInsert [rnext + 1, rnext + 2] rlive) :=
              sptMem_sptListInsert_of n [rnext + 1, rnext + 2] rlive hnrlive
            have hvmax : n ≤ ctxt.vmax := hlR.2.1 vname n hvar
            have hncond : n ≠ rnext + 1 := by omega
            have hnreg : n ≠ rnext + 2 := by omega
            refine ⟨n, hvar, hnlive, ?_⟩
            rw [hpres n hnlive hncond hnreg]
            simpa only [stR'] using hnlook

end Flapjack
