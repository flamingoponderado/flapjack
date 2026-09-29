import Flapjack.Pancake.CrepToLoop.Proofs.LoopEvaluateHelpers
import Flapjack.Pancake.CrepToLoop.Proofs.CrepEvalHelpers
import Flapjack.Pancake.CrepToLoop.Proofs.RelationsExact
import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate
import Flapjack.Pancake.Semantics.LoopProps.EvalExact
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqExact
import Flapjack.Pancake.Semantics.ByteAlignBridge
import Flapjack.Pancake.Semantics.PanSem.MemLoad32Alt
import Flapjack.Pancake.Semantics.LoopProps.EvaluateClockExact
import Flapjack.Pancake.Semantics.LoopProps.CompSyntaxOkEvalExact
import Flapjack.Pancake.Semantics.CrepProps.EvalSomeVarCexp
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpTmpBound
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpLeTmpDomain
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpOutRel
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpPreservesEval.Load

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
relations.  The leaf cases (`Const`, `Var`, `LoadGlob`, `BaseAddr`, `TopAddr`)
and the `Load` case are flapjack-luna-c's pieces in
`CompExpPreservesEval/Leaf.lean` and its focused `Load` module.  The
assembling theorem is tracked on bead `flapjack-pxn.18.5.6.33.15.8`.
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

/-- Flapjack helper (no HOL declaration of its own): the `compile_exps` statement of
    HOL `comp_exps_preserves_eval` (`crep_to_loopProofScript.sml:1241-1254`) for an
    argument list `es`, derived from the single-expression statement at each member
    of `es`.  HOL's own proof (`Induct` on `es`, 1255-1320) is this induction with
    `comp_exp_preserves_eval` in place of the member hypotheses; the tagged
    `comp_exps_preserves_eval` instantiates them with the assembled theorem, and the
    `Op`/`Crepop` cases use it with their `eval_ind` hypotheses.  `OPT_MMAP` is
    `List.mapM` and `MAP wlab_wloc` is `List.map wlabWlocExact`. -/
theorem crepToLoopCompExpsPreservesEvalOfAt {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) :
    ∀ (es : List (CrepExpHOL width)),
      (∀ e ∈ es, crepToLoopCompExpPreservesEvalAt s e) →
    ∀ (vs : List (HolWordLab width)) (t : LoopSemStateFiniteExact width σ)
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
      (p : List (HolLoopProg width)) (les : List (HolLoopExp width)) (ntmp : Nat) (nl : NumSet),
      es.mapM (evalCrepSemHOLExp s) = some vs ∧
        crepToLoopStateRelExact s t ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        crepToLoopCodeRelExact ctxt s.code t.code ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
        compileExpsHOLExact ctxt tmp l es = (p, les, ntmp, nl) ∧
        ctxt.vmax < tmp →
      ∃ (ck : Nat) (st : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL p)
            { t with clock := t.clock + ck } = (none, st) ∧
        les.mapM (LoopSemStateFiniteExact.eval st) = some (vs.map wlabWlocExact) ∧
        crepToLoopStateRelExact s st ∧
        crepToLoopMemRelHOLExact s.memory st.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals st.globals ∧
        crepToLoopCodeRelExact ctxt s.code st.code ∧
        crepToLoopLocalsRelExact ctxt nl s.locals st.locals := by
  intro es
  induction es with
  | nil =>
    intro _ vs t ctxt tmp l p les ntmp nl ⟨he, hs, hm, hg, hc, hl, hcomp, _⟩
    simp only [compileExpsHOLExact, Prod.mk.injEq] at hcomp
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hcomp
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at he
    subst he
    exact ⟨0, t, by simp [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate], by simp,
      hs, hm, hg, hc, hl⟩
  | cons e es ihl =>
    intro ih vs t ctxt tmp l p les ntmp nl ⟨he, hs, hm, hg, hc, hl, hcomp, hv⟩
    cases he1 : evalCrepSemHOLExp s e with
    | none => simp [List.mapM_cons, he1] at he
    | some x =>
    cases hes : es.mapM (evalCrepSemHOLExp s) with
    | none => simp [List.mapM_cons, he1, hes] at he
    | some xs =>
    have hvs : vs = x :: xs := by
      simp [List.mapM_cons, he1, hes] at he; exact he.symm
    subst hvs
    rcases hA : compileExpHOLExact ctxt tmp l e with ⟨c1, v1, n1, l1⟩
    rcases hB : compileExpsHOLExact ctxt n1 l1 es with ⟨c2, vs2, n2, l2⟩
    rw [compileExpsHOLExact, hA] at hcomp
    simp only [hB, Prod.mk.injEq] at hcomp
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hcomp
    obtain ⟨hokA, htA, hlA⟩ := compile_exp_out_rel ctxt tmp l e c1 v1 n1 l1 hA
    obtain ⟨hokB, _, _, _⟩ := compile_exp_out_rel_cases.2 ctxt n1 l1 es c2 vs2 n2 l2 hB
    obtain ⟨ck1, st1, h1, h1v, h1s, h1m, h1g, h1c, h1l⟩ :=
      ih e List.mem_cons_self x t ctxt tmp l c1 v1 n1 l1 ⟨he1, hs, hm, hg, hc, hl, hA, hv⟩
    obtain ⟨ck2, st2, h2, h2v, h2s, h2m, h2g, h2c, h2l⟩ :=
      ihl (fun e' he' => ih e' (List.mem_cons_of_mem _ he')) xs st1 ctxt n1 l1 c2 vs2 n2 l2
        ⟨hes, h1s, h1m, h1g, h1c, h1l, hB, Nat.lt_of_lt_of_le hv htA⟩
    have h1ck : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL c1)
        { t with clock := t.clock + (ck1 + ck2) } =
          (none, { st1 with clock := st1.clock + ck2 }) := by
      have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ ck2 h1 (by simp)
      simpa [Nat.add_assoc] using this
    have hv1 : LoopSemStateFiniteExact.eval st2 v1 = some (wlabWlocExact x) := by
      refine LoopSemStateFiniteExact.nested_seq_pure_evaluation c1 c2 t st2 st1 l n1 v1
        (wlabWlocExact x) ck1 ck2 ⟨by rw [Nat.add_comm]; exact h1, by rw [Nat.add_comm]; exact h2,
          hokA, hlA ▸ hokB, ?_, ?_, ?_, h1v⟩
      · intro n hn
        exact (comp_exp_assigned_vars_tmp_bound ctxt tmp l e c1 v1 n1 l1 n ⟨hA, hn⟩).2
      · intro n hn
        exact (comp_exps_assigned_vars_tmp_bound ctxt n1 l1 es c2 vs2 n2 l2 n ⟨hB, hn⟩).1
      · intro n hn
        have := compile_exp_le_tmp_domain ctxt tmp l e c1 v1 n1 l1 n
          ⟨hl.2.1, hA, hv, fun k hk => ?_, hn⟩
        · exact ⟨this.1, hlA ▸ this.2⟩
        · obtain ⟨w, hw⟩ := crepEval_some_var_cexp_local_lookup s e _ k ⟨he1, hk⟩
          obtain ⟨m, hm1, hm2, _⟩ := hl.2.2.2 k w hw
          exact ⟨m, hm1, hm2⟩
    refine ⟨ck1 + ck2, st2, ?_, ?_, h2s, h2m, h2g, h2c, h2l⟩
    · rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none c1 _ _ c2 h1ck]
      exact h2
    · simp [List.mapM_cons, hv1, h2v]

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
    ∀ (s : CrepSemHOLState width σ) (e : CrepExpHOL width),
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
  classical
  intro s e ih v t ctxt tmp l p le ntmp nl ⟨he, hs, hm, hg, hc, hl, hcomp, hv⟩
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

/-- Flapjack helper (no HOL declaration): HOL `wordSem$mem_load_32_alt`'s
    shift/OR form of `word_of_bytes be (0w:word32)` at the four concrete byte
    positions (HOL proves it by `EVAL_TAC >> BBLAST_TAC`). -/
private theorem wordOfBytes32_alt (be : Bool) (g0 g1 g2 g3 : BitVec 8) :
    wordOfBytesHOL8 be (0 : BitVec 32) [g0, g1, g2, g3] =
      if be then g0.setWidth 32 <<< 24 ||| g1.setWidth 32 <<< 16 |||
          g2.setWidth 32 <<< 8 ||| g3.setWidth 32
      else g0.setWidth 32 ||| g1.setWidth 32 <<< 8 |||
          g2.setWidth 32 <<< 16 ||| g3.setWidth 32 <<< 24 := by
  cases be <;> simp [wordOfBytesHOL8, setByteHOL8, byteIndexHOL] <;> bv_decide

/-- The `UInt8`-valued `panGetByteHOL` and the `word8`-valued `getByteHOL8`
    (both HOL `byte$get_byte`) select the same byte. -/
private theorem byte32_of_panGetByteHOL {width : Nat} [NeZero width]
    (a v : BitVec width) (be : Bool) :
    BitVec.ofNat 32 (panGetByteHOL a v be).toNat = (getByteHOL8 a v be).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  rw [panGetByteHOL_eq_riscvGetByteHOL]
  simp [getByteHOL8, riscvGetByteHOL, byteIndexHOL]

/-- `riscvAlignedHOL 2` (HOL `aligned 2`) is `w2n a MOD 4 = 0`. -/
private theorem riscvAligned2_iff {width : Nat} (a : BitVec width) :
    riscvAlignedHOL 2 a = true ↔ a.toNat % 4 = 0 := by
  have hlt : a.toNat / 4 * 4 < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) a.isLt
  have key : ((a >>> (2 : Nat)) <<< (2 : Nat)).toNat = a.toNat / 4 * 4 := by
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt hlt
  simp only [riscvAlignedHOL, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [key] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [key]
    omega

/-- Flapjack bridge (no HOL declaration; HOL's Load32 case rewrites with
    `panSem$mem_load_32_alt` and `wordSem$mem_load_32_alt`): under `mem_rel` and
    the `state_rel` domain equation, a Crep 32-bit load returns the same
    `word32` on the Loop side. -/
private theorem memLoad32_bridge {width : Nat} [NeZero width]
    (smem : BitVec width → HolWordLab width) (dom : BitVec width → Prop) [DecidablePred dom]
    (tmem : BitVec width → WordLocW width) (tdom : BitVec width → Bool)
    (be : Bool) (a : BitVec width) (word : BitVec 32)
    (hdom : dom = fun x => tdom x = true) (hm : crepToLoopMemRelHOLExact smem tmem dom)
    (h : panMemLoad32HOL smem dom be a = some word) :
    memLoad32Exact tmem tdom be a = some word := by
  rw [panMemLoad32HOL_eq_alt] at h
  by_cases ha : a.toNat % 4 = 0
  · rw [if_pos ha] at h
    cases hv : smem (panByteAlignHOL a) with
    | word val =>
      simp only [hv] at h
      by_cases hd : dom (panByteAlignHOL a)
      · rw [if_pos hd] at h
        have hmv := hm _ hd
        rw [hv] at hmv
        have htd : tdom (panByteAlignHOL a) = true := by subst hdom; exact hd
        unfold memLoad32Exact
        rw [if_pos ((riscvAligned2_iff a).mpr ha), riscvByteAlignHOL_eq_panByteAlignHOL, ← hmv]
        simp only [wlabWlocExact, htd, if_true, wordOfBytes32_alt]
        simp only [byte32_of_panGetByteHOL] at h
        exact h
      · rw [if_neg hd] at h
        cases h
  · rw [if_neg ha] at h
    cases h

/-- `comp_exp_preserves_eval`, case `Load32 e` (`crep_to_loopProofScript.sml:772-786`
    statement; case proof at 1036-1074), with the `eval_ind` hypothesis for the
    address sub-expression `e`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_preserves_eval"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_comp_exp_preserves_eval_load32 {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) (e : CrepExpHOL width),
      crepToLoopCompExpPreservesEvalAt s e →
    ∀ (v : HolWordLab width) (t : LoopSemStateFiniteExact width σ)
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet),
      evalCrepSemHOLExp s (.load32 e) = some v ∧
        crepToLoopStateRelExact s t ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        crepToLoopCodeRelExact ctxt s.code t.code ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
        compileExpHOLExact ctxt tmp l (.load32 e) = (p, le, ntmp, nl) ∧
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
  classical
  intro s e ih v t ctxt tmp l p le ntmp nl ⟨he, hs, hm, hg, hc, hl, hcomp, hv⟩
  cases hea : evalCrepSemHOLExp s e with
  | none => simp [evalCrepSemHOLExp, hea] at he
  | some a =>
    cases a with
    | word w =>
      cases hb : panMemLoad32HOL s.memory s.memaddrs s.be w with
      | none => simp [evalCrepSemHOLExp, hea, hb] at he
      | some byte =>
        have hv' : v = .word (byte.setWidth width) := by
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
        have hbl := memLoad32_bridge s.memory s.memaddrs st.memory st.mdomain s.be w byte h3.1 h4 hb
        rw [h3.2.2.2.1] at hbl
        have hvm : ctxt.vmax < m := Nat.lt_of_lt_of_le hv hout
        refine ⟨ck, LoopSemStateFiniteExact.setVar m (.word (byte.setWidth width))
            (LoopSemStateFiniteExact.setVar m (.word w) st), ?_, ?_, h3, h4, h5, h6, ?_⟩
        · rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none c _ st _ h1]
          simp [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq,
            LoopSemStateFiniteExact.evaluate, h2, LoopSemStateFiniteExact.setVar, wlabWlocExact,
            sptLookup_sptInsert, hbl]
        · simp [LoopSemStateFiniteExact.eval, LoopSemStateFiniteExact.setVar,
            sptLookup_sptInsert, wlabWlocExact]
        · refine locals_rel_insert_domain ctxt o s.locals _ m
            (crepToLoopLocalsRelExact_insert_gt_vmax ctxt o s.locals _ m _
              (crepToLoopLocalsRelExact_insert_gt_vmax ctxt o s.locals _ m _ h7 hvm) hvm) ?_
          simp [sptMem, sptDomain, LoopSemStateFiniteExact.setVar,
            sptLookup_sptInsert]

/-- `comp_exp_preserves_eval`, case `Shift sh e1 e2`
    (`crep_to_loopProofScript.sml:772-786` statement; case proof at 1084-1127),
    with the `eval_ind` hypotheses for both operands. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_preserves_eval"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_comp_exp_preserves_eval_shift {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) (sh : Shift)
      (e1 e2 : CrepExpHOL width),
      crepToLoopCompExpPreservesEvalAt s e1 → crepToLoopCompExpPreservesEvalAt s e2 →
    ∀ (v : HolWordLab width) (t : LoopSemStateFiniteExact width σ)
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet),
      evalCrepSemHOLExp s (.shift sh e1 e2) = some v ∧
        crepToLoopStateRelExact s t ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        crepToLoopCodeRelExact ctxt s.code t.code ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
        compileExpHOLExact ctxt tmp l (.shift sh e1 e2) = (p, le, ntmp, nl) ∧
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
  intro s sh e1 e2 ih1 ih2 v t ctxt tmp l p le ntmp nl ⟨he, hs, hm, hg, hc, hl, hcomp, hv⟩
  cases he1 : evalCrepSemHOLExp s e1 with
  | none => simp [evalCrepSemHOLExp, he1] at he
  | some a1 =>
  cases a1 with
  | word w1 =>
  cases he2 : evalCrepSemHOLExp s e2 with
  | none => simp [evalCrepSemHOLExp, he1, he2] at he
  | some a2 =>
  cases a2 with
  | word w2 =>
  cases hsh : wordShiftHOL sh w1 w2.toNat with
  | none => simp [evalCrepSemHOLExp, he1, he2, hsh] at he
  | some x =>
  have hvx : v = .word x := by
    simp [evalCrepSemHOLExp, he1, he2, hsh] at he; exact he.symm
  subst hvx
  rcases hA : compileExpHOLExact ctxt tmp l e1 with ⟨c1, lv, n1, l1⟩
  rcases hB : compileExpHOLExact ctxt n1 l1 e2 with ⟨c2, rv, n2, l2⟩
  rw [compileExpHOLExact, hA] at hcomp
  simp only [hB, Prod.mk.injEq] at hcomp
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hcomp
  obtain ⟨hokA, htA, hlA⟩ := compile_exp_out_rel ctxt tmp l e1 c1 lv n1 l1 hA
  obtain ⟨hokB, htB, hlB⟩ := compile_exp_out_rel ctxt n1 l1 e2 c2 rv n2 l2 hB
  obtain ⟨ck1, st1, h1, h1v, h1s, h1m, h1g, h1c, h1l⟩ :=
    ih1 (.word w1) t ctxt tmp l c1 lv n1 l1 ⟨he1, hs, hm, hg, hc, hl, hA, hv⟩
  obtain ⟨ck2, st2, h2, h2v, h2s, h2m, h2g, h2c, h2l⟩ :=
    ih2 (.word w2) st1 ctxt n1 l1 c2 rv n2 l2
      ⟨he2, h1s, h1m, h1g, h1c, h1l, hB, Nat.lt_of_lt_of_le hv htA⟩
  have h1ck : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL c1)
      { t with clock := t.clock + (ck1 + ck2) } =
        (none, { st1 with clock := st1.clock + ck2 }) := by
    have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ ck2 h1 (by simp)
    simpa [Nat.add_assoc] using this
  refine ⟨ck1 + ck2, st2, ?_, ?_, h2s, h2m, h2g, h2c, h2l⟩
  · rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none c1 _ _ c2 h1ck]
    exact h2
  · have hlv : LoopSemStateFiniteExact.eval st2 lv = some (.word w1) := by
      refine LoopSemStateFiniteExact.nested_seq_pure_evaluation c1 c2 t st2 st1 l n1 lv
        (.word w1) ck1 ck2 ⟨by rw [Nat.add_comm]; exact h1, by rw [Nat.add_comm]; exact h2,
          hokA, hlA ▸ hokB, ?_, ?_, ?_, by simpa [wlabWlocExact] using h1v⟩
      · intro n hn
        exact (comp_exp_assigned_vars_tmp_bound ctxt tmp l e1 c1 lv n1 l1 n ⟨hA, hn⟩).2
      · intro n hn
        exact (comp_exp_assigned_vars_tmp_bound ctxt n1 l1 e2 c2 rv n2 l2 n ⟨hB, hn⟩).1
      · intro n hn
        have := compile_exp_le_tmp_domain ctxt tmp l e1 c1 lv n1 l1 n
          ⟨hl.2.1, hA, hv, fun k hk => ?_, hn⟩
        · exact ⟨this.1, hlA ▸ this.2⟩
        · obtain ⟨w, hw⟩ := crepEval_some_var_cexp_local_lookup s e1 _ k ⟨he1, hk⟩
          obtain ⟨m, hm1, hm2, _⟩ := hl.2.2.2 k w hw
          exact ⟨m, hm1, hm2⟩
    simp [LoopSemStateFiniteExact.eval, hlv, h2v, wlabWlocExact, hsh]

private theorem sptMem_sptListInsert_cases (k : Nat) :
    ∀ (keys : List Nat) (tree : NumSet), sptMem k (sptListInsert keys tree) →
      k ∈ keys ∨ sptMem k tree
  | [], _, h => Or.inr h
  | key :: keys, tree, h => by
      rcases sptMem_sptListInsert_cases k keys _ h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · rcases (sptMem_sptInsert k key () tree).mp h with rfl | h
        · exact Or.inl List.mem_cons_self
        · exact Or.inr h

/-- Flapjack helper (no HOL declaration): `locals_rel` survives a change of
    live set and target locals that keeps every slot `≤ vmax`, extends the live
    set, and keeps the new live set inside the new target domain (the
    `SUBSET_TRANS`/`lookup_insert` step of HOL's Crepop/Cmp cases). -/
private theorem locals_rel_update {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (o o' : NumSet)
    (sl : HolFiniteMapExact Nat (HolWordLab width)) (tl tl' : Spt (WordLocW width))
    (h : crepToLoopLocalsRelExact ctxt o sl tl)
    (hdom : ∀ k, sptMem k o' → sptMem k tl') (hsub : ∀ k, sptMem k o → sptMem k o')
    (hkeep : ∀ n, n ≤ ctxt.vmax → sptLookup n tl' = sptLookup n tl) :
    crepToLoopLocalsRelExact ctxt o' sl tl' := by
  refine ⟨h.1, h.2.1, hdom, fun vn val hval => ?_⟩
  obtain ⟨n, h1, h2, h3⟩ := h.2.2.2 vn val hval
  exact ⟨n, h1, hsub n h2, by rw [hkeep n (h.2.1 vn n h1)]; exact h3⟩

private theorem eval_setVar_untouched {width : Nat} [NeZero width] {F : Type}
    (st : LoopSemStateFiniteExact width F) (e : HolLoopExp width) (n : Nat)
    (x : WordLocW width) (h : ∀ k, k ∈ holLoopLocalsTouched e → k < n) :
    LoopSemStateFiniteExact.eval (LoopSemStateFiniteExact.setVar n x st) e =
      LoopSemStateFiniteExact.eval st e := by
  apply LoopSemStateFiniteExact.locals_touched_eq_eval_eq st e
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun k hk => ?_⟩
  have := h k hk
  simp only [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert]
  rw [if_neg (by omega)]

/-- `comp_exp_preserves_eval`, case `Crepop bop es`
    (`crep_to_loopProofScript.sml:772-786` statement; case proof at 889-972),
    with the `eval_ind` hypotheses for every argument expression. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_preserves_eval"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_comp_exp_preserves_eval_crepOp {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) (bop : CrepOp)
      (es : List (CrepExpHOL width)),
      (∀ e ∈ es, crepToLoopCompExpPreservesEvalAt s e) →
    ∀ (v : HolWordLab width) (t : LoopSemStateFiniteExact width σ)
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet),
      evalCrepSemHOLExp s (.crepOp bop es) = some v ∧
        crepToLoopStateRelExact s t ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        crepToLoopCodeRelExact ctxt s.code t.code ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
        compileExpHOLExact ctxt tmp l (.crepOp bop es) = (p, le, ntmp, nl) ∧
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
  intro s bop es ih v t ctxt tmp l p le ntmp nl ⟨he, hs, hm, hg, hc, hl, hcomp, hv⟩
  cases bop
  -- only two-argument word lists reach `crep_op Mul`
  obtain ⟨e1, e2, a, b, rfl, he1, he2, rfl⟩ : ∃ e1 e2 a b, es = [e1, e2] ∧
      evalCrepSemHOLExp s e1 = some (.word a) ∧ evalCrepSemHOLExp s e2 = some (.word b) ∧
      v = .word (a * b) := by
    match es, he with
    | [], he => simp [evalCrepSemHOLExp, crepOpCrepWord] at he
    | [x], he =>
      cases hx : evalCrepSemHOLExp s x with
      | none => simp [evalCrepSemHOLExp, hx] at he
      | some y => cases y; simp [evalCrepSemHOLExp, hx, crepOpCrepWord] at he
    | [x, y], he =>
      cases hx : evalCrepSemHOLExp s x with
      | none => simp [evalCrepSemHOLExp, hx] at he
      | some x' =>
        cases hy : evalCrepSemHOLExp s y with
        | none => simp [evalCrepSemHOLExp, hx, hy] at he
        | some y' =>
          cases x' with | word a' => cases y' with | word b' =>
          simp [evalCrepSemHOLExp, hx, hy, crepOpCrepWord] at he
          exact ⟨x, y, a', b', rfl, hx, hy, he.symm⟩
    | x :: y :: z :: rest, he =>
      cases hx : evalCrepSemHOLExp s x with
      | none => simp [evalCrepSemHOLExp, hx] at he
      | some x' =>
        cases hy : evalCrepSemHOLExp s y with
        | none => simp [evalCrepSemHOLExp, hx, hy] at he
        | some y' =>
          cases hz : evalCrepSemHOLExp s z with
          | none => simp [evalCrepSemHOLExp, hx, hy, hz] at he
          | some z' =>
            cases hr : rest.mapM (evalCrepSemHOLExp s) with
            | none => simp [evalCrepSemHOLExp, hx, hy, hz, hr] at he
            | some rs => simp [evalCrepSemHOLExp, hx, hy, hz, hr, crepOpCrepWord] at he
  have ih1 := ih e1 (by simp)
  have ih2 := ih e2 (by simp)
  rcases hA : compileExpHOLExact ctxt tmp l e1 with ⟨c1, v1, n1, l1⟩
  rcases hB : compileExpHOLExact ctxt n1 l1 e2 with ⟨c2, v2, n2, l2⟩
  have hexps : compileExpsHOLExact ctxt tmp l [e1, e2] = (c1 ++ (c2 ++ []), [v1, v2], n2, l2) := by
    rw [compileExpsHOLExact, hA]
    simp only
    rw [compileExpsHOLExact, hB]
    simp only
    rw [compileExpsHOLExact]
  obtain ⟨d, hd, hcopEq⟩ : ∃ d, (d = n2 + 2 ∨ d = n2 + 3) ∧ ∀ L : NumSet,
      compileCrepopHOLExact (width := width) .mul ctxt.target n2 (n2 + 1) (n2 + 2) L =
        ([.arith (.longMul (n2 + 2) d n2 (n2 + 1))], d) := by
    by_cases ht : ctxt.target = .armv7
    · exact ⟨n2 + 3, Or.inr rfl, fun L => by simp [compileCrepopHOLExact, ht]⟩
    · exact ⟨n2 + 2, Or.inl rfl, fun L => by simp [compileCrepopHOLExact, ht]⟩
  rw [compileExpHOLExact, hexps] at hcomp
  simp only [List.length_cons, List.length_nil, Nat.zero_add,
    show n2 + (1 + 1) = n2 + 2 from rfl, hcopEq, Prod.mk.injEq] at hcomp
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hcomp
  obtain ⟨hokA, htA, hlA⟩ := compile_exp_out_rel ctxt tmp l e1 c1 v1 n1 l1 hA
  obtain ⟨hokB, htB, hlB⟩ := compile_exp_out_rel ctxt n1 l1 e2 c2 v2 n2 l2 hB
  obtain ⟨ck1, st1, h1, h1v, h1s, h1m, h1g, h1c, h1l⟩ :=
    ih1 (.word a) t ctxt tmp l c1 v1 n1 l1 ⟨he1, hs, hm, hg, hc, hl, hA, hv⟩
  obtain ⟨ck2, st2, h2, h2v, h2s, h2m, h2g, h2c, h2l⟩ :=
    ih2 (.word b) st1 ctxt n1 l1 c2 v2 n2 l2
      ⟨he2, h1s, h1m, h1g, h1c, h1l, hB, Nat.lt_of_lt_of_le hv htA⟩
  have h1ck : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL c1)
      { t with clock := t.clock + (ck1 + ck2) } =
        (none, { st1 with clock := st1.clock + ck2 }) := by
    have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ ck2 h1 (by simp)
    simpa [Nat.add_assoc] using this
  have hv1 : LoopSemStateFiniteExact.eval st2 v1 = some (.word a) := by
    refine LoopSemStateFiniteExact.nested_seq_pure_evaluation c1 c2 t st2 st1 l n1 v1
      (.word a) ck1 ck2 ⟨by rw [Nat.add_comm]; exact h1, by rw [Nat.add_comm]; exact h2,
        hokA, hlA ▸ hokB, ?_, ?_, ?_, by simpa [wlabWlocExact] using h1v⟩
    · intro n hn
      exact (comp_exp_assigned_vars_tmp_bound ctxt tmp l e1 c1 v1 n1 l1 n ⟨hA, hn⟩).2
    · intro n hn
      exact (comp_exp_assigned_vars_tmp_bound ctxt n1 l1 e2 c2 v2 n2 l2 n ⟨hB, hn⟩).1
    · intro n hn
      have := compile_exp_le_tmp_domain ctxt tmp l e1 c1 v1 n1 l1 n
        ⟨hl.2.1, hA, hv, fun k hk => ?_, hn⟩
      · exact ⟨this.1, hlA ▸ this.2⟩
      · obtain ⟨w, hw⟩ := crepEval_some_var_cexp_local_lookup s e1 _ k ⟨he1, hk⟩
        obtain ⟨m, hm1, hm2, _⟩ := hl.2.2.2 k w hw
        exact ⟨m, hm1, hm2⟩
  have hv2 : LoopSemStateFiniteExact.eval
      (LoopSemStateFiniteExact.setVar n2 (.word a) st2) v2 = some (.word b) := by
    rw [eval_setVar_untouched st2 v2 n2 _ ?_]
    · simpa [wlabWlocExact] using h2v
    · intro k hk
      exact (compile_exp_le_tmp_domain ctxt n1 l1 e2 c2 v2 n2 l2 k
        ⟨h1l.2.1, hB, Nat.lt_of_lt_of_le hv htA, fun x hx => by
          obtain ⟨w, hw⟩ := crepEval_some_var_cexp_local_lookup s e2 _ x ⟨he2, hx⟩
          obtain ⟨m, hm1, hm2, _⟩ := h1l.2.2.2 x w hw
          exact ⟨m, hm1, hm2⟩, hk⟩).1
  have hmul : BitVec.ofNat width (a.toNat * b.toNat) = a * b := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul]
  have hvm : ctxt.vmax < n2 := by omega
  refine ⟨ck1 + ck2, LoopSemStateFiniteExact.setVar d
      (.word (BitVec.ofNat width (a.toNat * b.toNat)))
      (LoopSemStateFiniteExact.setVar (n2 + 2)
        (.word (BitVec.ofNat width (a.toNat * b.toNat / 2 ^ width)))
        (LoopSemStateFiniteExact.setVar (n2 + 1) (.word b)
          (LoopSemStateFiniteExact.setVar n2 (.word a) st2))), ?_, ?_, h2s, h2m, h2g, h2c, ?_⟩
  · simp only [List.append_assoc, List.append_nil, List.nil_append, List.zipWith,
      List.range_succ, List.range_zero, List.nil_append, List.cons_append]
    rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none c1 _ _ _ h1ck,
      LoopSemStateFiniteExact.evaluate_nested_seq_append_none c2 _ _ _ h2]
    simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq]
    simp only [LoopSemStateFiniteExact.evaluate, hv1, Nat.add_zero, hv2]
    simp only [LoopSemStateFiniteExact.loopArith, LoopSemStateFiniteExact.setVar,
      sptLookup_sptInsert, if_true, show ¬ n2 = n2 + 1 by omega, if_false]
  · simp [LoopSemStateFiniteExact.eval, LoopSemStateFiniteExact.setVar, sptLookup_sptInsert,
      wlabWlocExact, hmul]
  · refine locals_rel_update ctxt l2 _ s.locals st2.locals _ h2l ?_ ?_ ?_
    · intro k hk
      simp only [LoopSemStateFiniteExact.setVar, sptMem_sptInsert]
      rcases (sptMem_sptInsert k d () _).mp hk with hk | hk
      · exact Or.inl hk
      · rcases sptMem_sptListInsert_cases k _ _ hk with hk | hk
        · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
          rw [List.mem_range] at hj
          have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
          rcases this with rfl | rfl | rfl
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (h2l.2.2.1 k hk))))
    · intro k hk
      exact (sptMem_sptInsert k d () _).mpr (Or.inr (sptMem_sptListInsert_of k _ _ hk))
    · intro n hn
      simp only [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- `comp_exp_preserves_eval`, case `Cmp cmp e e'`
    (`crep_to_loopProofScript.sml:772-786` statement; case proof at 1128-1233),
    with the `eval_ind` hypotheses for both operands.  The `If` of `prog_if`
    consumes one tick in `cut_res`, so the clock witness is HOL's `ck + ck' + 1`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_preserves_eval"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_comp_exp_preserves_eval_cmp {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) (cmp : Cmp)
      (e1 e2 : CrepExpHOL width),
      crepToLoopCompExpPreservesEvalAt s e1 → crepToLoopCompExpPreservesEvalAt s e2 →
    ∀ (v : HolWordLab width) (t : LoopSemStateFiniteExact width σ)
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet),
      evalCrepSemHOLExp s (.cmp cmp e1 e2) = some v ∧
        crepToLoopStateRelExact s t ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        crepToLoopCodeRelExact ctxt s.code t.code ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
        compileExpHOLExact ctxt tmp l (.cmp cmp e1 e2) = (p, le, ntmp, nl) ∧
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
  intro s cmp e1 e2 ih1 ih2 v t ctxt tmp l p le ntmp nl ⟨he, hs, hm, hg, hc, hl, hcomp, hv⟩
  cases he1 : evalCrepSemHOLExp s e1 with
  | none => simp [evalCrepSemHOLExp, he1] at he
  | some a1 =>
  cases a1 with
  | word w1 =>
  cases he2 : evalCrepSemHOLExp s e2 with
  | none => simp [evalCrepSemHOLExp, he1, he2] at he
  | some a2 =>
  cases a2 with
  | word w2 =>
  have hvx : v = .word (Compiler.Encoders.Asm.wordCmpResultHOL cmp w1 w2) := by
    simp [evalCrepSemHOLExp, he1, he2] at he; exact he.symm
  subst hvx
  rcases hA : compileExpHOLExact ctxt tmp l e1 with ⟨c1, lv, n1, l1⟩
  rcases hB : compileExpHOLExact ctxt n1 l1 e2 with ⟨c2, rv, n2, l2⟩
  rw [compileExpHOLExact, hA] at hcomp
  simp only [hB, Prod.mk.injEq] at hcomp
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hcomp
  obtain ⟨hokA, htA, hlA⟩ := compile_exp_out_rel ctxt tmp l e1 c1 lv n1 l1 hA
  obtain ⟨hokB, htB, hlB⟩ := compile_exp_out_rel ctxt n1 l1 e2 c2 rv n2 l2 hB
  obtain ⟨ck1, st1, h1, h1v, h1s, h1m, h1g, h1c, h1l⟩ :=
    ih1 (.word w1) t ctxt tmp l c1 lv n1 l1 ⟨he1, hs, hm, hg, hc, hl, hA, hv⟩
  obtain ⟨ck2, st2, h2, h2v, h2s, h2m, h2g, h2c, h2l⟩ :=
    ih2 (.word w2) st1 ctxt n1 l1 c2 rv n2 l2
      ⟨he2, h1s, h1m, h1g, h1c, h1l, hB, Nat.lt_of_lt_of_le hv htA⟩
  have h1ck : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL c1)
      { t with clock := t.clock + (ck1 + ck2 + 1) } =
        (none, { st1 with clock := st1.clock + (ck2 + 1) }) := by
    have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ (ck2 + 1) h1 (by simp)
    simpa [Nat.add_assoc] using this
  have h2ck : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL c2)
      { st1 with clock := st1.clock + (ck2 + 1) } =
        (none, { st2 with clock := st2.clock + 1 }) := by
    have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ 1 h2 (by simp)
    simpa [Nat.add_assoc] using this
  have hlv : LoopSemStateFiniteExact.eval st2 lv = some (.word w1) := by
    refine LoopSemStateFiniteExact.nested_seq_pure_evaluation c1 c2 t st2 st1 l n1 lv
      (.word w1) ck1 ck2 ⟨by rw [Nat.add_comm]; exact h1, by rw [Nat.add_comm]; exact h2,
        hokA, hlA ▸ hokB, ?_, ?_, ?_, by simpa [wlabWlocExact] using h1v⟩
    · intro n hn
      exact (comp_exp_assigned_vars_tmp_bound ctxt tmp l e1 c1 lv n1 l1 n ⟨hA, hn⟩).2
    · intro n hn
      exact (comp_exp_assigned_vars_tmp_bound ctxt n1 l1 e2 c2 rv n2 l2 n ⟨hB, hn⟩).1
    · intro n hn
      have := compile_exp_le_tmp_domain ctxt tmp l e1 c1 lv n1 l1 n
        ⟨hl.2.1, hA, hv, fun k hk => ?_, hn⟩
      · exact ⟨this.1, hlA ▸ this.2⟩
      · obtain ⟨w, hw⟩ := crepEval_some_var_cexp_local_lookup s e1 _ k ⟨he1, hk⟩
        obtain ⟨m, hm1, hm2, _⟩ := hl.2.2.2 k w hw
        exact ⟨m, hm1, hm2⟩
  have hrvt : ∀ k, k ∈ holLoopLocalsTouched rv → k < n2 + 1 := by
    intro k hk
    have := (compile_exp_le_tmp_domain ctxt n1 l1 e2 c2 rv n2 l2 k
      ⟨h1l.2.1, hB, Nat.lt_of_lt_of_le hv htA, fun x hx => by
        obtain ⟨w, hw⟩ := crepEval_some_var_cexp_local_lookup s e2 _ x ⟨he2, hx⟩
        obtain ⟨m, hm1, hm2, _⟩ := h1l.2.2.2 x w hw
        exact ⟨m, hm1, hm2⟩, hk⟩).1
    omega
  -- the state after both operands, with the extra tick for the `If` cut
  let s2 : LoopSemStateFiniteExact width σ := { st2 with clock := st2.clock + 1 }
  have hv1' : LoopSemStateFiniteExact.eval s2 lv = some (.word w1) := by
    simp only [s2, LoopSemStateFiniteExact.eval_upd_clock_eq, hlv]
  have hv2' : LoopSemStateFiniteExact.eval
      (LoopSemStateFiniteExact.setVar (n2 + 1) (.word w1) s2) rv = some (.word w2) := by
    rw [eval_setVar_untouched _ rv (n2 + 1) _ hrvt]
    simp only [s2, LoopSemStateFiniteExact.eval_upd_clock_eq]
    simpa [wlabWlocExact] using h2v
  have hvm : ctxt.vmax < n1 := Nat.lt_of_lt_of_le hv htA
  have hvm2 : ctxt.vmax < n2 := Nat.lt_of_lt_of_le hvm htB
  let r := Compiler.Encoders.Asm.wordCmpResultHOL cmp w1 w2
  let s3 := LoopSemStateFiniteExact.setVar (n2 + 2) (.word w2)
    (LoopSemStateFiniteExact.setVar (n2 + 1) (.word w1) s2)
  let s4 := LoopSemStateFiniteExact.setVar (n2 + 1) (.word r) s3
  let L := sptListInsert [n2 + 1, n2 + 2] l2
  have hLmem : ∀ k, sptMem k L ↔ k = n2 + 2 ∨ k = n2 + 1 ∨ sptMem k l2 := by
    intro k; simp only [L, sptListInsert, sptMem_sptInsert]
  have hs4mem : ∀ k, sptMem k L → sptMem k s4.locals := by
    intro k hk
    simp only [s4, s3, s2, LoopSemStateFiniteExact.setVar, sptMem_sptInsert]
    rcases (hLmem k).mp hk with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (h2l.2.2.1 k h)))
  have hite : LoopSemStateFiniteExact.evaluate
      (.ite cmp (n2 + 1) (.reg (n2 + 2)) (.assign (n2 + 1) (.const 1))
        (.assign (n2 + 1) (.const 0)) L) s3 =
      (none, { st2 with locals := sptInter s4.locals L }) := by
    have hbr : LoopSemStateFiniteExact.evaluate
        (.ite cmp (n2 + 1) (.reg (n2 + 2)) (.assign (n2 + 1) (.const 1))
          (.assign (n2 + 1) (.const 0)) L) s3 =
        LoopSemStateFiniteExact.cutRes L (none, s4) := by
      rw [LoopSemStateFiniteExact.evaluate]
      simp only [s4, s3, LoopSemStateFiniteExact.setVar, LoopSemStateFiniteExact.getVarImm,
        sptLookup_sptInsert, if_true, show ¬ n2 + 1 = n2 + 2 by omega, if_false]
      by_cases hcmp : Compiler.Encoders.Asm.wordCmpHOL cmp w1 w2 = true <;>
        simp [hcmp, r, Compiler.Encoders.Asm.wordCmpResultHOL, LoopSemStateFiniteExact.evaluate,
          LoopSemStateFiniteExact.eval, LoopSemStateFiniteExact.setVar]
    rw [hbr, LoopSemStateFiniteExact.cutRes]
    simp only
    rw [LoopSemStateFiniteExact.cutState_of_subset L s4 hs4mem]
    simp [s4, s3, s2, LoopSemStateFiniteExact.setVar, LoopSemStateFiniteExact.decClock]
  refine ⟨ck1 + ck2 + 1, { st2 with locals := sptInter s4.locals L }, ?_, ?_, h2s, h2m, h2g,
    h2c, ?_⟩
  · simp only [progIfHOLExact, List.append_assoc]
    rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none c1 _ _ _ h1ck,
      LoopSemStateFiniteExact.evaluate_nested_seq_append_none c2 _ _ _ h2ck]
    simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq]
    have ha1 : LoopSemStateFiniteExact.evaluate (.assign (n2 + 1) lv) s2 =
        (none, LoopSemStateFiniteExact.setVar (n2 + 1) (.word w1) s2) := by
      simp [LoopSemStateFiniteExact.evaluate, hv1']
    have ha2 : LoopSemStateFiniteExact.evaluate (.assign (n2 + 2) rv)
        (LoopSemStateFiniteExact.setVar (n2 + 1) (.word w1) s2) = (none, s3) := by
      simp [LoopSemStateFiniteExact.evaluate, hv2', s3]
    change (match LoopSemStateFiniteExact.evaluate (.assign (n2 + 1) lv) s2 with
      | (none, s1) =>
        match LoopSemStateFiniteExact.evaluate (HolLoopProg.assign (n2 + 2) rv) s1 with
        | (none, s1) =>
          match LoopSemStateFiniteExact.evaluate
              (HolLoopProg.ite cmp (n2 + 1) (RegImm.reg (n2 + 2)) (.assign (n2 + 1) (.const 1))
                (.assign (n2 + 1) (.const 0)) L) s1 with
          | (none, s1) => LoopSemStateFiniteExact.evaluate HolLoopProg.skip s1
          | (res, s1) => (res, s1)
        | (res, s1) => (res, s1)
      | (res, s1) => (res, s1)) = _
    rw [ha1]; simp only; rw [ha2]; simp only; rw [hite]; simp only
    rw [LoopSemStateFiniteExact.evaluate]
  · have hL1 : (sptLookup (n2 + 1) L).isSome := (hLmem (n2 + 1)).mpr (Or.inr (Or.inl rfl))
    simp only [LoopSemStateFiniteExact.eval, sptLookup_sptInter, hL1, if_true]
    simp [s4, LoopSemStateFiniteExact.setVar, sptLookup_sptInsert, wlabWlocExact, r]
  · refine ⟨h2l.1, h2l.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
    · have hk' : (sptLookup k L).isSome := hk
      show (sptLookup k (sptInter s4.locals L)).isSome
      rw [sptLookup_sptInter, if_pos hk']
      exact hs4mem k hk
    · obtain ⟨n, h1, h2, h3⟩ := h2l.2.2.2 vn val hval
      have hn := h2l.2.1 vn n h1
      have hnL : (sptLookup n L).isSome := (hLmem n).mpr (Or.inr (Or.inr h2))
      refine ⟨n, h1, hnL, ?_⟩
      show sptLookup n (sptInter s4.locals L) = _
      rw [sptLookup_sptInter, if_pos hnL]
      simp only [s4, s3, s2, LoopSemStateFiniteExact.setVar, sptLookup_sptInsert]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      exact h3

/-! ## Op-case clause projections (flapjack-luna-c, bead `flapjack-pxn.18.5.6.33.15.6`) -/

section OpClauses

variable {width : Nat} [NeZero width] {ffiState : Type}

/-- Flapjack-only projection of the exact Crep `eval_def` Op clause. The exact
    evaluator internally fixes classical decidability for the Prop-valued
    memory domain, so its HOL-facing type and this helper require no
    `DecidablePred` premise. -/
theorem evalCrepSemHOLExp_op_clause (state : CrepSemHOLState width ffiState)
    (operator : BinOp)
    (expressions : List (CrepExpHOL width)) (values : List (BitVec width))
    (hvalues : expressions.mapM (evalCrepSemHOLExp state) =
      some (values.map HolWordLab.word)) :
    evalCrepSemHOLExp state (.op operator expressions) =
      (wordOpHOL operator values).map HolWordLab.word := by
  simp [evalCrepSemHOLExp, hvalues, Function.comp_def]

/-- Flapjack-only projection of the exact Loop `eval_def` Op clause. -/
theorem loopEvalHOLExact_op_clause {F : Type}
    (state : LoopSemStateFiniteExact width F) (operator : BinOp)
    (expressions : List (HolLoopExp width)) (values : List (BitVec width))
    (hvalues : theWords (expressions.map (LoopSemStateFiniteExact.eval state)) =
      some values) :
    LoopSemStateFiniteExact.eval state (.op operator expressions) =
      (wordOpHOL operator values).map WordLocW.word := by
  simp [LoopSemStateFiniteExact.eval, hvalues]

end OpClauses

/-! ## Assembly over HOL's `eval_ind` cases -/

/-- Flapjack helper (no HOL declaration): HOL `comp_exp_preserves_eval`'s
    `ho_match_mp_tac crepSemTheory.eval_ind` assembly of the case pieces, by strong
    induction on the expression size (sub-expressions of every `eval_ind` case are
    strictly smaller), given the `Op` case in the same hypothesis shape as the
    `Crepop` piece.  The tagged assembled theorem instantiates `hop` with the `Op`
    piece (bead `flapjack-pxn.18.5.6.33.15.6`). -/
theorem crepToLoopCompExpPreservesEvalOfOp {width : Nat} [NeZero width] {σ : Type}
    (hop : ∀ (s : CrepSemHOLState width σ) (bop : BinOp) (es : List (CrepExpHOL width)),
      (∀ e ∈ es, crepToLoopCompExpPreservesEvalAt s e) →
      crepToLoopCompExpPreservesEvalAt s (.op bop es)) :
    ∀ (s : CrepSemHOLState width σ) (e : CrepExpHOL width),
      crepToLoopCompExpPreservesEvalAt s e := by
  intro s
  have key : ∀ (n : Nat) (e : CrepExpHOL width), sizeOf e = n →
      crepToLoopCompExpPreservesEvalAt s e := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ihn =>
      intro e hn
      have ih : ∀ e', sizeOf e' < sizeOf e → crepToLoopCompExpPreservesEvalAt s e' :=
        fun e' h => ihn _ (hn ▸ h) e' rfl
      clear ihn hn
      cases e with
      | const w =>
        exact fun v t ctxt tmp l p le ntmp nl ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
          compExpPreservesEval_const_case s w v t ctxt tmp l p le ntmp nl h1 h2 h3 h4 h5 h6 h7 h8
      | var x =>
        exact fun v t ctxt tmp l p le ntmp nl ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
          compExpPreservesEval_var_case s x v t ctxt tmp l p le ntmp nl h1 h2 h3 h4 h5 h6 h7 h8
      | loadGlob g =>
        exact fun v t ctxt tmp l p le ntmp nl ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
          compExpPreservesEval_loadGlob_case s g v t ctxt tmp l p le ntmp nl h1 h2 h3 h4 h5 h6 h7 h8
      | baseAddr =>
        exact fun v t ctxt tmp l p le ntmp nl ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
          compExpPreservesEval_baseAddr_case s v t ctxt tmp l p le ntmp nl h1 h2 h3 h4 h5 h6 h7 h8
      | topAddr =>
        exact fun v t ctxt tmp l p le ntmp nl ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
          compExpPreservesEval_topAddr_case s v t ctxt tmp l p le ntmp nl h1 h2 h3 h4 h5 h6 h7 h8
      | load a =>
        have iha := ih a (by simp)
        exact fun v t ctxt tmp l p le ntmp nl ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
          compExpPreservesEval_load_case s a v t ctxt tmp l p le ntmp nl h1 h2 h3 h4 h5 h6 h7 h8
            (fun av ac ar an al g1 g2 g3 g4 g5 g6 g7 g8 =>
              iha av t ctxt tmp l ac ar an al ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩)
      | loadByte a =>
        exact crepToLoop_comp_exp_preserves_eval_loadByte s a (ih a (by simp))
      | load32 a =>
        exact crepToLoop_comp_exp_preserves_eval_load32 s a (ih a (by simp))
      | op bop es =>
        exact hop s bop es fun e he => ih e (by
          have := List.sizeOf_lt_of_mem he; simp only [CrepExpHOL.op.sizeOf_spec]; omega)
      | crepOp bop es =>
        exact crepToLoop_comp_exp_preserves_eval_crepOp s bop es fun e he => ih e (by
          have := List.sizeOf_lt_of_mem he; simp only [CrepExpHOL.crepOp.sizeOf_spec]; omega)
      | cmp c e1 e2 =>
        exact crepToLoop_comp_exp_preserves_eval_cmp s c e1 e2 (ih e1 (by simp; omega))
          (ih e2 (by simp; omega))
      | shift sh e1 e2 =>
        exact crepToLoop_comp_exp_preserves_eval_shift s sh e1 e2 (ih e1 (by simp; omega))
          (ih e2 (by simp; omega))
  exact fun e => key _ e rfl

end Flapjack
