import Flapjack.HolRef
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call.HandlerTail
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelLookups
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelUpdates
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelAllDistinct
import Flapjack.Pancake.Proofs.LoopToWord.CutsetDomain
import Flapjack.Pancake.Proofs.LoopToWord.CutEnvSupport
import Flapjack.Pancake.Proofs.LoopToWord.LastNAddCons
import Flapjack.Pancake.Proofs.LoopToWord.FindVar
import Flapjack.Pancake.Semantics.LoopProps.EvalExact
import Flapjack.Pancake.Semantics.LoopProps.AccVars

/-!
# `Call_SOMEhandler` piece of `loop_to_word`'s `compile_correct`

This is the returning `Call` with a handler: HOL `compile_correct[Call]` with
`ret = SOME (ns, live)` and `handler = SOME (hn, hh, hr, lo)`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:1017-1082`, and
`Call_SOMEhandler` at `:1223-1407`), bead `flapjack-pxn.18.5.9.27.3`.  The
piece is HOL's `evaluate_ind` `Call` conjunct at that `ret` and `handler`.
It takes the three induction hypotheses that are not vacuous there:
* the Result-handler continuation;
* the Exception-handler continuation;
* the callee body.

They are transcribed with `ret` and `handler` substituted.  The goal is
written out as in `CompileCorrect/Base.lean`.  The assembling `Call` theorem
is bead `flapjack-pxn.18.5.9.27.4`.
-/

namespace Flapjack

open LoopToWord.CompileCorrect

namespace LoopToWordCompileCorrectCallSomeHandlerWitnesses

/-- Same-module roundtrip for the relation qualifier's loopSem state fields. -/
theorem holFmapAsFiniteSupportRelationWitness_LoopSemStateFiniteExact
    {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Same-module roundtrip for the relation qualifier's wordSem state fields. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end LoopToWordCompileCorrectCallSomeHandlerWitnesses

/-- Genuine `Call_SOMEhandler` piece of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:1017-1082` and
    `:1223-1407`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_Call_SOMEhandler {width : Nat} [NeZero width] {C F : Type}
    (ns : List Nat) (live : NumSet) (dest : Option Nat) (argvars : List Nat)
    (hn : Nat) (hh hr : HolLoopProg width) (lo : NumSet) (s : LoopSemStateFiniteExact width F)
    (ihR : ∀ (argvals : List (WordLocW width))
      (v7 : Spt (WordLocW width) × HolLoopProg width) (env : Spt (WordLocW width))
      (prog : HolLoopProg width) (v6 : List Nat × NumSet) (ns' : List Nat) (live' : NumSet)
      (v9 : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s' : LoopSemStateFiniteExact width F)
      (v8 : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (st : LoopSemStateFiniteExact width F) (v11 : LoopSemStateFiniteExact.LoopResultExact width)
      (retvs : List (WordLocW width)) (v : Nat × HolLoopProg width × HolLoopProg width × NumSet)
      (v1 : Nat) (v2 : HolLoopProg width × HolLoopProg width × NumSet) (v3 : HolLoopProg width)
      (v4 : HolLoopProg width × NumSet) (r : HolLoopProg width) (live_out : NumSet),
      LoopSemStateFiniteExact.getVars argvars s = some argvals ∧
        LoopSemStateFiniteExact.findCode dest argvals s.code = some v7 ∧ v7 = (env, prog) ∧
        some (ns, live) = some v6 ∧ v6 = (ns', live') ∧ ns'.Nodup ∧
        LoopSemStateFiniteExact.cutRes live' (none, s) = (v9, s') ∧ v9 = none ∧
        LoopSemStateFiniteExact.evaluate prog { s' with locals := env } = (v8, st) ∧
        v8 = some v11 ∧ v11 = .result retvs ∧ retvs.length = ns'.length ∧
        some (hn, hh, hr, lo) = some v ∧ v = (v1, v2) ∧ v2 = (v3, v4) ∧ v4 = (r, live_out) →
      PropertyAt C r (LoopSemStateFiniteExact.setVars ns' retvs { st with locals := s'.locals }))
    (ihE : ∀ (argvals : List (WordLocW width))
      (v7 : Spt (WordLocW width) × HolLoopProg width) (env : Spt (WordLocW width))
      (prog : HolLoopProg width) (v6 : List Nat × NumSet) (ns' : List Nat) (live' : NumSet)
      (v9 : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s' : LoopSemStateFiniteExact width F)
      (v8 : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (st : LoopSemStateFiniteExact width F) (v11 : LoopSemStateFiniteExact.LoopResultExact width)
      (exn : WordLocW width) (v : Nat × HolLoopProg width × HolLoopProg width × NumSet)
      (n : Nat) (v2 : HolLoopProg width × HolLoopProg width × NumSet) (h : HolLoopProg width)
      (v4 : HolLoopProg width × NumSet) (v5 : HolLoopProg width) (live_out : NumSet),
      LoopSemStateFiniteExact.getVars argvars s = some argvals ∧
        LoopSemStateFiniteExact.findCode dest argvals s.code = some v7 ∧ v7 = (env, prog) ∧
        some (ns, live) = some v6 ∧ v6 = (ns', live') ∧ ns'.Nodup ∧
        LoopSemStateFiniteExact.cutRes live' (none, s) = (v9, s') ∧ v9 = none ∧
        LoopSemStateFiniteExact.evaluate prog { s' with locals := env } = (v8, st) ∧
        v8 = some v11 ∧ v11 = .exception exn ∧
        some (hn, hh, hr, lo) = some v ∧ v = (n, v2) ∧ v2 = (h, v4) ∧ v4 = (v5, live_out) →
      PropertyAt C h (LoopSemStateFiniteExact.setVar n exn { st with locals := s'.locals }))
    (ih : ∀ (argvals : List (WordLocW width))
      (v7 : Spt (WordLocW width) × HolLoopProg width) (env : Spt (WordLocW width))
      (prog : HolLoopProg width) (v6 : List Nat × NumSet) (ns' : List Nat) (live' : NumSet)
      (v9 : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s' : LoopSemStateFiniteExact width F),
      LoopSemStateFiniteExact.getVars argvars s = some argvals ∧
        LoopSemStateFiniteExact.findCode dest argvals s.code = some v7 ∧ v7 = (env, prog) ∧
        some (ns, live) = some v6 ∧ v6 = (ns', live') ∧ ns'.Nodup ∧
        LoopSemStateFiniteExact.cutRes live' (none, s) = (v9, s') ∧ v9 = none →
      PropertyAt C prog { s' with locals := env }) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.call (some (ns, live)) dest argvars (some (hn, hh, hr, lo))) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ k, sptMem k (accVarsHOL (width := width) (.call (some (ns, live)) dest argvars (some (hn, hh, hr, lo))) .ln) → sptMem k ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.call (some (ns, live)) dest argvars (some (hn, hh, hr, lo))) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, hNE, hState, hLocals, hRetv, hgd, hWord, hAcc⟩
  have hState' := hState
  obtain ⟨len, hm, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := hState'
  have hcall := (WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C)
    (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hdomacc : ∀ k, sptMem k (accVarsHOL (width := width)
      (.call (some (ns, live)) dest argvars (some (hn, hh, hr, lo))) .ln) ↔
      sptMem k (accVarsHOL hh .ln) ∨ sptMem k (accVarsHOL hr .ln) ∨ k = hn ∨ k ∈ ns := by
    intro k
    have e1 := congrFun (accVarsAccHOL hh
      (accVarsHOL hr (sptInsert hn () (sptListInsert ns .ln)))) k
    have e2 := congrFun (accVarsAccHOL hr (sptInsert hn () (sptListInsert ns .ln))) k
    simp only [accVarsHOL]
    change sptDomain _ k ↔ _
    rw [e1]
    change sptMem k _ ∨ sptDomain _ k ↔ _
    rw [e2]
    change sptMem k _ ∨ sptMem k _ ∨ sptMem k _ ↔ _
    rw [sptMem_sptInsert, sptMem_sptListInsert_iff]
    have : ¬ sptMem k (Spt.ln : NumSet) := by simp [sptMem, sptDomain, sptLookup]
    simp [this]
  have hnsctx : ∀ k, k ∈ ns → sptMem k ctxt := fun k hk =>
    hAcc k ((hdomacc k).mpr (Or.inr (Or.inr (Or.inr hk))))
  have hhnctx : sptMem hn ctxt := hAcc hn ((hdomacc hn).mpr (Or.inr (Or.inr (Or.inl rfl))))
  have hhhctx : ∀ k, sptMem k (accVarsHOL hh .ln) → sptMem k ctxt := fun k hk =>
    hAcc k ((hdomacc k).mpr (Or.inl hk))
  have hhrctx : ∀ k, sptMem k (accVarsHOL hr .ln) → sptMem k ctxt := fun k hk =>
    hAcc k ((hdomacc k).mpr (Or.inr (Or.inl hk)))
  have hseq := (WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C)
    (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [LoopSemStateFiniteExact.evaluate] at hEval
  split at hEval
  · simp only [Prod.mk.injEq] at hEval
    exact absurd hEval.1.symm hNE
  rename_i argvals hgv
  split at hEval
  · simp only [Prod.mk.injEq] at hEval
    exact absurd hEval.1.symm hNE
  rename_i env prog hfc
  simp only at hEval
  by_cases hnnd : ¬ ns.Nodup
  · rw [if_pos hnnd] at hEval
    simp only [Prod.mk.injEq] at hEval
    exact absurd hEval.1.symm hNE
  rw [if_neg hnnd] at hEval
  have hnd : ns.Nodup := by simpa using hnnd
  obtain ⟨hwgv, -⟩ := LoopToWord.localsRelHOLGetVars ctxt s t argvars argvals ⟨hLocals, hgv⟩
  obtain ⟨args1, ss1, ctxt1, l1, hwf, h0, hl1, hacc1⟩ :=
    findCode_rel s.code t.code t.stackSize dest argvals env prog (.loc l.1 l.2) hcode hfc
  have hbad : wordSemBadDestArgs dest (argvars.map (LoopToWord.findVarHOL ctxt)) = false := by
    cases dest with
    | some _ => simp [wordSemBadDestArgs]
    | none =>
      cases argvars with
      | nil =>
        simp [LoopSemStateFiniteExact.getVars] at hgv
        subst hgv
        simp [LoopSemStateFiniteExact.findCode] at hfc
      | cons _ _ => simp [wordSemBadDestArgs]
  have hne : ¬ sptDomainEmpty (LoopToWord.mkNewCutsetHOL ctxt live) := fun h =>
    LoopToWord.domainMkNewCutsetNotEmpty ctxt live
      (funext fun k => propext ⟨fun hk => h k hk, False.elim⟩)
  have hndw : (ns.map (LoopToWord.findVarHOL ctxt)).Nodup :=
    LoopToWord.localsRelHOLAllDistinctMap ctxt s.locals t.locals ns ⟨hLocals, hnsctx, hnd⟩
  simp only [LoopToWord.compHOL]
  rw [hseq, hcall]
  simp only [hwgv, hbad, Bool.false_eq_true, if_false, wordSemAddRetLoc, hwf, hne, hndw,
    not_true_eq_false, or_self]
  have hcutw : ∀ cs, LoopSemStateFiniteExact.cutState live s = some cs →
      ∃ result, wordSemCutEnvs (LoopToWord.mkNewCutsetHOL ctxt live, .ln) t.locals =
          some (result, .ln) ∧
        LoopToWord.localsRelHOL ctxt (sptInter s.locals live) result ∧
        sptLookup 0 result = some retv ∧ cs = { s with locals := sptInter s.locals live } := by
    intro cs h
    unfold LoopSemStateFiniteExact.cutState at h
    split at h
    · rename_i hsub
      cases h
      obtain ⟨result, hce, hlr⟩ := LoopToWord.wordSemCutEnvMkNewCutsetHOL ctxt live s.locals
        t.locals retv ⟨hLocals, hsub, hRetv⟩
      exact ⟨result, LoopToWord.wordSemCutEnvLNIMPHOL _ _ _ hce, hlr,
        (LoopToWord.wordSemCutEnvMkNewCutsetIMPHOL ctxt live t.locals result hce).trans hRetv,
        rfl⟩
    · cases h
  split at hEval
  · rename_i s1c hcr
    have hc2 : ∃ cs, LoopSemStateFiniteExact.cutState live s = some cs ∧ s.clock ≠ 0 ∧
        s1c = LoopSemStateFiniteExact.decClock cs := by
      unfold LoopSemStateFiniteExact.cutRes at hcr
      simp only at hcr
      cases hcs : LoopSemStateFiniteExact.cutState live s with
      | none => simp [hcs] at hcr
      | some cs =>
        obtain ⟨_, _, _, _, rfl⟩ := hcutw _ hcs
        simp only [hcs] at hcr
        by_cases hz : s.clock = 0
        · simp [hz] at hcr
        · simp only [hz, if_false, Prod.mk.injEq, true_and] at hcr
          exact ⟨_, rfl, hz, hcr.symm⟩
    obtain ⟨cs, hcs, hz, rfl⟩ := hc2
    obtain ⟨result, hce, hlr, h0r, rfl⟩ := hcutw _ hcs
    rw [hce]
    simp only
    rw [if_neg (by rw [hclock]; exact hz)]
    have ihs := ih argvals (env, prog) env prog (ns, live) ns live none _
      ⟨hgv, hfc, rfl, rfl, rfl, hnd, hcr, rfl⟩
    have hIH : ∀ r st, LoopSemStateFiniteExact.evaluate prog
          { LoopSemStateFiniteExact.decClock { s with locals := sptInter s.locals live } with
              locals := env } = (r, st) → r ≠ some .error →
        ∃ t1 res1, WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt1 prog l1).fst
            (WordSemStateFiniteExact.callEnv args1 ss1
              (WordSemStateFiniteExact.pushEnv (result, Spt.ln)
                (some (LoopToWord.findVarHOL ctxt hn,
                  (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).fst,
                  (LoopToWord.compHOL ctxt hr (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).snd).snd))
                (WordSemStateFiniteExact.decClock t))) = (res1, t1) ∧
          t1.ffi = st.ffi ∧
          resultCase ctxt1 (.loc l.1 l.2) (WordSemStateFiniteExact.callEnv args1 ss1
              (WordSemStateFiniteExact.pushEnv (result, Spt.ln)
                (some (LoopToWord.findVarHOL ctxt hn,
                  (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).fst,
                  (LoopToWord.compHOL ctxt hr (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).snd).snd))
                (WordSemStateFiniteExact.decClock t))) r st res1 t1 := by
      intro r st h hne
      exact ihs r st _ ctxt1 (.loc l.1 l.2) l1 ⟨h, hne,
        ⟨len, hm, hmd, hsmd, by simp [WordSemStateFiniteExact.callEnv,
          WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock,
          LoopSemStateFiniteExact.decClock, hclock], hbe, hffi, hcur, hlen, htop, hglob, hcode⟩,
        hl1, h0, hgd, by simp [wordSemIsWordLoc], hacc1⟩
    have hpush : (WordSemStateFiniteExact.callEnv args1 ss1
              (WordSemStateFiniteExact.pushEnv (result, Spt.ln)
                (some (LoopToWord.findVarHOL ctxt hn, (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).fst,
                  (LoopToWord.compHOL ctxt hr (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).snd).snd))
                (WordSemStateFiniteExact.decClock t))).stack =
        .stackFrame t.localsSize (sptToAList result) [] (some (t.handler, (LoopToWord.compHOL ctxt hr (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).snd).snd.1, (LoopToWord.compHOL ctxt hr (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).snd).snd.2)) ::
          t.stack := by
      have hx := LoopToWord.envToListLNIMPHOL (width := width) t.permute _ _ (Prod.eta _).symm
      simp [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
        WordSemStateFiniteExact.decClock, hx]
    have hhand : (WordSemStateFiniteExact.callEnv args1 ss1
              (WordSemStateFiniteExact.pushEnv (result, Spt.ln)
                (some (LoopToWord.findVarHOL ctxt hn, (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).fst,
                  (LoopToWord.compHOL ctxt hr (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).snd).snd))
                (WordSemStateFiniteExact.decClock t))).handler = t.stack.length := by
      simp [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
        WordSemStateFiniteExact.decClock]
    have hdom : sptDomainEqUnion (sptUnion (sptFromAList [])
        (sptFromAList (sptToAList result))) result (Spt.ln : Spt (WordLocW width)) := by
      intro k
      simp [sptUnion, sptFromAList, sptMem_iff_lookup, sptLookup_sptFromAList_sptToAList,
        sptLookup]
    have h0ns : 0 ∉ ns.map (LoopToWord.findVarHOL ctxt) := by
      intro hmem
      obtain ⟨n, hn', h⟩ := List.mem_map.mp hmem
      exact LoopToWord.findVarHOL_ne_zero ctxt s.locals t.locals n ⟨hnsctx n hn', hLocals⟩ h
    split at hEval
    · -- Result
      rename_i retvs st heq
      rw [LoopSemStateFiniteExact.fix_clock_evaluate] at heq
      split at hEval
      · simp only [Prod.mk.injEq] at hEval
        exact absurd hEval.1.symm hNE
      rename_i hlen0
      have hlenEq : retvs.length = ns.length := by simpa using hlen0
      obtain ⟨t1, res1, he, hf1, hst, hres1, hstk, hhd⟩ := hIH _ _ heq (by simp)
      subst hres1
      rw [he]
      have hlen' : ¬ retvs.length ≠ (ns.map (LoopToWord.findVarHOL ctxt)).length := by
        simp [hlenEq]
      have hpop : WordSemStateFiniteExact.popEnv t1 = some { t1 with
          locals := sptUnion (sptFromAList []) (sptFromAList (sptToAList result)),
          stack := t.stack, localsSize := t.localsSize, handler := t.handler } := by
        unfold WordSemStateFiniteExact.popEnv
        rw [hstk, hpush]
      simp only [ne_eq, not_true_eq_false, false_or, hlen', if_false, hpop]
      simp only [if_pos hdom]
      obtain ⟨len', e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hst
      rcases hq : LoopSemStateFiniteExact.evaluate hr (LoopSemStateFiniteExact.setVars ns retvs
          { st with locals := (LoopSemStateFiniteExact.decClock
            { s with locals := sptInter s.locals live }).locals }) with ⟨q, s2⟩
      rw [hq] at hEval
      have hqne : q ≠ some .error := by
        intro hq'
        subst hq'
        simp only [LoopSemStateFiniteExact.cutRes, Prod.mk.injEq] at hEval
        exact hNE hEval.1.symm
      have ihr := ihR argvals (env, prog) env prog (ns, live) ns live none _ _ st _ retvs _ hn _
        hh _ hr lo ⟨hgv, hfc, rfl, rfl, rfl, hnd, hcr, rfl, heq, rfl, rfl, hlenEq, rfl, rfl, rfl,
          rfl⟩
      obtain ⟨t1', res1', he', hf', hrc'⟩ := ihr q s2
        (WordSemStateFiniteExact.setVars (ns.map (LoopToWord.findVarHOL ctxt)) retvs
          { t1 with
              locals := sptUnion (sptFromAList []) (sptFromAList (sptToAList result))
              stack := t.stack
              localsSize := t.localsSize
              handler := t.handler })
        ctxt retv (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).snd ⟨hq, hqne,
        ⟨len', e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩,
        by
          have h := LoopToWord.localsRelHOLAlistInsertToAList ctxt ns retvs
            (sptInter s.locals live) result ⟨hlr, hnsctx⟩
          simp only [WordSemStateFiniteExact.setVars, LoopSemStateFiniteExact.setVars, sptUnion,
            sptFromAList]
          exact h,
        by
          simp only [WordSemStateFiniteExact.setVars]
          rw [LoopSemStateFiniteExact.sptLookup_sptAlistInsert_not_mem 0 _ _ _ h0ns]
          simpa [sptUnion, sptFromAList, sptLookup_sptFromAList_sptToAList] using h0r,
        hgd, hWord, hhrctx⟩
      rw [he']
      exact handlerTail ctxt retv t _ lo q s2 res1' t1' res s1 hrc' hf' rfl rfl hEval hNE
    · -- Exception
      rename_i exn st heq
      rw [LoopSemStateFiniteExact.fix_clock_evaluate] at heq
      obtain ⟨t1, res1, he, hf1, hst, himp, hj⟩ := hIH _ _ heq (by simp)
      have hjx : WordSemStateFiniteExact.jumpExc
          { t1 with stack := (WordSemStateFiniteExact.callEnv args1 ss1
              (WordSemStateFiniteExact.pushEnv (result, Spt.ln)
                (some (LoopToWord.findVarHOL ctxt hn, (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).fst,
                  (LoopToWord.compHOL ctxt hr (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).snd).snd))
                (WordSemStateFiniteExact.decClock t))).stack, handler := (WordSemStateFiniteExact.callEnv args1 ss1
              (WordSemStateFiniteExact.pushEnv (result, Spt.ln)
                (some (LoopToWord.findVarHOL ctxt hn, (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).fst,
                  (LoopToWord.compHOL ctxt hr (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).snd).snd))
                (WordSemStateFiniteExact.decClock t))).handler } =
          some ({ t1 with
            locals := sptUnion (sptFromAList []) (sptFromAList (sptToAList result)),
            stack := t.stack, localsSize := t.localsSize, handler := t.handler },
            (LoopToWord.compHOL ctxt hr (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).snd).snd.1, (LoopToWord.compHOL ctxt hr (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).snd).snd.2) := by
        unfold WordSemStateFiniteExact.jumpExc
        simp only [hpush, hhand]
        rw [if_pos (by simp)]
        have hfull : wordSemLastN (t.stack.length + 1)
            (.stackFrame t.localsSize (sptToAList result) [] (some (t.handler, (LoopToWord.compHOL ctxt hr (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).snd).snd.1, (LoopToWord.compHOL ctxt hr (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).snd).snd.2)) ::
              t.stack) =
            .stackFrame t.localsSize (sptToAList result) [] (some (t.handler, (LoopToWord.compHOL ctxt hr (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).snd).snd.1, (LoopToWord.compHOL ctxt hr (LoopToWord.compHOL ctxt hh (l.fst, l.snd + 1)).snd).snd.2)) ::
              t.stack := by
          simp only [wordSemLastN, List.reverse_cons]
          rw [List.take_of_length_le (by simp)]
          simp
        rw [hfull]
      obtain ⟨hres1, hR0⟩ := hj _ _ _ hjx
      subst hres1
      rw [he]
      have hl1loc : t1.locals = sptUnion (sptFromAList []) (sptFromAList (sptToAList result)) := by
        rw [← hR0]
      have hl1stk : t1.stack = t.stack := by rw [← hR0]
      have hl1hd : t1.handler = t.handler := by rw [← hR0]
      simp only [ne_eq, not_true_eq_false, if_false, hl1loc]
      simp only [if_pos hdom]
      obtain ⟨len', e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hst
      rcases hq : LoopSemStateFiniteExact.evaluate hh (LoopSemStateFiniteExact.setVar hn exn
          { st with locals := (LoopSemStateFiniteExact.decClock
            { s with locals := sptInter s.locals live }).locals }) with ⟨q, s2⟩
      rw [hq] at hEval
      have hqne : q ≠ some .error := by
        intro hq'
        subst hq'
        simp only [LoopSemStateFiniteExact.cutRes, Prod.mk.injEq] at hEval
        exact hNE hEval.1.symm
      have ihe := ihE argvals (env, prog) env prog (ns, live) ns live none _ _ st _ exn _ hn _
        hh _ hr lo ⟨hgv, hfc, rfl, rfl, rfl, hnd, hcr, rfl, heq, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hhn0 := LoopToWord.findVarHOL_ne_zero ctxt s.locals t.locals hn ⟨hhnctx, hLocals⟩
      obtain ⟨t1', res1', he', hf', hrc'⟩ := ihe q s2
        (WordSemStateFiniteExact.setVar (LoopToWord.findVarHOL ctxt hn) exn t1)
        ctxt retv (l.fst, l.snd + 1) ⟨hq, hqne,
        ⟨len', e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩,
        by
          have h := LoopToWord.localsRelHOLAlistInsertToAList ctxt [hn] [exn]
            (sptInter s.locals live) result ⟨hlr, fun k hk => by
              simp only [List.mem_singleton] at hk
              subst hk
              exact hhnctx⟩
          simp only [WordSemStateFiniteExact.setVar, LoopSemStateFiniteExact.setVar, hl1loc,
            sptUnion, sptFromAList]
          simp only [LoopSemStateFiniteExact.sptAlistInsert, List.map_cons, List.map_nil] at h
          exact h,
        by
          simp only [WordSemStateFiniteExact.setVar, hl1loc]
          rw [sptLookup_sptInsert_ne _ _ _ _ (Ne.symm hhn0)]
          simpa [sptUnion, sptFromAList, sptLookup_sptFromAList_sptToAList] using h0r,
        hgd, hWord, hhhctx⟩
      rw [he']
      exact handlerTail ctxt retv t _ lo q s2 res1' t1' res s1 hrc' hf' hl1stk hl1hd hEval hNE
    all_goals first
      | (simp only [Prod.mk.injEq] at hEval; exact absurd hEval.1.symm hNE)
      | skip
    -- pass-through results
    rename_i hn1 hn2 hn3 hn4 hn5
    have hE0 := hEval
    rw [LoopSemStateFiniteExact.fix_clock_evaluate] at hEval
    obtain ⟨t1, res1, he, hf1, hrc⟩ := hIH _ _ hEval hNE
    rw [he]
    rcases res with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩
    all_goals first
      | exact (hn1 _ _ hE0).elim
      | exact (hn2 _ _ hE0).elim
      | exact (hn3 _ _ hE0).elim
      | exact (hn4 _ _ hE0).elim
      | exact (hn5 _ hE0).elim
      | exact (hn1 _ hE0).elim
      | exact (hn2 _ hE0).elim
      | exact (hn3 _ hE0).elim
      | exact (hn4 _ hE0).elim
      | exact (hn5 _ _ hE0).elim
      | exact absurd rfl hNE
      | (have hrc' : res1 = _ := hrc; subst hrc'; exact ⟨t1, _, rfl, hf1, rfl⟩)
  · rename_i hnone
    unfold LoopSemStateFiniteExact.cutRes at hEval
    simp only at hEval
    cases hcs : LoopSemStateFiniteExact.cutState live s with
    | none =>
      rw [hcs] at hEval
      simp only [Prod.mk.injEq] at hEval
      exact absurd hEval.1.symm hNE
    | some cs =>
      obtain ⟨result, hce, -, -, rfl⟩ := hcutw _ hcs
      simp only [hcs] at hEval
      by_cases hz : s.clock = 0
      · simp only [hz, if_true, Prod.mk.injEq] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        rw [hce]
        simp only
        rw [if_pos (by rw [hclock]; exact hz)]
        exact ⟨_, _, rfl, by simp [WordSemStateFiniteExact.flushState, hffi], rfl⟩
      · exfalso
        refine hnone (LoopSemStateFiniteExact.decClock
          { s with locals := sptInter s.locals live }) ?_
        unfold LoopSemStateFiniteExact.cutRes
        simp [hcs, hz]

end Flapjack
