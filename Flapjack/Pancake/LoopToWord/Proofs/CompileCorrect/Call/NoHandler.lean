import Flapjack.HolRef
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call.Support
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
# `Call_NOhandler` piece of `loop_to_word`'s `compile_correct`

This is the returning `Call` without a handler: HOL `compile_correct[Call]`
with `ret = SOME (ns, live)` and `handler = NONE`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:1017-1082`, and
`Call_NOhandler` at `:1154-1222`), bead `flapjack-pxn.18.5.9.27.2`.  The piece
is HOL's `evaluate_ind` `Call` conjunct at that `ret` and `handler`.  It takes
the one induction hypothesis that is not vacuous there, the callee body
hypothesis, transcribed with `ret` substituted.  The goal is written out as
in `CompileCorrect/Base.lean`.  The assembling `Call` theorem is bead
`flapjack-pxn.18.5.9.27.4`.
-/

namespace Flapjack

open LoopToWord.CompileCorrect

namespace LoopToWordCompileCorrectCallNoHandlerWitnesses

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

end LoopToWordCompileCorrectCallNoHandlerWitnesses

/-- Genuine `Call_NOhandler` piece of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:1017-1082` and
    `:1154-1222`). -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation :=
    [LoopSemStateFiniteExact.globals, WordSemStateFiniteExact.fpRegs,
      WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Call_NOhandler {width : Nat} [NeZero width] {C F : Type}
    (ns : List Nat) (live : NumSet) (dest : Option Nat) (argvars : List Nat) (s : LoopSemStateFiniteExact width F)
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
      LoopSemStateFiniteExact.evaluate (.call (some (ns, live)) dest argvars none) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ k, sptMem k (accVarsHOL (width := width) (.call (some (ns, live)) dest argvars none) .ln) → sptMem k ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.call (some (ns, live)) dest argvars none) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, hNE, hState, hLocals, hRetv, hgd, hWord, hAcc⟩
  have hState' := hState
  obtain ⟨len, hm, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := hState'
  have hcall := (WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C)
    (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hnsctx : ∀ k, k ∈ ns → sptMem k ctxt := fun k hk => hAcc k (by
    simp only [accVarsHOL]
    exact (sptMem_sptListInsert_iff k ns .ln).mpr (Or.inl hk))
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
  rw [hcall]
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
              (WordSemStateFiniteExact.pushEnv (result, Spt.ln) none
                (WordSemStateFiniteExact.decClock t))) = (res1, t1) ∧
          t1.ffi = st.ffi ∧
          resultCase ctxt1 (.loc l.1 l.2) (WordSemStateFiniteExact.callEnv args1 ss1
              (WordSemStateFiniteExact.pushEnv (result, Spt.ln) none
                (WordSemStateFiniteExact.decClock t))) r st res1 t1 := by
      intro r st h hne
      exact ihs r st _ ctxt1 (.loc l.1 l.2) l1 ⟨h, hne,
        ⟨len, hm, hmd, hsmd, by simp [WordSemStateFiniteExact.callEnv,
          WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock,
          LoopSemStateFiniteExact.decClock, hclock], hbe, hffi, hcur, hlen, htop, hglob, hcode⟩,
        hl1, h0, hgd, by simp [wordSemIsWordLoc], hacc1⟩
    have hpush : (WordSemStateFiniteExact.pushEnv (result, Spt.ln) none
        (WordSemStateFiniteExact.decClock t)).stack =
        .stackFrame t.localsSize (sptToAList result) [] none :: t.stack := by
      have hx := LoopToWord.envToListLNIMPHOL (width := width) t.permute _ _ (Prod.eta _).symm
      simp [WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock, hx]
    have hjmp : ∀ (t1 : WordSemStateFiniteExact width C F) p,
        WordSemStateFiniteExact.jumpExc { t1 with stack := t.stack, handler := t.handler } =
          some p →
        WordSemStateFiniteExact.jumpExc
          { t1 with stack := .stackFrame t.localsSize (sptToAList result) [] none :: t.stack,
                    handler := t.handler } = some p := by
      intro t1 p h
      unfold WordSemStateFiniteExact.jumpExc at h ⊢
      simp only at h ⊢
      split at h
      · rename_i hlt
        rw [if_pos (by simp; omega), LoopToWord.wordSemLastN_add_cons _ _ _ (by omega)]
        exact h
      · cases h
    split at hEval
    · -- Result
      rename_i retvs st heq
      rw [LoopSemStateFiniteExact.fix_clock_evaluate] at heq
      split at hEval
      · simp only [Prod.mk.injEq] at hEval
        exact absurd hEval.1.symm hNE
      rename_i hlen
      simp only [Prod.mk.injEq] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      obtain ⟨t1, res1, he, hf1, hst, hres1, hstk, hhd⟩ := hIH _ _ heq (by simp)
      subst hres1
      rw [he]
      have hlen' : ¬ retvs.length ≠ (ns.map (LoopToWord.findVarHOL ctxt)).length := by
        simpa using hlen
      have hpop : WordSemStateFiniteExact.popEnv t1 = some { t1 with
          locals := sptUnion (sptFromAList []) (sptFromAList (sptToAList result)),
          stack := t.stack, localsSize := t.localsSize } := by
        unfold WordSemStateFiniteExact.popEnv
        rw [hstk]
        simp only [WordSemStateFiniteExact.callEnv]
        rw [hpush]
      have hdom : sptDomainEqUnion (sptUnion (sptFromAList [])
          (sptFromAList (sptToAList result))) result (Spt.ln : Spt (WordLocW width)) := by
        intro k
        simp [sptUnion, sptFromAList, sptMem_iff_lookup, sptLookup_sptFromAList_sptToAList,
          sptLookup]
      have hskip := (WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C)
        (F := F)).1
      simp only [ne_eq, not_true_eq_false, false_or, hlen', if_false, hpop]
      simp only [if_pos hdom, hskip]
      have h0ns : 0 ∉ ns.map (LoopToWord.findVarHOL ctxt) := by
        intro hmem
        obtain ⟨n, hn, h⟩ := List.mem_map.mp hmem
        exact LoopToWord.findVarHOL_ne_zero ctxt s.locals t.locals n ⟨hnsctx n hn, hLocals⟩ h
      obtain ⟨len', e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hst
      refine ⟨_, none, rfl, ?_, ⟨len', e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩, rfl,
        ?_, ?_, ?_, ?_⟩
      · simpa [WordSemStateFiniteExact.setVars, LoopSemStateFiniteExact.setVars] using hf1
      · simp only [WordSemStateFiniteExact.setVars]
        rw [LoopSemStateFiniteExact.sptLookup_sptAlistInsert_not_mem 0 _ _ _ h0ns]
        simpa [sptUnion, sptFromAList, sptLookup_sptFromAList_sptToAList] using h0r
      · have h := LoopToWord.localsRelHOLAlistInsertToAList ctxt ns retvs
          (sptInter s.locals live) result ⟨hlr, hnsctx⟩
        simp only [WordSemStateFiniteExact.setVars, LoopSemStateFiniteExact.setVars, sptUnion,
          sptFromAList]
        exact h
      · simp [WordSemStateFiniteExact.setVars]
      · simp only [WordSemStateFiniteExact.setVars]
        exact hhd
    · -- Exception
      rename_i exn st heq
      rw [LoopSemStateFiniteExact.fix_clock_evaluate] at heq
      simp only [Prod.mk.injEq] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      obtain ⟨t1, res1, he, hf1, hst, himp, hj⟩ := hIH _ _ heq (by simp)
      rw [he]
      obtain ⟨len', e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hst
      have hrc : resultCase ctxt retv t (some (.exception exn))
          { st with locals := Spt.ln } res1 t1 :=
        ⟨⟨len', e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩, himp, fun r a b h => by
          apply hj r a b
          have e : (WordSemStateFiniteExact.callEnv args1 ss1
              (WordSemStateFiniteExact.pushEnv (result, Spt.ln) none
                (WordSemStateFiniteExact.decClock t))).stack =
              .stackFrame t.localsSize (sptToAList result) [] none :: t.stack := hpush
          rw [e]
          exact hjmp t1 _ h⟩
      by_cases hE : res1 = some .error
      · subst hE
        exact ⟨t1, _, rfl, hf1, hrc⟩
      · obtain ⟨u1, u2, rfl⟩ := himp hE
        exact ⟨t1, _, rfl, hf1, hrc⟩
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
