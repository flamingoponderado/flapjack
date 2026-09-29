import Flapjack.HolRef
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call.Support
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelLookups

/-!
# `Call_TailCall` piece of `loop_to_word`'s `compile_correct`

This is the `ret = NONE` sub-resume of HOL `compile_correct[Call]`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:1017-1030` and
`Call_TailCall` at `:1085-1153`), bead `flapjack-pxn.18.5.9.27.1`.  The piece
is HOL's `evaluate_ind` `Call` conjunct with `ret` fixed to `NONE`.  It takes
the one induction hypothesis that is not vacuous for `ret = NONE`, the
tail-call body hypothesis, transcribed with that `ret` substituted.  The
goal is written out as in `CompileCorrect/Base.lean`.  The assembling `Call`
theorem is bead `flapjack-pxn.18.5.9.27.4`.
-/

namespace Flapjack

open LoopToWord.CompileCorrect

namespace LoopToWordCompileCorrectCallTailWitnesses

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

end LoopToWordCompileCorrectCallTailWitnesses

/-- Genuine `Call_TailCall` piece of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:1017-1030` and
    `:1085-1153`). -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation :=
    [LoopSemStateFiniteExact.globals, WordSemStateFiniteExact.fpRegs,
      WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_Call_TailCall {width : Nat} [NeZero width] {C F : Type}
    (dest : Option Nat) (argvars : List Nat)
    (handler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet)) (s : LoopSemStateFiniteExact width F)
    (ih : ∀ (argvals : List (WordLocW width))
      (v7 : Spt (WordLocW width) × HolLoopProg width) (env : Spt (WordLocW width))
      (prog : HolLoopProg width),
      LoopSemStateFiniteExact.getVars argvars s = some argvals ∧
        LoopSemStateFiniteExact.findCode dest argvals s.code = some v7 ∧ v7 = (env, prog) ∧
        (none : Option (List Nat × NumSet)) = none ∧ handler = none ∧ s.clock ≠ 0 →
      PropertyAt C prog { LoopSemStateFiniteExact.decClock s with locals := env }) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.call none dest argvars handler) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ k, sptMem k (accVarsHOL (width := width) (.call none dest argvars handler) .ln) → sptMem k ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.call none dest argvars handler) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, hNE, hState, hLocals, hRetv, hgd, hWord, hAcc⟩
  have hState' := hState
  obtain ⟨len, hm, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := hState'
  have hcall := (WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C)
    (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [LoopSemStateFiniteExact.evaluate] at hEval
  split at hEval
  · simp only [Prod.mk.injEq] at hEval
    exact absurd hEval.1.symm hNE
  · rename_i argvals hgv
    split at hEval
    · simp only [Prod.mk.injEq] at hEval
      exact absurd hEval.1.symm hNE
    · rename_i env prog hfc
      simp only at hEval
      by_cases hh : handler.isSome = true
      · rw [if_pos hh] at hEval
        simp only [Prod.mk.injEq] at hEval
        exact absurd hEval.1.symm hNE
      rw [if_neg hh] at hEval
      have hhn : handler = none := by cases handler <;> simp_all
      subst hhn
      obtain ⟨hwgv, -⟩ := LoopToWord.localsRelHOLGetVars ctxt s t argvars argvals ⟨hLocals, hgv⟩
      obtain ⟨args1, ss1, ctxt1, l1, hwf, h0, hl1, hacc1⟩ :=
        findCode_rel s.code t.code t.stackSize dest argvals env prog retv hcode hfc
      have hwgv0 : WordSemStateFiniteExact.getVars
          (0 :: argvars.map (LoopToWord.findVarHOL ctxt)) t = some (retv :: argvals) := by
        simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, hRetv, hwgv]
      have hbad : wordSemBadDestArgs dest (0 :: argvars.map (LoopToWord.findVarHOL ctxt)) = false := by
        simp [wordSemBadDestArgs]
      simp only [LoopToWord.compHOL]
      rw [hcall]
      simp only [hwgv0, hbad, Bool.false_eq_true, if_false, wordSemAddRetLoc, hwf]
      by_cases hz : s.clock = 0
      · rw [dif_pos hz] at hEval
        simp only [Prod.mk.injEq] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        refine ⟨WordSemStateFiniteExact.flushState true t, some .timeOut, ?_, ?_, rfl⟩
        · rw [if_pos (by rw [hclock]; exact hz)]
        · simp [WordSemStateFiniteExact.flushState, hffi]
      · rw [dif_neg hz] at hEval
        have hz' : ¬ t.clock = 0 := by rw [hclock]; exact hz
        rw [if_neg hz']
        have ihs := ih argvals (env, prog) env prog ⟨hgv, hfc, rfl, rfl, rfl, hz⟩
        rcases hr : LoopSemStateFiniteExact.evaluate prog
          { LoopSemStateFiniteExact.decClock s with locals := env } with ⟨r', s'⟩
        rw [hr] at hEval
        have hstep : ∀ r : LoopSemStateFiniteExact.LoopResultExact width,
            (∀ k, r ≠ .break k) → (∀ k, r ≠ .continue k) →
            r' = some r → res = some r → s1 = s' →
            ∃ t1 res1, (if wordSemBadFunReturn
                  (WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt1 prog l1).fst
                    (WordSemStateFiniteExact.callEnv args1 ss1
                      (WordSemStateFiniteExact.decClock t))).fst = true then
                (some WordSemResult.error,
                  (WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt1 prog l1).fst
                    (WordSemStateFiniteExact.callEnv args1 ss1
                      (WordSemStateFiniteExact.decClock t))).snd)
              else
                ((WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt1 prog l1).fst
                    (WordSemStateFiniteExact.callEnv args1 ss1
                      (WordSemStateFiniteExact.decClock t))).fst,
                  (WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt1 prog l1).fst
                    (WordSemStateFiniteExact.callEnv args1 ss1
                      (WordSemStateFiniteExact.decClock t))).snd)) = (res1, t1) ∧
              t1.ffi = s1.ffi ∧ resultCase ctxt retv t res s1 res1 t1 := by
          intro r hnb hnc hr' hres hs1
          subst hr' hres hs1
          obtain ⟨t1, res1, he, hf1, hrc⟩ := ihs _ _
            (WordSemStateFiniteExact.callEnv args1 ss1 (WordSemStateFiniteExact.decClock t))
            ctxt1 retv l1 ⟨hr, hNE, ⟨len, hm, hmd, hsmd,
              by simp [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
                LoopSemStateFiniteExact.decClock, hclock], hbe, hffi, hcur, hlen, htop, hglob,
              hcode⟩, hl1, h0, hgd, hWord, hacc1⟩
          rw [he]
          cases r with
          | result v =>
            have hres1 := hrc.2.1
            subst hres1
            exact ⟨t1, _, rfl, hf1, hrc⟩
          | exception v =>
            have hb : wordSemBadFunReturn res1 = false := by
              obtain ⟨_, himp, _⟩ := hrc
              by_cases hE : res1 = some .error
              · rw [hE]; rfl
              · obtain ⟨u1, u2, rfl⟩ := himp hE; rfl
            simp only [hb, Bool.false_eq_true, if_false]
            exact ⟨t1, res1, rfl, hf1, hrc⟩
          | timeOut =>
            have hrc' : res1 = some .timeOut := hrc
            subst hrc'
            exact ⟨t1, _, rfl, hf1, rfl⟩
          | finalFfi f =>
            have hrc' : res1 = some (.finalFfi f) := hrc
            subst hrc'
            exact ⟨t1, _, rfl, hf1, rfl⟩
          | error => exact absurd rfl hNE
          | «break» k => exact absurd rfl (hnb k)
          | «continue» k => exact absurd rfl (hnc k)
        cases r' with
        | none =>
          simp only [Prod.mk.injEq] at hEval
          exact absurd hEval.1.symm hNE
        | some r =>
          cases r with
          | «continue» k =>
            simp only [Prod.mk.injEq] at hEval
            exact absurd hEval.1.symm hNE
          | «break» k =>
            simp only [Prod.mk.injEq] at hEval
            exact absurd hEval.1.symm hNE
          | _ =>
            simp only [Prod.mk.injEq] at hEval
            exact hstep _ (by intro k h; cases h) (by intro k h; cases h) rfl hEval.1.symm
              hEval.2.symm

end Flapjack
