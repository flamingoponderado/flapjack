import Flapjack.HolRef
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call.HandlerTail
import Flapjack.Pancake.Proofs.LoopToWord.TickUnfold
import Flapjack.Pancake.Proofs.LoopToWord.ContextSupport

/-!
# `Loop` case of `loop_to_word`'s `compile_correct`

The exact `loopSem$evaluate_ind` `Loop` case of HOL `compile_correct`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:57-97`, resumed at
`:571-728` with the sub-resumes `Loop_bodyNONE`, `Loop_Exception`,
`Loop_Break` and `Loop_Continue`), bead `flapjack-pxn.18.5.9.23.2`.  The
statement is HOL's conjunct with its three induction-hypothesis premise sets,
as one conjunction as in HOL:
1. the `Continue 0` re-entry;
2. the `NONE` re-entry;
3. the body.

The goal is written out as in `CompileCorrect/Base.lean`.
-/

namespace Flapjack

open LoopToWord.CompileCorrect

namespace LoopToWordCompileCorrectLoopWitnesses

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

end LoopToWordCompileCorrectLoopWitnesses

/-- Genuine `Loop` case of HOL `compile_correct`
    (`loop_to_wordProofScript.sml:57-97`, resumed at `:571-728`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_Loop {width : Nat} [NeZero width] {C F : Type}
    (liveIn : NumSet) (body : HolLoopProg width) (liveOut : NumSet) (s : LoopSemStateFiniteExact width F)
    (ih : (∀ (v4 : Option (LoopSemStateFiniteExact.LoopResultExact width))
        (s' : LoopSemStateFiniteExact width F)
        (v : Option (LoopSemStateFiniteExact.LoopResultExact width))
        (s'' : LoopSemStateFiniteExact width F)
        (v3 : LoopSemStateFiniteExact.LoopResultExact width) (v12 : Nat),
        LoopSemStateFiniteExact.cutRes liveIn (none, s) = (v4, s') ∧ v4 = none ∧
          LoopSemStateFiniteExact.evaluate body s' = (v, s'') ∧ v = some v3 ∧
          v3 = .continue v12 ∧ v12 = 0 →
        PropertyAt C (.loop liveIn body liveOut) s'') ∧
      (∀ (v4 : Option (LoopSemStateFiniteExact.LoopResultExact width))
        (s' : LoopSemStateFiniteExact width F)
        (v : Option (LoopSemStateFiniteExact.LoopResultExact width))
        (s'' : LoopSemStateFiniteExact width F),
        LoopSemStateFiniteExact.cutRes liveIn (none, s) = (v4, s') ∧ v4 = none ∧
          LoopSemStateFiniteExact.evaluate body s' = (v, s'') ∧ v = none →
        PropertyAt C (.loop liveIn body liveOut) s'') ∧
      (∀ (v4 : Option (LoopSemStateFiniteExact.LoopResultExact width))
        (s' : LoopSemStateFiniteExact width F),
        LoopSemStateFiniteExact.cutRes liveIn (none, s) = (v4, s') ∧ v4 = none →
        PropertyAt C body s')) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.loop liveIn body liveOut) s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ k, sptMem k (accVarsHOL (width := width) (.loop liveIn body liveOut) .ln) → sptMem k ctxt) →
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.loop liveIn body liveOut) l).1 t = (res1, t1) ∧
          t1.ffi = s1.ffi ∧
          resultCase ctxt retv t res s1 res1 t1 := by
  rintro res s1 t ctxt retv l ⟨hEval, hNE, hState, hLocals, hRetv, hgd, hWord, hAcc⟩
  obtain ⟨ihC, ihN, ihB⟩ := ih
  have hState' := hState
  obtain ⟨len, hm, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := hState'
  have hseq := (WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C)
    (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
  have htick := (WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C)
    (F := F)).2.2.2.2.2.2.2.2.2.2.1
  have hloopW := (WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C)
    (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbodyctx : ∀ k, sptMem k (accVarsHOL body .ln) → sptMem k ctxt := fun k hk =>
    hAcc k (by simpa [accVarsHOL] using hk)
  rw [LoopSemStateFiniteExact.evaluate] at hEval
  split at hEval
  · rename_i s1c hcr
    have hc2 : ∃ cs, LoopSemStateFiniteExact.cutState liveIn s = some cs ∧ s.clock ≠ 0 ∧
        s1c = LoopSemStateFiniteExact.decClock cs := by
      unfold LoopSemStateFiniteExact.cutRes at hcr
      simp only at hcr
      cases hcs : LoopSemStateFiniteExact.cutState liveIn s with
      | none => simp [hcs] at hcr
      | some cs =>
        simp only [hcs] at hcr
        have hcl : cs.clock = s.clock := by
          unfold LoopSemStateFiniteExact.cutState at hcs
          split at hcs
          · cases hcs; rfl
          · cases hcs
        by_cases hz : s.clock = 0
        · simp [hcl, hz] at hcr
        · simp only [hcl, hz, if_false, Prod.mk.injEq, true_and] at hcr
          exact ⟨_, rfl, hz, hcr.symm⟩
    obtain ⟨cs, hcs, hz, rfl⟩ := hc2
    have hsub : LoopSemStateFiniteExact.sptSubsetLive liveIn s.locals ∧
        cs = { s with locals := sptInter s.locals liveIn } := by
      unfold LoopSemStateFiniteExact.cutState at hcs
      split at hcs
      · exact ⟨‹_›, (Option.some.inj hcs).symm⟩
      · cases hcs
    obtain ⟨hsub, rfl⟩ := hsub
    obtain ⟨env1, hce, hlr⟩ := LoopToWord.wordSemCutEnvMkNewCutsetHOL ctxt liveIn s.locals
      t.locals retv ⟨hLocals, hsub, hRetv⟩
    have h0e := (LoopToWord.wordSemCutEnvMkNewCutsetIMPHOL ctxt liveIn t.locals env1 hce).trans
      hRetv
    have hz' : t.clock ≠ 0 := by rw [hclock]; exact hz
    simp only [LoopToWord.compHOL]
    rw [WordSemStateFiniteExact.evaluate_tick_loop_tick_unfold t _ _ _ hz', hloopW]
    simp only [WordSemStateFiniteExact.cutState, hce]
    have ihb := ihB none _ ⟨hcr, rfl⟩
    have hIHb : ∀ r st, LoopSemStateFiniteExact.evaluate body
          (LoopSemStateFiniteExact.decClock { s with locals := sptInter s.locals liveIn }) =
          (r, st) → r ≠ some .error →
        ∃ t1 res1, WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt body l).fst
            { t with clock := t.clock - 1, locals := env1 } = (res1, t1) ∧
          t1.ffi = st.ffi ∧
          resultCase ctxt retv { t with clock := t.clock - 1, locals := env1 } r st res1 t1 := by
      intro r st h hne
      exact ihb r st _ ctxt retv l ⟨h, hne,
        ⟨len, hm, hmd, hsmd, by simp [LoopSemStateFiniteExact.decClock, hclock], hbe, hffi, hcur,
          hlen, htop, hglob, hcode⟩, hlr, h0e, hgd, hWord, hbodyctx⟩
    split at hEval
    · -- body NONE: re-enter the loop
      rename_i sb heq
      rw [LoopSemStateFiniteExact.fix_clock_evaluate] at heq
      obtain ⟨t1, res1, he, hf1, hst, hr1, h0t, hlt, hstk, hhd⟩ := hIHb none sb heq (by simp)
      subst hr1
      rw [he]
      obtain ⟨t1', res1', he', hf', hrc'⟩ := ihN none _ none sb ⟨hcr, rfl, heq, rfl⟩
        res s1 t1 ctxt retv l ⟨hEval, hNE, hst, hlt, h0t, hgd, hWord, hAcc⟩
      refine ⟨t1', res1', ?_, hf', resultCase_congr ctxt retv t1 t res s1 res1' t1'
        (hstk.trans rfl) (hhd.trans rfl) hrc'⟩
      simp only [LoopToWord.compHOL] at he'
      simp only [wordSemContLoop, if_true]
      by_cases hz1 : t1.clock = 0
      · rw [hseq, htick, if_pos hz1] at he'
        simp only [hz1, if_true]
        exact he'
      · rw [WordSemStateFiniteExact.evaluate_tick_loop_tick_unfold t1 _ _ _ hz1] at he'
        simp only [hz1, if_false, wordSemSTOP]
        exact he'
    · -- body Continue 0: re-enter the loop
      rename_i sb heq
      rw [LoopSemStateFiniteExact.fix_clock_evaluate] at heq
      obtain ⟨t1, res1, he, hf1, hst, hr1, h0t, hlt, hstk, hhd⟩ :=
        hIHb (some (.continue 0)) sb heq (by simp)
      subst hr1
      rw [he]
      obtain ⟨t1', res1', he', hf', hrc'⟩ := ihC none _ (some (.continue 0)) sb (.continue 0) 0
        ⟨hcr, rfl, heq, rfl, rfl, rfl⟩
        res s1 t1 ctxt retv l ⟨hEval, hNE, hst, hlt, h0t, hgd, hWord, hAcc⟩
      refine ⟨t1', res1', ?_, hf', resultCase_congr ctxt retv t1 t res s1 res1' t1'
        (hstk.trans rfl) (hhd.trans rfl) hrc'⟩
      simp only [LoopToWord.compHOL] at he'
      simp only [wordSemContLoop, decide_true, if_true]
      by_cases hz1 : t1.clock = 0
      · rw [hseq, htick, if_pos hz1] at he'
        simp only [hz1, if_true]
        exact he'
      · rw [WordSemStateFiniteExact.evaluate_tick_loop_tick_unfold t1 _ _ _ hz1] at he'
        simp only [hz1, if_false, wordSemSTOP]
        exact he'
    · -- body Break 0: leave the loop through the exit cut
      rename_i sb heq
      rw [LoopSemStateFiniteExact.fix_clock_evaluate] at heq
      obtain ⟨t1, res1, he, hf1, hst, hr1, h0t, hlt, hstk, hhd⟩ :=
        hIHb (some (.break 0)) sb heq (by simp)
      subst hr1
      rw [he]
      obtain ⟨len2, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩ := hst
      unfold LoopSemStateFiniteExact.cutRes at hEval
      simp only at hEval
      cases hcs2 : LoopSemStateFiniteExact.cutState liveOut sb with
      | none =>
        rw [hcs2] at hEval
        simp only [Prod.mk.injEq] at hEval
        exact absurd hEval.1.symm hNE
      | some c =>
        have hsub2 : LoopSemStateFiniteExact.sptSubsetLive liveOut sb.locals ∧
            c = { sb with locals := sptInter sb.locals liveOut } := by
          unfold LoopSemStateFiniteExact.cutState at hcs2
          split at hcs2
          · exact ⟨‹_›, (Option.some.inj hcs2).symm⟩
          · cases hcs2
        obtain ⟨hsub2, rfl⟩ := hsub2
        simp only [hcs2] at hEval
        obtain ⟨env2, hce2, hlr2⟩ := LoopToWord.wordSemCutEnvMkNewCutsetHOL ctxt liveOut
          sb.locals t1.locals retv ⟨hlt, hsub2, h0t⟩
        have h0e2 := (LoopToWord.wordSemCutEnvMkNewCutsetIMPHOL ctxt liveOut t1.locals env2
          hce2).trans h0t
        simp only [wordSemContLoop, Bool.false_eq_true, if_false]
        simp only [hce2]
        by_cases hz2 : sb.clock = 0
        · simp only [hz2, if_true, Prod.mk.injEq] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          simp only [f4, hz2, if_true]
          exact ⟨_, _, rfl, by simp [WordSemStateFiniteExact.flushState, f6], rfl⟩
        · simp only [hz2, if_false, Prod.mk.injEq] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          simp only [f4, hz2, if_false]
          refine ⟨_, _, rfl, f6, ⟨len2, f1, f2, f3, ?_, f5, f6, f7, f8, f9, f10, f11⟩, rfl,
            h0e2, hlr2, hstk, hhd⟩
          simp [LoopSemStateFiniteExact.decClock]
    · -- other body results leave through exit_loop
      rename_i r sb hnN hnC hnB heq
      rw [LoopSemStateFiniteExact.fix_clock_evaluate] at heq
      simp only [Prod.mk.injEq] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      have hrne : r ≠ some .error := by
        intro h
        subst h
        exact hNE rfl
      obtain ⟨t1, res1, he, hf1, hrc⟩ := hIHb r sb heq hrne
      rw [he]
      cases r with
      | none => exact absurd rfl hnN
      | some x =>
        cases x with
        | «continue» n =>
          have hn0 : n ≠ 0 := fun h => hnC (by rw [h])
          obtain ⟨hst, hr1, h0t, hlt, hstk, hhd⟩ := hrc
          subst hr1
          refine ⟨t1, some (.continue (n - 1)), ?_, hf1, hst, rfl, h0t, hlt, hstk, hhd⟩
          simp [wordSemContLoop, wordSemExitLoop, hn0]
        | «break» n =>
          have hn0 : n ≠ 0 := fun h => hnB (by rw [h])
          obtain ⟨hst, hr1, h0t, hlt, hstk, hhd⟩ := hrc
          subst hr1
          refine ⟨t1, some (.break (n - 1)), ?_, hf1, hst, rfl, h0t, hlt, hstk, hhd⟩
          simp [wordSemContLoop, wordSemExitLoop, hn0]
        | result v =>
          have hrc' := resultCase_congr ctxt retv _ t (some (.result v)) sb res1 t1 rfl rfl hrc
          have hr1 := hrc.2.1
          subst hr1
          exact ⟨t1, _, by simp [wordSemContLoop, wordSemExitLoop], hf1, hrc'⟩
        | exception v =>
          have hrc' := resultCase_congr ctxt retv _ t (some (.exception v)) sb res1 t1 rfl rfl hrc
          by_cases hE : res1 = some .error
          · subst hE
            exact ⟨t1, _, by simp [wordSemContLoop, wordSemExitLoop], hf1, hrc'⟩
          · obtain ⟨u1, u2, rfl⟩ := hrc.2.1 hE
            exact ⟨t1, _, by simp [wordSemContLoop, wordSemExitLoop], hf1, hrc'⟩
        | timeOut =>
          have hr1 : res1 = some .timeOut := hrc
          subst hr1
          exact ⟨t1, _, by simp [wordSemContLoop, wordSemExitLoop], hf1, rfl⟩
        | finalFfi f =>
          have hr1 : res1 = some (.finalFfi f) := hrc
          subst hr1
          exact ⟨t1, _, by simp [wordSemContLoop, wordSemExitLoop], hf1, rfl⟩
        | error => exact absurd rfl hrne
  · rename_i hnone
    unfold LoopSemStateFiniteExact.cutRes at hEval
    simp only at hEval
    cases hcs : LoopSemStateFiniteExact.cutState liveIn s with
    | none =>
      rw [hcs] at hEval
      simp only [Prod.mk.injEq] at hEval
      exact absurd hEval.1.symm hNE
    | some cs =>
      have hcs' := hcs
      unfold LoopSemStateFiniteExact.cutState at hcs'
      split at hcs'
      · cases hcs'
        simp only [hcs] at hEval
        by_cases hz : s.clock = 0
        · simp only [hz, if_true, Prod.mk.injEq] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          simp only [LoopToWord.compHOL]
          rw [hseq, htick, if_pos (by rw [hclock]; exact hz)]
          exact ⟨_, _, rfl, by simp [WordSemStateFiniteExact.flushState, hffi], rfl⟩
        · exfalso
          refine hnone (LoopSemStateFiniteExact.decClock
            { s with locals := sptInter s.locals liveIn }) ?_
          unfold LoopSemStateFiniteExact.cutRes
          simp [hcs, hz]
      · cases hcs'

end Flapjack
