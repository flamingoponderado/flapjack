import Flapjack.HolRef
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Property
import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateClock
import Flapjack.Pancake.Proofs.LoopToWord.AccVarsAcc

/-!
# `Seq` case of `loop_to_word`'s `compile_correct`

This is the exact `Seq` conjunct of HOL `loopSem$evaluate_ind` specialised to
`compile_correct` (`cakeml/pancake/proofs/loop_to_wordProofScript.sml:57-97`,
resumed at the `Seq` case). The first induction hypothesis is unrestricted
apart from the shared non-Error premise. The second is available only when the
first exact source evaluation returns `NONE`; its `PropertyAt` retains all of
HOL's original premises and existential target-run conclusion.

The proof follows HOL `evaluate_def`: it fixes the first child clock, runs the
second child only on `NONE`, and otherwise propagates the first result. It
projects the exact `acc_vars_acc'` domain equation to each child, and uses the
compiler's returned label pair when instantiating the second hypothesis. The
direct HOL Seq induction conjunct is recorded in
`scripts/hol-probes/loop_to_word_compile_correct_cases_probe.out`; the focused
compiler label-threading regression is in
`Flapjack/Test/LoopToWordCompileCorrectSeq.lean`.
-/

namespace Flapjack

open LoopToWord.CompileCorrect

namespace LoopToWordCompileCorrectSeqWitnesses

/-- Same-module roundtrip for the Seq case's loopSem finite-map fields. -/
theorem holFmapAsFiniteSupportRelationWitness_LoopSemStateFiniteExact
    {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Same-module roundtrip for the Seq case's wordSem finite-map fields. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end LoopToWordCompileCorrectSeqWitnesses

/-- Genuine Seq induction case of HOL `loop_to_wordProof$compile_correct`.
    The first hypothesis is conditional on the first source command returning
    `NONE`; the second is the unrestricted first-command case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_Seq {width : Nat} [NeZero width] {C F : Type}
    (c1 c2 : HolLoopProg width) (s : LoopSemStateFiniteExact width F) :
    ((∀ res s1, (res, s1) = LoopSemStateFiniteExact.evaluate c1 s ∧ res = none →
        PropertyAt C c2 s1) ∧ PropertyAt C c1 s) →
      PropertyAt C (.seq c1 c2) s := by
  rintro ⟨hSecond, hFirst⟩ res sFinal t ctxt retv l
      ⟨hSourceSeq, hNonError, hState, hLocals, hRetv, hDim, hWord, hAcc⟩
  have hAccFirst : ∀ k, sptMem k (accVarsHOL c1 .ln) → sptMem k ctxt := by
    intro k hk
    have hSplit : sptMem k (accVarsHOL c1 (accVarsHOL c2 .ln)) ↔
        sptMem k (accVarsHOL c1 .ln) ∨ sptMem k (accVarsHOL c2 .ln) := by
      change sptDomain (accVarsHOL c1 (accVarsHOL c2 .ln)) k ↔
        sptDomain (accVarsHOL c1 .ln) k ∨ sptDomain (accVarsHOL c2 .ln) k
      rw [accVarsAccHOL c1 (accVarsHOL c2 .ln)]
    exact hAcc k (by simpa only [accVarsHOL] using hSplit.mpr (Or.inl hk))
  have hAccSecond : ∀ k, sptMem k (accVarsHOL c2 .ln) → sptMem k ctxt := by
    intro k hk
    have hSplit : sptMem k (accVarsHOL c1 (accVarsHOL c2 .ln)) ↔
        sptMem k (accVarsHOL c1 .ln) ∨ sptMem k (accVarsHOL c2 .ln) := by
      change sptDomain (accVarsHOL c1 (accVarsHOL c2 .ln)) k ↔
        sptDomain (accVarsHOL c1 .ln) k ∨ sptDomain (accVarsHOL c2 .ln) k
      rw [accVarsAccHOL c1 (accVarsHOL c2 .ln)]
    exact hAcc k (by simpa only [accVarsHOL] using hSplit.mpr (Or.inr hk))
  have hPropagate (firstResult : LoopSemStateFiniteExact.LoopResultExact width)
      (hFirstNe : some firstResult ≠ some .error)
      (hFirstEval : LoopSemStateFiniteExact.evaluate c1 s = (some firstResult, sFinal)) :
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.seq c1 c2) l).1 t =
          (res1, t1) ∧ t1.ffi = sFinal.ffi ∧
            resultCase ctxt retv t (some firstResult) sFinal res1 t1 := by
    have hFirstCase := hFirst (some firstResult) sFinal t ctxt retv l
      ⟨hFirstEval, hFirstNe, hState, hLocals, hRetv, hDim, hWord, hAccFirst⟩
    rcases hFirstCase with ⟨t1, res1, hTargetFirst, hFfiFirst, hResultFirst⟩
    have hTargetNe : res1 ≠ none := by
      intro hnone
      cases firstResult <;> simp_all [resultCase]
    refine ⟨t1, res1, ?_, hFfiFirst, hResultFirst⟩
    simp only [LoopToWord.compHOL]
    change WordSemStateFiniteExact.evaluate
      (.seq (LoopToWord.compHOL ctxt c1 l).1
        (LoopToWord.compHOL ctxt c2 (LoopToWord.compHOL ctxt c1 l).2).1) t =
        (res1, t1)
    rw [WordSemStateFiniteExact.evaluate]
    rw [WordSemStateFiniteExact.fix_clock_evaluate t (LoopToWord.compHOL ctxt c1 l).1]
    simp [hTargetFirst]
  have hSourceSeq' := hSourceSeq
  simp only [LoopSemStateFiniteExact.evaluate] at hSourceSeq'
  rw [LoopSemStateFiniteExact.fix_clock_evaluate c1 s] at hSourceSeq'
  cases hFirstEval : LoopSemStateFiniteExact.evaluate c1 s with
  | mk firstResult firstState =>
    rw [hFirstEval] at hSourceSeq'
    cases firstResult with
    | none =>
      have hSourceSecond :
          LoopSemStateFiniteExact.evaluate c2 firstState = (res, sFinal) := hSourceSeq'
      have hFirstCase := hFirst none firstState t ctxt retv l
        ⟨hFirstEval, by simp, hState, hLocals, hRetv, hDim, hWord, hAccFirst⟩
      rcases hFirstCase with ⟨t1, res1, hTargetFirst, hFirstFfi, hFirstResultCase⟩
      rcases hFirstResultCase with ⟨hState1, hNone, hRetv1, hLocals1, hStack1, hHandler1⟩
      subst res1
      have hSecondCase := hSecond none firstState ⟨hFirstEval.symm, rfl⟩
      let l2 := (LoopToWord.compHOL ctxt c1 l).2
      have hTargetSecond := hSecondCase res sFinal t1 ctxt retv l2
        ⟨hSourceSecond, hNonError, hState1, hLocals1, hRetv1, hDim, hWord, hAccSecond⟩
      rcases hTargetSecond with ⟨t2, res2, hEvalSecond, hFfiSecond, hResultSecond⟩
      have hResult : resultCase ctxt retv t res sFinal res2 t2 := by
        simpa [resultCase, hStack1, hHandler1] using hResultSecond
      refine ⟨t2, res2, ?_, hFfiSecond, hResult⟩
      simp only [LoopToWord.compHOL]
      change WordSemStateFiniteExact.evaluate
        (.seq (LoopToWord.compHOL ctxt c1 l).1
          (LoopToWord.compHOL ctxt c2 (LoopToWord.compHOL ctxt c1 l).2).1) t =
          (res2, t2)
      rw [WordSemStateFiniteExact.evaluate]
      rw [WordSemStateFiniteExact.fix_clock_evaluate t (LoopToWord.compHOL ctxt c1 l).1]
      simp [hTargetFirst, hEvalSecond, l2]
    | some result =>
      have hSourceFinal : res = some result ∧ sFinal = firstState := by
        simpa [hFirstEval, Option.some.injEq] using hSourceSeq'.symm
      rcases hSourceFinal with ⟨rfl, rfl⟩
      have hFirstNe : some result ≠ some LoopSemStateFiniteExact.LoopResultExact.error := by
        intro heq
        apply hNonError
        simpa using heq
      exact hPropagate result hFirstNe hFirstEval

end Flapjack
