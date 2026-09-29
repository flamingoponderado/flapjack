import Flapjack.HolRef
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Property
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.Semantics.CrepProps.EvaluateAddClock
import Flapjack.Pancake.Semantics.LoopProps.EvaluateClockExact
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqExact

/-!
# The `Seq` case of `crep_to_loop`'s `ncompile_correct`

This is the constructor case resumed at
`cakeml/pancake/proofs/crep_to_loopProofScript.sml:1679-1703`. Its only
induction hypotheses are the exact theorem property for the two subprograms.
-/

namespace Flapjack

open LoopSemStateFiniteExact
open Pancake.CrepToLoop.Proofs.NCompileCorrect

namespace NCompileCorrectSeqFmapWitnesses

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
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : LoopSemStateBroad width σ) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width σ,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

end NCompileCorrectSeqFmapWitnesses

/-- Genuine `Seq c1 c2` induction case of HOL `ncompile_correct`
    (`crep_to_loopProofScript.sml:110-154`, resumed at `:1679-1703`). As in
    `crepSemTheory.evaluate_ind`, the first IH is at the fixed source state;
    the second IH is available only after evaluating `c1` to `none` and its
    resulting state. The conclusion retains the existential target result,
    final state, and clock extension. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ncompile_correct"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_ncompile_correct_seq {width : Nat} [NeZero width] {σ : Type}
    (context : CrepToLoopContextExact) (live : NumSet)
    (first second : CrepProgHOL width)
    (source : CrepSemHOLState width σ)
    (ihSecond : ∀ firstResult firstState,
      (firstResult, firstState) = evalCrepSemHOLProgExact source first →
      firstResult = none → PropertyAt second firstState)
    (ihFirst : PropertyAt first source)
    (target : LoopSemStateFiniteExact width σ)
    (result : Option (CrepResultHOLExact width))
    (sourceFinal : CrepSemHOLState width σ)
    (hEval : evalCrepSemHOLProgExact source (.seq first second) = (result, sourceFinal))
    (hNotError : result ≠ some .error)
    (hState : crepToLoopStateRelExact source target)
    (hMem : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (hGlobals : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (hCode : crepToLoopCodeRelExact context source.code target.code)
    (hLocals : crepToLoopLocalsRelExact context live source.locals target.locals) :
    ∃ (extra : Nat) (targetResult : Option (LoopResultExact width))
      (targetFinal : LoopSemStateFiniteExact width σ),
      LoopSemStateFiniteExact.evaluate (compileHOLExact context live (.seq first second))
          { target with clock := target.clock + extra } = (targetResult, targetFinal) ∧
      crepToLoopStateRelExact sourceFinal targetFinal ∧
      crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
      crepToLoopCodeRelExact context sourceFinal.code targetFinal.code ∧
      targetResult = resultToLoop result ∧
      localsResultRel context live result sourceFinal targetFinal := by
  rw [evalCrepSemHOLProgExact_seq_holShape] at hEval
  cases hFirst : evalCrepSemHOLProgExact source first with
  | mk firstResult firstState =>
    rw [hFirst] at hEval
    cases firstResult with
    | none =>
      simp only at hEval
      obtain ⟨firstExtra, firstTargetResult, firstTargetFinal,
        hFirstRun, hFirstState, hFirstMem, hFirstGlobals, hFirstCode,
        hFirstResult, hFirstLocals⟩ :=
        ihFirst none firstState target context live hFirst (by simp)
          hState hMem hGlobals hCode hLocals
      have hFirstTargetNone : firstTargetResult = none := by
        simpa [resultToLoop] using hFirstResult
      subst firstTargetResult
      obtain ⟨secondExtra, finalTargetResult, finalTarget,
        hSecondRun, hSecondState, hSecondMem, hSecondGlobals, hSecondCode,
        hSecondResult, hSecondLocals⟩ :=
        (ihSecond none firstState hFirst.symm rfl)
          result sourceFinal firstTargetFinal context live hEval hNotError
          hFirstState hFirstMem hFirstGlobals hFirstCode hFirstLocals
      have hFirstRunLift :
          LoopSemStateFiniteExact.evaluate (compileHOLExact context live first)
            { target with clock := target.clock + (firstExtra + secondExtra) } =
              (none, { firstTargetFinal with
                clock := firstTargetFinal.clock + secondExtra }) := by
        have hLift := LoopSemStateFiniteExact.evaluate_add_clock_eq
          (compileHOLExact context live first)
          { target with clock := target.clock + firstExtra } none firstTargetFinal
          secondExtra hFirstRun (by simp)
        simpa [Nat.add_assoc] using hLift
      refine ⟨firstExtra + secondExtra, finalTargetResult, finalTarget, ?_,
        hSecondState, hSecondMem, hSecondGlobals, hSecondCode,
        hSecondResult, hSecondLocals⟩
      rw [compileHOLExact, LoopSemStateFiniteExact.evaluate_seq, hFirstRunLift]
      exact hSecondRun
    | some firstValue =>
      have hFirstPair : (some firstValue, firstState) = (result, sourceFinal) := by
        simpa using hEval
      rcases Prod.mk.inj hFirstPair with ⟨hResultEq, hFinalEq⟩
      have hFirstNotError : some firstValue ≠ some .error := by
        intro h
        apply hNotError
        rw [← hResultEq]
        exact h
      obtain ⟨extra, targetResult, targetFinal,
        hRun, hFinalState, hFinalMem, hFinalGlobals, hFinalCode,
        hResultMap, hFinalLocals⟩ :=
        ihFirst (some firstValue) firstState target context live hFirst hFirstNotError
          hState hMem hGlobals hCode hLocals
      have hFinalState' : crepToLoopStateRelExact sourceFinal targetFinal :=
        hFinalEq ▸ hFinalState
      have hFinalMem' : crepToLoopMemRelHOLExact sourceFinal.memory
          targetFinal.memory sourceFinal.memaddrs := hFinalEq ▸ hFinalMem
      have hFinalGlobals' : crepToLoopGlobalsRelHOLExact sourceFinal.globals
          targetFinal.globals := hFinalEq ▸ hFinalGlobals
      have hFinalCode' : crepToLoopCodeRelExact context sourceFinal.code
          targetFinal.code := hFinalEq ▸ hFinalCode
      have hFinalLocals' : localsResultRel context live result sourceFinal targetFinal := by
        simpa [← hResultEq] using (hFinalEq ▸ hFinalLocals)
      have hTargetSome : targetResult ≠ none := by
        rw [hResultMap]
        cases firstValue <;> simp [resultToLoop]
      have hResultMap' : targetResult = resultToLoop result := by
        simpa [← hResultEq] using hResultMap
      refine ⟨extra, targetResult, targetFinal, ?_, hFinalState', hFinalMem',
        hFinalGlobals', hFinalCode', hResultMap', hFinalLocals'⟩
      rw [compileHOLExact, LoopSemStateFiniteExact.evaluate_seq, hRun]
      cases targetResult with
      | none => exact False.elim (hTargetSome rfl)
      | some value => rfl

end Flapjack
