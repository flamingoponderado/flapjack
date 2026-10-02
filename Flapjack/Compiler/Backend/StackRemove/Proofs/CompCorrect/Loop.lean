import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Control
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateClock
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock
import Flapjack.Compiler.Backend.StackProps.ClockSupport
namespace Flapjack.Compiler.Backend.StackRemove.CompCorrect.Loop
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemControl StackSemStateOps
/-- Canonical owning-state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Source-local Loop proof infrastructure: the reviewed unconditional clock
identity recovers the original rebound evaluator equation. No independent
HOL declaration is claimed. -/
theorem evaluateLoopUnclamped {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (source : StackSemStateFiniteExact width C F) :
    evaluate (.loop body, source) =
      match evaluate (body, source) with
      | (result, middle) =>
          if StackSemControl.contLoop result then
            if middle.clock = 0 then (some .timeOut, emptyEnv middle)
            else evaluate (.loop body, decClock middle)
          else (StackSemControl.exitLoop result, middle) := by
  rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate]

/-- Actual exit branch equation; source-local infrastructure with no separate HOL original. -/
theorem evaluateLoopExit {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (source middle : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : evaluate (body, source) = (result, middle))
    (exits : StackSemControl.contLoop result = false) :
    evaluate (.loop body, source) = (StackSemControl.exitLoop result, middle) := by
  rw [evaluateLoopUnclamped, execution]
  simp only [exits, Bool.false_eq_true, if_false]

/-- Actual zero-clock branch equation; source-local infrastructure, not a separate HOL port. -/
theorem evaluateLoopTimeOut {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (source middle : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : evaluate (body, source) = (result, middle))
    (continues : StackSemControl.contLoop result = true) (zero : middle.clock = 0) :
    evaluate (.loop body, source) = (some .timeOut, emptyEnv middle) := by
  rw [evaluateLoopUnclamped, execution]
  simp only [continues, if_true, zero]

/-- Actual reentry equation; source-local infrastructure retaining both real guards. -/
theorem evaluateLoopReentry {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (source middle : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : evaluate (body, source) = (result, middle))
    (continues : StackSemControl.contLoop result = true) (nonzero : middle.clock ≠ 0) :
    evaluate (.loop body, source) = evaluate (.loop body, decClock middle) := by
  rw [evaluateLoopUnclamped, execution]
  simp only [continues, if_true, nonzero, if_false]

/-- The original non-Error whole-run premise excludes a body Error. This is
source-local case factoring, with no independent HOL declaration. -/
theorem loopBodyNotError {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (source middle post : StackSemStateFiniteExact width C F)
    (bodyResult result : Option (StackSemResult width))
    (bodyRun : evaluate (body, source) = (bodyResult, middle))
    (loopRun : evaluate (.loop body, source) = (result, post))
    (notError : result ≠ some .error) : bodyResult ≠ some .error := by
  intro eq
  subst bodyResult
  have exits : StackSemControl.contLoop (some (.error : StackSemResult width)) = false := rfl
  rw [evaluateLoopExit body source middle (some .error) bodyRun exits] at loopRun
  exact notError (Prod.mk.inj loopRun).1.symm

/-- Genuine full original Loop induction case, with only the original body and
actual body-run/continuation/nonzero-clock guarded reentry IHs augmenting the
four source premises. The native target run and added clock are derived. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectLoop {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (bodyIH : ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
      (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (body, source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k source t ∧ StackProps.regBound body k →
      ∃ clock postTarget,
        evaluate (comp j off k body, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (reentryIH : ∀ (bodyResult : Option (StackSemResult width)) (middle : StackSemStateFiniteExact width C F),
      evaluate (body, source) = (bodyResult, middle) →
      StackSemControl.contLoop bodyResult = true → middle.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (.loop body, decClock middle) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (decClock middle) t ∧ StackProps.regBound (.loop body) k →
      ∃ clock postTarget,
        evaluate (comp j off k (.loop body), {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.loop body, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.loop body) pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer (.loop body),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  rcases bodyRun : evaluate (body, source) with ⟨bodyResult, middle⟩
  have bodyNotError := loopBodyNotError body source middle postSource bodyResult result bodyRun sourceRun notError
  obtain ⟨firstClock, middleTarget, firstTargetRun, bodyPost⟩ :=
    bodyIH bodyResult middle target pointer bounds jump
      ⟨bodyRun, bodyNotError, relation, by simpa only [StackProps.regBound] using lower⟩
  by_cases continues : StackSemControl.contLoop bodyResult = true
  · have middleRelation : stateRelHOL jump bounds pointer middle middleTarget := by
      rcases StackProps.contLoopImp bodyResult continues with same | same
      · rw [same] at bodyPost; exact bodyPost
      · rw [same] at bodyPost; exact bodyPost
    have middleClocks : middleTarget.clock = middle.clock := middleRelation.2.2.2.2.2.2.2.2.1
    by_cases zero : middle.clock = 0
    · rw [evaluateLoopTimeOut body source middle bodyResult bodyRun continues zero] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
      subst result
      subst postSource
      refine ⟨firstClock, emptyEnv middleTarget, ?_, ?_⟩
      · simpa only [comp] using
          evaluateLoopTimeOut (comp jump bounds pointer body)
            {target with clock := firstClock + target.clock} middleTarget bodyResult
            firstTargetRun continues (middleClocks.trans zero)
      · change middleTarget.ffi = middle.ffi
        exact middleRelation.2.2.2.2.2.2.2.2.2.1
    · rw [evaluateLoopReentry body source middle bodyResult bodyRun continues zero] at sourceRun
      have decRelation := RelationLaws.stateRelDecClock jump bounds pointer middle middleTarget middleRelation
      obtain ⟨secondClock, postTarget, secondTargetRun, postRelation⟩ :=
        reentryIH bodyResult middle bodyRun continues zero result postSource
          (decClock middleTarget) pointer bounds jump ⟨sourceRun, notError, decRelation, lower⟩
      have notTimeout : bodyResult ≠ some .timeOut := by
        rcases StackProps.contLoopImp bodyResult continues with same | same <;> simp [same]
      have extraRun := StackProps.evaluateAddClock secondClock
        (comp jump bounds pointer body) {target with clock := firstClock + target.clock}
        bodyResult middleTarget ⟨firstTargetRun, notTimeout⟩
      have combinedRun :
          evaluate (comp jump bounds pointer body,
            {target with clock := (firstClock + secondClock) + target.clock}) =
            (bodyResult, {middleTarget with clock := secondClock + middleTarget.clock}) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using extraRun
      have targetNonzero : middleTarget.clock ≠ 0 := by rw [middleClocks]; exact zero
      have boostedNonzero : ({middleTarget with clock := secondClock + middleTarget.clock}).clock ≠ 0 := by
        change secondClock + middleTarget.clock ≠ 0
        omega
      have decState : decClock {middleTarget with clock := secondClock + middleTarget.clock} =
          {decClock middleTarget with clock := secondClock + (decClock middleTarget).clock} := by
        change {middleTarget with clock := secondClock + middleTarget.clock - 1} =
          {middleTarget with clock := secondClock + (middleTarget.clock - 1)}
        have arithmetic : secondClock + middleTarget.clock - 1 = secondClock + (middleTarget.clock - 1) := by omega
        rw [arithmetic]
      refine ⟨firstClock + secondClock, postTarget, ?_, ?_⟩
      · rw [comp, evaluateLoopReentry _ _ _ _ combinedRun continues boostedNonzero, decState]
        simpa only [comp] using secondTargetRun
      · cases result with
        | none => exact postRelation
        | some value => cases value <;> exact postRelation
  · have exits : StackSemControl.contLoop bodyResult = false := by
      cases equality : StackSemControl.contLoop bodyResult <;> simp_all
    rw [evaluateLoopExit body source middle bodyResult bodyRun exits] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨firstClock, middleTarget, ?_, ?_⟩
    · simpa only [comp] using
        evaluateLoopExit (comp jump bounds pointer body)
          {target with clock := firstClock + target.clock} middleTarget bodyResult firstTargetRun exits
    · cases bodyResult with
      | none => simp [StackSemControl.contLoop] at continues
      | some value =>
        cases value with
        | «break» label => cases label <;> exact bodyPost
        | _ => exact bodyPost
end Flapjack.Compiler.Backend.StackRemove.CompCorrect.Loop
