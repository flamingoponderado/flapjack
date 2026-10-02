import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.If
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateClock

namespace Flapjack.Compiler.Backend.StackRawCall.LoopCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl

/-- Genuine canonical codec for the actual imported full evaluator state.
Flapjack representation infrastructure with no separate HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-! Flapjack infrastructure for the genuine recursive rawcall Loop case.
These laws derive whole-state transport from the literal source relation;
they do not assume a target evaluation or postrelation. -/

theorem stateRel_clock {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) : target.clock = source.clock := by
  obtain ⟨code, _, equality, _⟩ := relation
  subst target
  rfl

theorem stateRel_setClock {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (clock : Nat) :
    stateRel info { source with clock := clock } { target with clock := clock } := by
  obtain ⟨code, domain, equality, frames, entries⟩ := relation
  subst target
  exact ⟨code, domain, rfl, frames, entries⟩

theorem stateRel_decClock {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) :
    stateRel info (decClock source) (decClock target) := by
  have clockEq := stateRel_clock info source target relation
  simpa only [decClock, clockEq] using
    stateRel_setClock info source target relation (source.clock - 1)

theorem stateRel_emptyEnv {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) :
    stateRel info (emptyEnv source) (emptyEnv target) := by
  obtain ⟨code, domain, equality, frames, entries⟩ := relation
  subst target
  exact ⟨code, domain, rfl, frames, entries⟩

/-- The actual Loop dispatch after the already proved unconditional clock
clamp identity. No body or recursive target execution is assumed. -/
theorem evaluateLoopUnclamped {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (source : StackSemStateFiniteExact width C F) :
    StackSemEvaluate.evaluate (.loop body, source) =
      match StackSemEvaluate.evaluate (body, source) with
      | (result, post) =>
        if contLoop result then
          if post.clock = 0 then (some .timeOut, emptyEnv post)
          else StackSemEvaluate.evaluate (.loop body, decClock post)
        else (StackSemControl.exitLoop result, post) := by
  rw [StackSemEvaluate.evaluate_loop, StackSemEvaluateClock.fixClockEvaluate]

/-- Non-error Loop execution forces the actual body result to be non-error.
This is a derived induction-hypothesis side condition, not a new case premise. -/
theorem loopBodyNonError {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (source resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (.loop body, source) = (result, resultState))
    (nonerror : result ≠ some .error) :
    (StackSemEvaluate.evaluate (body, source)).1 ≠ some .error := by
  rw [evaluateLoopUnclamped] at execution
  rcases bodyExecution : StackSemEvaluate.evaluate (body, source) with ⟨bodyResult, bodyPost⟩
  rw [bodyExecution] at execution
  intro error
  change bodyResult = some .error at error
  subst bodyResult
  simp only [contLoop, StackSemControl.exitLoop, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
  exact nonerror execution.1.symm

/-- Actual recursive source state has a strictly smaller clock. -/
theorem loopReentryClockLess {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (body, source) = (result, post))
    (nonzero : post.clock ≠ 0) : (decClock post).clock < source.clock := by
  have bound := StackSemEvaluateClock.evaluateClock body source result post execution
  simp only [decClock]
  omega

/-- Exit dispatch preserves the exceptional results mentioned by the original
stack-space guard. Flapjack infrastructure for this case, not a HOL port. -/
theorem exitLoopGuard {width : Nat} [NeZero width]
    (result : Option (StackSemResult width))
    (guard : StackSemControl.exitLoop result ≠ some .timeOut ∧
      StackSemControl.exitLoop result ≠ some (.halt (.word (BitVec.ofNat width 2)))) :
    result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) := by
  constructor
  · intro h
    subst result
    exact guard.1 rfl
  · intro h
    subst result
    exact guard.2 rfl

/-- Infrastructure for the exiting branch of the genuine Loop case. The
non-continuation condition is discharged by the final case split; it is not
an additional premise of a tagged comp_correct case. -/
theorem compCorrectLoopExit {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (bodyIH : IfCase.BranchIH C F body)
    (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (body, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target)
    (exit : contLoop result = false) :
    IfCase.SimulationResult (comp info (.loop body)) info target post
      (StackSemControl.exitLoop result) := by
  obtain ⟨clock, targetState, stackSpace, postRelation, targetExecution, guard⟩ :=
    bodyIH info source target post result ⟨execution, nonerror, relation⟩
  refine ⟨clock, targetState, stackSpace, postRelation, ?_, ?_⟩
  · rw [comp, evaluateLoopUnclamped, targetExecution]
    simp only [exit, Bool.false_eq_true, if_false]
  · intro exitGuard
    exact guard (exitLoopGuard result exitGuard)

/-- Loop continuation excludes both exceptional stack-space guard results. -/
theorem contLoopGuard {width : Nat} [NeZero width]
    (result : Option (StackSemResult width)) (continuing : contLoop result = true) :
    result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) := by
  rcases Compiler.Backend.StackProps.contLoopImp result continuing with h | h <;>
    simp [h]

/-- The zero-clock continuation branch, with target timeout and relation
both derived from the actual body induction hypothesis. Untagged case support. -/
theorem compCorrectLoopTimeout {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (bodyIH : IfCase.BranchIH C F body)
    (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (body, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target)
    (continuing : contLoop result = true) (zero : post.clock = 0) :
    IfCase.SimulationResult (comp info (.loop body)) info target (emptyEnv post)
      (some .timeOut) := by
  obtain ⟨clock, targetState, stackSpace, postRelation, targetExecution, guard⟩ :=
    bodyIH info source target post result ⟨execution, nonerror, relation⟩
  have spaceEq := guard (contLoopGuard result continuing)
  subst stackSpace
  have stackSelf : { targetState with stackSpace := targetState.stackSpace } = targetState := by
    cases targetState
    rfl
  rw [stackSelf] at targetExecution
  have targetZero : targetState.clock = 0 :=
    (stateRel_clock info post targetState postRelation).trans zero
  refine ⟨clock, emptyEnv targetState, (emptyEnv targetState).stackSpace,
    stateRel_emptyEnv info post targetState postRelation, ?_, ?_⟩
  · rw [comp, evaluateLoopUnclamped, targetExecution]
    simp only [continuing, if_true]
    rw [if_pos targetZero]
  · intro impossible
    exact False.elim (impossible.1 rfl)

/-- Genuine recursive Loop IH restricted to smaller source clocks. It does
not assume simulation of the current Loop run or arbitrary whole programs. -/
abbrev LoopReentryIH {width : Nat} [NeZero width] (C F : Type)
    (body : HolProg width) (parentClock : Nat) : Prop :=
  ∀ (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)), source.clock < parentClock →
    StackSemEvaluate.evaluate (.loop body, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target →
    IfCase.SimulationResult (comp info (.loop body)) info target post result

/-- Nonzero continuation: extend the actual target body clock by the clock
needed for the smaller recursive Loop execution. All target results are derived
from the two genuine IHs. Untagged case-split infrastructure. -/
theorem compCorrectLoopReentry {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (bodyIH : IfCase.BranchIH C F body)
    (info : Spt Nat) (source target bodyPost post : StackSemStateFiniteExact width C F)
    (bodyResult result : Option (StackSemResult width))
    (reentryIH : LoopReentryIH C F body source.clock)
    (bodyExecution : StackSemEvaluate.evaluate (body, source) = (bodyResult, bodyPost))
    (bodyNonerror : bodyResult ≠ some .error) (relation : stateRel info source target)
    (continuing : contLoop bodyResult = true) (nonzero : bodyPost.clock ≠ 0)
    (execution : StackSemEvaluate.evaluate (.loop body, decClock bodyPost) = (result, post))
    (nonerror : result ≠ some .error) :
    IfCase.SimulationResult (comp info (.loop body)) info target post result := by
  obtain ⟨clock, targetBody, stackSpace, bodyRelation, targetBodyExecution, bodyGuard⟩ :=
    bodyIH info source target bodyPost bodyResult ⟨bodyExecution, bodyNonerror, relation⟩
  have continuationGuard := contLoopGuard bodyResult continuing
  have spaceEq := bodyGuard continuationGuard
  subst stackSpace
  have stackSelf : { targetBody with stackSpace := targetBody.stackSpace } = targetBody := by
    cases targetBody
    rfl
  rw [stackSelf] at targetBodyExecution
  have recursiveRelation := stateRel_decClock info bodyPost targetBody bodyRelation
  obtain ⟨recursiveClock, targetPost, finalSpace, postRelation, targetExecution, guard⟩ :=
    reentryIH info (decClock bodyPost) (decClock targetBody) post result
      (loopReentryClockLess body source bodyPost bodyResult bodyExecution nonzero)
      ⟨execution, nonerror, recursiveRelation⟩
  have targetClockEq := stateRel_clock info bodyPost targetBody bodyRelation
  have targetNonzero : targetBody.clock ≠ 0 := by
    simpa only [targetClockEq] using nonzero
  have extendedBody := Compiler.Backend.StackProps.evaluateAddClock recursiveClock
    (comp info body) { target with clock := target.clock + clock }
    bodyResult targetBody ⟨targetBodyExecution, continuationGuard.1⟩
  have inputEq : { { target with clock := target.clock + clock } with
      clock := ({ target with clock := target.clock + clock }).clock + recursiveClock } =
      { target with clock := target.clock + (clock + recursiveClock) } := by
    simp only [Nat.add_assoc]
  rw [inputEq] at extendedBody
  have reentryEq : decClock { targetBody with clock := targetBody.clock + recursiveClock } =
      { decClock targetBody with clock := (decClock targetBody).clock + recursiveClock } := by
    simp only [decClock]
    congr 1
    omega
  refine ⟨clock + recursiveClock, targetPost, finalSpace, postRelation, ?_, guard⟩
  rw [comp, evaluateLoopUnclamped, extendedBody]
  simp only [continuing, if_true]
  rw [if_neg (show targetBody.clock + recursiveClock ≠ 0 by omega), reentryEq]
  exact targetExecution

/-- Genuine recursive Loop case. The original three premises are retained;
only the body and strictly smaller-clock recursive Loop induction hypotheses
are added. Both original compTop/comp existential conclusions remain intact.
The full native evaluator inherits its documented real-carrier assurance limit;
this proof introduces no real rendering. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectLoop {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (bodyIH : IfCase.BranchIH C F body)
    (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (reentryIH : LoopReentryIH C F body source.clock)
    (hypothesis : StackSemEvaluate.evaluate (.loop body, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    IfCase.SimulationResult (compTop info (.loop body)) info target post result ∧
    IfCase.SimulationResult (comp info (.loop body)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have bodyNonerror := loopBodyNonError body source post result execution nonerror
  have same : compTop info (.loop body) = comp info (.loop body) := rfl
  rw [same]
  suffices simulation : IfCase.SimulationResult (comp info (.loop body)) info target post result by
    exact ⟨simulation, simulation⟩
  rw [evaluateLoopUnclamped] at execution
  rcases bodyExecution : StackSemEvaluate.evaluate (body, source) with ⟨bodyResult, bodyPost⟩
  rw [bodyExecution] at execution bodyNonerror
  change bodyResult ≠ some .error at bodyNonerror
  by_cases continuing : contLoop bodyResult = true
  · simp only [continuing, if_true] at execution
    by_cases zero : bodyPost.clock = 0
    · rw [if_pos zero] at execution
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      exact compCorrectLoopTimeout body bodyIH info source target bodyPost bodyResult
        bodyExecution bodyNonerror relation continuing zero
    · rw [if_neg zero] at execution
      exact compCorrectLoopReentry body bodyIH info source target bodyPost post bodyResult result
        reentryIH bodyExecution bodyNonerror relation continuing zero execution nonerror
  · have exit : contLoop bodyResult = false := by
      cases h : contLoop bodyResult <;> simp_all
    simp only [exit, Bool.false_eq_true, if_false] at execution
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
    exact compCorrectLoopExit body bodyIH info source target bodyPost bodyResult
      bodyExecution bodyNonerror relation exit

end Flapjack.Compiler.Backend.StackRawCall.LoopCase
