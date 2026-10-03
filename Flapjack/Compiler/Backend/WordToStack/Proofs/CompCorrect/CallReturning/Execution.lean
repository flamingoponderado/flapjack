import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturningHandler
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock

namespace Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Actual enclosing native NONE Call for the terminal callee branches. The
callee execution is the original IH output; dispatch derives the whole Call
run, retaining Timeout, Halt and FinalFFI and their exact native post-states.
This is case-local execution composition, not a full HOL correctness port. -/
theorem returningCallTerminalRun {width : Nat} [NeZero width] {C F : Type}
    (target targetPost : StackSemStateFiniteExact width C F)
    (l1 l2 extra : Nat) (destination : Sum Nat Nat)
    (body continuation : HolProg width) (result : Option (StackSemResult width))
    (found : StackSemControl.findCode destination (target.regs.eraseEq 0) target.code = some body)
    (nonzero : target.clock ≠ 0)
    (bodyRun : StackSemEvaluate.evaluate
      (body, {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock target) with
        clock := (StackSemStateOps.decClock target).clock + extra}) = (result, targetPost))
    (terminal : result = some .timeOut ∨ (∃ value, result = some (.halt value)) ∨
      ∃ event, result = some (.finalFFI event)) :
    StackSemEvaluate.evaluate
      (.call (some (continuation, 0, l1, l2)) destination none,
        {target with clock := target.clock + extra}) = (result, targetPost) := by
  rw [CallReturningHandler.returningCallDispatchClock target 0 l1 l2 extra
    destination body continuation none found nonzero]
  change (match StackSemEvaluate.evaluate
    (body, {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock target) with
      clock := (StackSemStateOps.decClock target).clock + extra}) with
    | (some (.result location), post) =>
        if location ≠ WordLocW.loc l1 l2 then (some StackSemResult.error, post)
        else StackSemEvaluate.evaluate (continuation, post)
    | (some (.exception location), post) => (some (.exception location), post)
    | (none, post) => (some StackSemResult.error, post)
    | (some (.break _), post) => (some StackSemResult.error, post)
    | (some (.continue _), post) => (some StackSemResult.error, post)
    | (result, post) => (result, post)) = _
  rw [bodyRun]
  rcases terminal with rfl | ⟨value, rfl⟩ | ⟨event, rfl⟩ <;> rfl

/-- Sum the actual callee and continuation IH clocks in the enclosing native
NONE Call. The original evaluate_add_clock theorem extends the successful
callee Return run by the continuation clock, then real Call dispatch executes
that continuation. No whole Call run is assumed. This untagged component
corresponds to the original 8660 normal-return clock composition. -/
theorem returningCallContinuationRun {width : Nat} [NeZero width] {C F : Type}
    (target bodyPost targetPost : StackSemStateFiniteExact width C F)
    (l1 l2 bodyExtra continuationExtra : Nat) (destination : Sum Nat Nat)
    (body continuation : HolProg width) (result : Option (StackSemResult width))
    (found : StackSemControl.findCode destination (target.regs.eraseEq 0) target.code = some body)
    (nonzero : target.clock ≠ 0)
    (bodyRun : StackSemEvaluate.evaluate
      (body, {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock target) with
        clock := (StackSemStateOps.decClock target).clock + bodyExtra}) =
      (some (.result (.loc l1 l2)), bodyPost))
    (continuationRun : StackSemEvaluate.evaluate
      (continuation, {bodyPost with clock := bodyPost.clock + continuationExtra}) =
      (result, targetPost)) :
    StackSemEvaluate.evaluate
      (.call (some (continuation, 0, l1, l2)) destination none,
        {target with clock := target.clock + (bodyExtra + continuationExtra)}) =
      (result, targetPost) := by
  have extended := Compiler.Backend.StackProps.evaluateAddClock continuationExtra body
    {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock target) with
      clock := (StackSemStateOps.decClock target).clock + bodyExtra}
    (some (.result (.loc l1 l2))) bodyPost ⟨bodyRun, by simp⟩
  simp only [Nat.add_assoc] at extended
  rw [CallReturningHandler.returningCallDispatchClock target 0 l1 l2
    (bodyExtra + continuationExtra) destination body continuation none found nonzero]
  change (match StackSemEvaluate.evaluate
    (body, {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock target) with
      clock := (StackSemStateOps.decClock target).clock + (bodyExtra + continuationExtra)}) with
    | (some (.result location), post) =>
        if location ≠ WordLocW.loc l1 l2 then (some StackSemResult.error, post)
        else StackSemEvaluate.evaluate (continuation, post)
    | (some (.exception location), post) => (some (.exception location), post)
    | (none, post) => (some StackSemResult.error, post)
    | (some (.break _), post) => (some StackSemResult.error, post)
    | (some (.continue _), post) => (some StackSemResult.error, post)
    | (result, post) => (result, post)) = _
  rw [extended]
  simpa only [ne_eq, not_true_eq_false, ↓reduceIte] using continuationRun

/-- Constructor-exact terminal result classification. It is Flapjack
infrastructure for splitting compile_result, not a separate HOL port. -/
theorem matchingTerminalSource {width : Nat} [NeZero width]
    (sourceResult : Option (WordSemResult width)) (targetResult : Option (StackSemResult width))
    (matching : sourceResult.map compileResult = targetResult)
    (terminal : targetResult = some .timeOut ∨ (∃ value, targetResult = some (.halt value)) ∨
      ∃ event, targetResult = some (.finalFFI event)) :
    sourceResult = some .timeOut ∨ sourceResult = some .notEnoughSpace ∨
      ∃ event, sourceResult = some (.finalFfi event) := by
  rw [← matching] at terminal
  cases sourceResult with
  | none => simp only [Option.map_none, reduceCtorEq, exists_false, or_self] at terminal
  | some value =>
    cases value <;> simp only [Option.map_some, compileResult, Option.some.injEq,
      reduceCtorEq, exists_false, or_self, false_or, or_false] at terminal ⊢
    case finalFfi event => exact ⟨event, rfl⟩

/-- Connect the actual terminal native Call execution with the full original
caller contract. The callee run and contract are outputs of the original
callee IH. Matching terminal results use exact source propagation; unmatched
results use the full trace/resource branch and all source outcomes remain
available. No enclosing target Call run is assumed. This is a case-local
assembly component; the full guarded theorem remains open. -/
theorem terminalCallFromCallee {width : Nat} [NeZero width] {C F : Type}
    (ac : Compiler.Encoders.Asm.AsmConfigExact width)
    (k callerSize callerFrame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (initial moved targetPost : StackSemStateFiniteExact width C F)
    (targetResult : Option (StackSemResult width)) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (extra : Nat) (destination : Sum Nat Nat) (body continuation : HolProg width)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source initial lens 0)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source = (result, sourcePost))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost))
    (found : StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some body)
    (movedNonzero : moved.clock ≠ 0)
    (calleeRun : StackSemEvaluate.evaluate
      (body, {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock + extra}) = (targetResult, targetPost))
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
      bodyPost targetPost bodyResult targetResult (callerFrame :: lens))
    (terminal : targetResult = some .timeOut ∨ (∃ value, targetResult = some (.halt value)) ∨
      ∃ event, targetResult = some (.finalFFI event)) :
    StackSemEvaluate.evaluate
      (.call (some (continuation, 0, l1, l2)) destination none,
        {moved with clock := moved.clock + extra}) = (targetResult, targetPost) ∧
    compCorrectResult ac k callerSize callerFrame source sourcePost targetPost result targetResult lens := by
  constructor
  · exact returningCallTerminalRun moved targetPost l1 l2 extra destination body continuation
      targetResult found movedNonzero calleeRun terminal
  · by_cases matching : bodyResult.map compileResult = targetResult
    · exact bodyTerminalResult ac k callerSize callerFrame calleeSize calleeFrame values names
        retCode l1 l2 dest args source sourcePost bodyPost result bodyResult targetPost targetResult
        lens xs args1 prog ss envs guards nonzero execution bodyRun
        (matchingTerminalSource bodyResult targetResult matching terminal) bodyConclusion matching
    · exact bodyMismatchResult ac k callerSize callerFrame calleeSize calleeFrame values names
        retCode l1 l2 dest args source sourcePost bodyPost result bodyResult initial targetPost
        targetResult lens xs args1 prog ss envs guards callerRelation nonzero execution bodyRun
        bodyConclusion matching

end Flapjack.WordToStackProofs.CompCorrect.CallReturning
