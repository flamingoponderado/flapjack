import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Install
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateClock

namespace Flapjack.Compiler.Backend.StackRawCall.SeqCase
open Flapjack Flapjack.Compiler.Backend.StackLang
open IfCase

/-- Source-local Seq equation. The original evaluator's clock theorem removes
its redundant clamp; this is infrastructure, not a separate HOL declaration. -/
theorem evaluateSeqUnclamped {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (source : StackSemStateFiniteExact width C F) :
    StackSemEvaluate.evaluate (.seq first second, source) =
      match StackSemEvaluate.evaluate (first, source) with
      | (none, middle) => StackSemEvaluate.evaluate (second, middle)
      | (some result, middle) => (some result, middle) := by
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases StackSemEvaluate.evaluate (first, source) with ⟨result, middle⟩
  cases result <;> rfl

/-- The genuine second evaluate_ind hypothesis is available only after the
actual first NONE run. Flapjack notation, not an independent HOL declaration. -/
abbrev SeqSecondIH {width : Nat} [NeZero width] (C F : Type)
    (first second : HolProg width) (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ middle : StackSemStateFiniteExact width C F,
    StackSemEvaluate.evaluate (first, source) = (none, middle) →
    ProgramIH C F second middle

/-- Complete standard composition in original175-194, before the compiler's
optimized Seq split. This source-local proof infrastructure has no separately
named HOL declaration, so carries no comp_correct tag. Its target is the actual
standard compiled Seq: the full parent still needs the optimized equal/less/
greater frame branches and the assembling theorem. Only the actual first and
guarded second evaluate_ind hypotheses supplement the original three premises.
Inherits reals_as_rational_cuts, SOUNDNESS item8. -/
theorem simulateStandardSeq {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (firstIH : ProgramIH C F first source)
    (secondIH : SeqSecondIH C F first second source)
    (hypothesis : StackSemEvaluate.evaluate (.seq first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (.seq (comp info first) (comp info second)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  rcases firstRun : StackSemEvaluate.evaluate (first, source) with ⟨firstResult, middle⟩
  cases firstResult with
  | none =>
      rw [evaluateSeqUnclamped, firstRun] at execution
      obtain ⟨firstClock, targetMiddle, firstSpace, middleRelation, firstTargetRun, firstGuard⟩ :=
        firstIH info target middle none ⟨firstRun, by simp, relation⟩
      have spaceEq := firstGuard (by simp)
      subst firstSpace
      have spaceSelf : { targetMiddle with stackSpace := targetMiddle.stackSpace } =
          targetMiddle := by cases targetMiddle; rfl
      rw [spaceSelf] at firstTargetRun
      obtain ⟨secondClock, targetPost, finalSpace, postRelation, secondTargetRun, finalGuard⟩ :=
        secondIH middle firstRun info targetMiddle post result
          ⟨execution, nonerror, middleRelation⟩
      have extendedFirst := Compiler.Backend.StackProps.evaluateAddClock secondClock
        (comp info first) { target with clock := target.clock + firstClock }
        none targetMiddle ⟨firstTargetRun, by simp⟩
      have inputEq : { { target with clock := target.clock + firstClock } with
          clock := ({ target with clock := target.clock + firstClock }).clock + secondClock } =
          { target with clock := target.clock + (firstClock + secondClock) } := by
        simp only [Nat.add_assoc]
      rw [inputEq] at extendedFirst
      refine ⟨firstClock + secondClock, targetPost, finalSpace, postRelation, ?_, finalGuard⟩
      rw [evaluateSeqUnclamped, extendedFirst]
      exact secondTargetRun
  | some firstResult =>
      rw [evaluateSeqUnclamped, firstRun] at execution
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      obtain ⟨clock, targetPost, finalSpace, postRelation, targetRun, guard⟩ :=
        firstIH info target middle (some firstResult) ⟨firstRun, nonerror, relation⟩
      refine ⟨clock, targetPost, finalSpace, postRelation, ?_, guard⟩
      rw [evaluateSeqUnclamped, targetRun]

end Flapjack.Compiler.Backend.StackRawCall.SeqCase
