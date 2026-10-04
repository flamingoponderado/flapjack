import Mathlib.Data.Nat.Basic
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Seq.Standard
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.RawCall

namespace Flapjack.Compiler.Backend.StackRawCall.SeqCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open IfCase

/-- Flapjack notation for the three actual compSeq output forms. This is a
source-local expression, not a replacement compiler or separate HOL port. -/
abbrev optimizedSeq {width : Nat} [NeZero width] (released allocated dest : Nat) : HolProg width :=
  if allocated = released then .rawCall dest
  else if allocated < released then .seq (.stackFree (released - allocated)) (.rawCall dest)
  else .seq .tick (.seq (.stackAlloc (allocated - released)) (.rawCall dest))

/-- Code-independent stack-space update of the literal relation; Flapjack
infrastructure, with no independently named HOL declaration. -/
theorem stateRel_setStackSpace {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (space : Nat) :
    stateRel info {source with stackSpace := space} {target with stackSpace := space} := by
  obtain ⟨code, domain, targetEq, frames, entries⟩ := relation
  subst target
  exact ⟨code, domain, rfl, frames, entries⟩

/-- Native direct-call equation for an actual entry allocation. Flapjack
infrastructure exposing all allocation/error/body outcomes, not a target run
assumption or a changed evaluator. -/
theorem evaluateCallAlloc {width : Nat} [NeZero width] {C F : Type}
    (dest allocated : Nat) (body : HolProg width) (s : StackSemStateFiniteExact width C F)
    (entry : sptLookup dest s.code = some (.seq (.stackAlloc allocated) body)) :
    StackSemEvaluate.evaluate (.call none (.inl dest) none, s) =
      if s.clock = 0 then (some .timeOut, emptyEnv s)
      else if !s.useStack then (some .error, decClock s)
      else if s.stackSpace < allocated then
        (some (.halt (.word (BitVec.ofNat width 2))), emptyEnv (decClock s))
      else match StackSemEvaluate.evaluate
          (body, {decClock s with stackSpace := s.stackSpace - allocated}) with
        | (result, post) => if badFunReturn result then (some .error, post) else (result, post) := by
  rw [StackSemEvaluate.evaluate_call]
  simp only [findCode, entry]
  simp only [StackSemEvaluateClock.fixClockEvaluate]
  simp only [evaluateSeqUnclamped, StackSemEvaluate.evaluate_stackAlloc, decClock]
  split_ifs <;> simp_all [badFunReturn]

/-- Actual successful-allocation transport for all three compiler output forms.
All body outcomes, including errors and timeouts, are preserved. The one extra
clock in the greater branch is consumed by its actual Tick. Source-local
infrastructure; its guards are derived by the final Seq case, not assumed there. -/
theorem successfulOptimization {width : Nat} [NeZero width] {C F : Type}
    (released allocated dest : Nat) (body : HolProg width)
    (s : StackSemStateFiniteExact width C F)
    (entry : sptLookup dest s.code = some (.seq (.stackAlloc allocated) body))
    (useStack : s.useStack = true) (bounds : s.stackSpace + released ≤ s.stack.length)
    (space : allocated ≤ s.stackSpace + released) (nonzero : s.clock ≠ 0) :
    StackSemEvaluate.evaluate (optimizedSeq released allocated dest,
      {s with clock := s.clock + (if released < allocated then 1 else 0)}) =
    StackSemEvaluate.evaluate (.call none (.inl dest) none,
      {s with stackSpace := s.stackSpace + released}) := by
  rw [evaluateCallAlloc dest allocated body {s with stackSpace := s.stackSpace + released} entry]
  by_cases equal : allocated = released
  · subst allocated
    have allocationSafe : ¬ s.stackSpace + released < released := by omega
    simp [optimizedSeq, StackSemEvaluate.evaluate_rawCall, entry, destSeq,
      useStack, nonzero, allocationSafe, decClock]
    rfl
  · by_cases less : allocated < released
    · have releaseSafe : ¬ s.stack.length < s.stackSpace + (released - allocated) := by omega
      have finalSpace : s.stackSpace + released - allocated =
          s.stackSpace + (released - allocated) := by omega
      simp [optimizedSeq, equal, less, show ¬ released < allocated by omega,
        evaluateSeqUnclamped, StackSemEvaluate.evaluate_stackFree,
        StackSemEvaluate.evaluate_rawCall, entry, destSeq, useStack, releaseSafe,
        nonzero, show ¬ s.stackSpace + released < allocated by omega, decClock, finalSpace]
      rfl
    · have greater : released < allocated := by omega
      have allocateSafe : ¬ s.stackSpace < allocated - released := by omega
      have finalSpace : s.stackSpace + released - allocated =
          s.stackSpace - (allocated - released) := by omega
      simp [optimizedSeq, equal, less, greater, evaluateSeqUnclamped,
        StackSemEvaluate.evaluate_tick, StackSemEvaluate.evaluate_stackAlloc,
        StackSemEvaluate.evaluate_rawCall, entry, destSeq, useStack, allocateSafe,
        nonzero, show ¬ s.stackSpace + released < allocated by omega, decClock, finalSpace]
      rfl

/-- Native zero-clock optimized outcomes. EmptyEnv retains stackSpace: the
original timeout exception permits the resulting space to differ. Infrastructure
used to derive the original guarded existential result, not a stronger claim. -/
theorem zeroOptimization {width : Nat} [NeZero width] {C F : Type}
    (released allocated dest : Nat) (body : HolProg width)
    (s : StackSemStateFiniteExact width C F)
    (entry : sptLookup dest s.code = some (.seq (.stackAlloc allocated) body))
    (useStack : s.useStack = true) (bounds : s.stackSpace + released ≤ s.stack.length)
    (zero : s.clock = 0) :
    StackSemEvaluate.evaluate (optimizedSeq released allocated dest, s) =
      (some .timeOut, {emptyEnv s with stackSpace :=
        if allocated < released then s.stackSpace + (released - allocated) else s.stackSpace}) := by
  by_cases equal : allocated = released
  · subst allocated
    simp [optimizedSeq, StackSemEvaluate.evaluate_rawCall, entry, destSeq, zero, emptyEnv]
  · by_cases less : allocated < released
    · have safe : ¬ s.stack.length < s.stackSpace + (released - allocated) := by omega
      simp [optimizedSeq, equal, less, evaluateSeqUnclamped,
        StackSemEvaluate.evaluate_stackFree, StackSemEvaluate.evaluate_rawCall,
        entry, destSeq, useStack, safe, zero, emptyEnv]
    · simp [optimizedSeq, equal, less, evaluateSeqUnclamped,
        StackSemEvaluate.evaluate_tick, zero, emptyEnv]

/-- The greater-frame allocation-failure outcome uses no extra clock: Tick
consumes exactly the original Call's clock. Stack-space equality is exempt for
Halt Word2 in the original theorem. Source-local native infrastructure. -/
theorem failedOptimization {width : Nat} [NeZero width] {C F : Type}
    (released allocated dest : Nat) (s : StackSemStateFiniteExact width C F)
    (useStack : s.useStack = true) (failure : s.stackSpace + released < allocated)
    (nonzero : s.clock ≠ 0) :
    StackSemEvaluate.evaluate (optimizedSeq released allocated dest, s) =
      (some (.halt (.word (BitVec.ofNat width 2))), emptyEnv (decClock s)) := by
  have greater : released < allocated := by omega
  have allocationFailure : s.stackSpace < allocated - released := by omega
  simp [optimizedSeq, show allocated ≠ released by omega,
    show ¬ allocated < released by omega, evaluateSeqUnclamped,
    StackSemEvaluate.evaluate_tick, StackSemEvaluate.evaluate_stackAlloc,
    useStack, allocationFailure, nonzero, decClock]

/-- Complete optimized source subcase. The frame lookup is the compiler's
actual branch guard; the only recursive premise is the original second-program
IH after the actual StackFree NONE run. Target execution is derived from that
IH and native transport, never supplied as a theorem premise. Flapjack source-
local infrastructure for the assembling comp_correct Seq case. -/
theorem simulateOptimizedSeq {width : Nat} [NeZero width] {C F : Type}
    (released allocated dest : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (frame : sptLookup dest info = some allocated)
    (secondIH : SeqSecondIH C F (.stackFree released) (.call none (.inl dest) none) source)
    (hypothesis : StackSemEvaluate.evaluate
        (.seq (.stackFree released) (.call none (.inl dest) none), source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (optimizedSeq released allocated dest) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have originalRelation := relation
  obtain ⟨code, domain, targetEq, frames, entries⟩ := relation
  have targetSpace : target.stackSpace = source.stackSpace := by rw [targetEq]
  have targetClock : target.clock = source.clock := by rw [targetEq]
  have clockSelf : {target with clock := target.clock + 0} = target := by cases target; simp
  rw [evaluateSeqUnclamped, StackSemEvaluate.evaluate_stackFree] at execution
  by_cases enabled : source.useStack = true
  · simp only [enabled, Bool.not_true, Bool.false_eq_true, if_false] at execution
    by_cases badBounds : source.stack.length < source.stackSpace + released
    · simp only [badBounds, if_true, Prod.mk.injEq] at execution
      exact False.elim (nonerror execution.1.symm)
    · simp only [badBounds, if_false] at execution
      have firstRun : StackSemEvaluate.evaluate (.stackFree released, source) =
          (none, {source with stackSpace := source.stackSpace + released}) := by
        simp [StackSemEvaluate.evaluate_stackFree, enabled, badBounds]
      have shiftedRelation := stateRel_setStackSpace info source target originalRelation
        (source.stackSpace + released)
      have targetEnabled : target.useStack = true := by simpa only [targetEq] using enabled
      have targetBounds : target.stackSpace + released ≤ target.stack.length := by
        simpa only [targetEq] using (show source.stackSpace + released ≤ source.stack.length by omega)
      obtain ⟨body, sourceEntry⟩ := frames dest allocated frame
      obtain ⟨entryInfo, _, targetLookup⟩ := RawCallCase.rawCallEntry info source target originalRelation
        dest (.stackAlloc allocated) body sourceEntry
      have targetEntry : sptLookup dest target.code =
          some (.seq (.stackAlloc allocated) (comp entryInfo body)) := by
        simpa only [comp] using targetLookup
      replace execution : StackSemEvaluate.evaluate (.call none (.inl dest) none,
          {source with stackSpace := source.stackSpace + released}) = (result, post) := by
        simpa only [enabled] using execution
      have callExecution := execution
      rw [evaluateCallAlloc dest allocated body
        {source with stackSpace := source.stackSpace + released} sourceEntry] at execution
      by_cases zero : source.clock = 0
      · simp only [zero, if_true, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        let targetPost := emptyEnv {target with stackSpace := source.stackSpace + released}
        refine ⟨0, targetPost,
          (if allocated < released then target.stackSpace + (released - allocated)
           else target.stackSpace), ?_, ?_, by simp⟩
        · simpa only [zero] using LoopCase.stateRel_emptyEnv info
            {source with stackSpace := source.stackSpace + released}
            {target with stackSpace := source.stackSpace + released} shiftedRelation
        · rw [clockSelf]
          simpa only [targetPost, emptyEnv] using
            zeroOptimization released allocated dest (comp entryInfo body) target targetEntry
              targetEnabled targetBounds (targetClock.trans zero)
      · simp only [zero, if_false,
          if_neg (show ¬ (!source.useStack) = true by simp [enabled])] at execution
        by_cases failure : source.stackSpace + released < allocated
        · simp only [failure, if_true, Prod.mk.injEq] at execution
          obtain ⟨rfl, rfl⟩ := execution
          let targetPost := emptyEnv (decClock {target with
            stackSpace := source.stackSpace + released})
          refine ⟨0, targetPost, target.stackSpace,
            LoopCase.stateRel_emptyEnv info _ _
              (LoopCase.stateRel_decClock info _ _ shiftedRelation), ?_, by simp⟩
          rw [clockSelf]
          simpa only [targetPost, emptyEnv, decClock] using
            failedOptimization released allocated dest target targetEnabled
              (by simpa only [targetSpace] using failure) (by simpa only [targetClock] using zero)
        · obtain ⟨clock, targetPost, finalSpace, postRelation, targetRun, guard⟩ :=
            secondIH {source with stackSpace := source.stackSpace + released} firstRun
              info {target with stackSpace := source.stackSpace + released} post result
              ⟨callExecution, nonerror, shiftedRelation⟩
          change StackSemEvaluate.evaluate (.call none (.inl dest) none,
            {{target with stackSpace := source.stackSpace + released} with
              clock := target.clock + clock}) = (result, {targetPost with stackSpace := finalSpace}) at targetRun
          have callInput : {{target with stackSpace := source.stackSpace + released} with
              clock := target.clock + clock} =
              {{target with clock := target.clock + clock} with
                stackSpace := target.stackSpace + released} := by rw [targetSpace]
          rw [callInput] at targetRun
          have transport := successfulOptimization released allocated dest (comp entryInfo body)
            {target with clock := target.clock + clock} targetEntry targetEnabled targetBounds
            (by simpa only [targetSpace] using (show allocated ≤ source.stackSpace + released by omega))
            (by simp only; rw [targetClock]; omega)
          have combinedInput : {{target with clock := target.clock + clock} with
              clock := ({target with clock := target.clock + clock}).clock +
                (if released < allocated then 1 else 0)} =
              {target with clock := target.clock + (clock + (if released < allocated then 1 else 0))} := by
            simp only [Nat.add_assoc]
          rw [combinedInput] at transport
          refine ⟨clock + (if released < allocated then 1 else 0), targetPost, finalSpace,
            postRelation, ?_, guard⟩
          rw [transport]
          exact targetRun
  · have disabled : source.useStack = false := by cases source.useStack <;> simp_all
    simp only [disabled, Bool.not_false, if_true, Prod.mk.injEq] at execution
    exact False.elim (nonerror execution.1.symm)

end Flapjack.Compiler.Backend.StackRawCall.SeqCase
