import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Control
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateClock
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock
namespace Flapjack.Compiler.Backend.StackRemove.CompCorrect.Seq
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemControl
/-- Canonical owning-state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Source-local Seq proof infrastructure: the reviewed unconditional clock
identity recovers the original rebound evaluator equation. No independent
HOL declaration is claimed. -/
theorem evaluateSeqUnclamped {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (source : StackSemStateFiniteExact width C F) :
    evaluate (.seq first second, source) =
      match evaluate (first, source) with
      | (none, middle) => evaluate (second, middle)
      | (some result, middle) => (some result, middle) := by
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases evaluate (first, source) with ⟨result, middle⟩
  cases result <;> rfl

/-- Source-local NONE branch equation, with the actual first run as its premise; no independent HOL declaration. -/
theorem evaluateSeqNone {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (source middle : StackSemStateFiniteExact width C F)
    (execution : evaluate (first, source) = (none, middle)) :
    evaluate (.seq first second, source) = evaluate (second, middle) := by
  rw [evaluateSeqUnclamped, execution]

/-- Source-local SOME branch equation, with the actual first run as its premise; no independent HOL declaration. -/
theorem evaluateSeqSome {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (source middle : StackSemStateFiniteExact width C F)
    (result : StackSemResult width)
    (execution : evaluate (first, source) = (some result, middle)) :
    evaluate (.seq first second, source) = (some result, middle) := by
  rw [evaluateSeqUnclamped, execution]

/-- Genuine original Seq induction case. Only the two source-shaped recursive
induction hypotheses augment the original four premises: the first is fixed
at the input source; the second is guarded by the actual first NONE run.
Target evaluation and extra clocks are derived, not assumed. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectSeq {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (firstIH : ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
      (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (first, source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k source t ∧ StackProps.regBound first k →
      ∃ clock postTarget,
        evaluate (comp j off k first, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (secondIH : ∀ (middle : StackSemStateFiniteExact width C F),
      evaluate (first, source) = (none, middle) →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (second, middle) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k middle t ∧ StackProps.regBound second k →
      ∃ clock postTarget,
        evaluate (comp j off k second, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.seq first second, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.seq first second) pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer (.seq first second),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change StackProps.regBound first pointer ∧ StackProps.regBound second pointer at lower
  rcases firstRun : evaluate (first, source) with ⟨firstResult, middle⟩
  cases firstResult with
  | none =>
    rw [evaluateSeqNone first second source middle firstRun] at sourceRun
    obtain ⟨firstClock, middleTarget, firstTargetRun, middleRelation⟩ :=
      firstIH none middle target pointer bounds jump ⟨firstRun, by simp, relation, lower.1⟩
    change stateRelHOL jump bounds pointer middle middleTarget at middleRelation
    obtain ⟨secondClock, postTarget, secondTargetRun, postRelation⟩ :=
      secondIH middle firstRun result postSource middleTarget pointer bounds jump
        ⟨sourceRun, notError, middleRelation, lower.2⟩
    have extraRun := StackProps.evaluateAddClock secondClock
      (comp jump bounds pointer first) {target with clock := firstClock + target.clock}
      none middleTarget ⟨firstTargetRun, by simp⟩
    have combinedRun :
        evaluate (comp jump bounds pointer first,
          {target with clock := (firstClock + secondClock) + target.clock}) =
          (none, {middleTarget with clock := secondClock + middleTarget.clock}) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using extraRun
    refine ⟨firstClock + secondClock, postTarget, ?_, ?_⟩
    · rw [comp, evaluateSeqNone _ _ _ _ combinedRun]
      exact secondTargetRun
    · cases result with
      | none => exact postRelation
      | some value => cases value <;> exact postRelation
  | some firstResult =>
    rw [evaluateSeqSome first second source middle firstResult firstRun] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    obtain ⟨clock, postTarget, targetRun, postRelation⟩ :=
      firstIH (some firstResult) middle target pointer bounds jump
        ⟨firstRun, notError, relation, lower.1⟩
    refine ⟨clock, postTarget, ?_, ?_⟩
    · rw [comp, evaluateSeqSome _ _ _ _ _ targetRun]
    · cases firstResult <;> exact postRelation
end Flapjack.Compiler.Backend.StackRemove.CompCorrect.Seq
