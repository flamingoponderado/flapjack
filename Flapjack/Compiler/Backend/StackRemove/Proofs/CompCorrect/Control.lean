import Flapjack.Compiler.Backend.StackRemove.Proofs.RelationLaws
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef

/-! Genuine Tick and control-transfer cases of full comp_correct. These cases
retain the original source run, non-Error, full state relation and register
bound premises, and prove the original existential target run. -/
namespace Flapjack.Compiler.Backend.StackRemove.CompCorrect.Control
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original Tick case, with no added successful-run or clock premise. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectTick {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.tick, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.tick : HolProg width) pointer) :
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer .tick,
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, _notError, relation, _bound⟩
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [StackSemEvaluate.evaluate_tick] at sourceRun
  by_cases zero : source.clock = 0
  · simp only [zero, ite_true] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨0, StackSemStateOps.emptyEnv target, ?_, ?_⟩
    · simpa only [comp, Nat.zero_add] using
        (StackSemEvaluate.evaluate_tick target).trans (by simp [clocks, zero])
    · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
  · simp only [zero, ite_false] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨0, StackSemStateOps.decClock target, ?_, ?_⟩
    · simpa only [comp, Nat.zero_add] using
        (StackSemEvaluate.evaluate_tick target).trans (by simp [clocks, zero])
    · exact RelationLaws.stateRelDecClock jump bounds pointer source target relation

/-- Full original Return case, with no added successful-run or clock premise. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectReturn {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (register : Nat)
    (hypothesis : StackSemEvaluate.evaluate ((.ret register), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.ret register) : HolProg width) pointer) :
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.ret register),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have registerBound : register < pointer := bound
  have lookupEq := RelationLaws.stateRelGetVar jump bounds pointer register source target
    ⟨relation, registerBound⟩
  rw [StackSemEvaluate.evaluate_ret] at sourceRun
  cases sourceLookup : StackSemStateOps.getVar register source with
  | none =>
    rw [sourceLookup] at sourceRun
    have resultEq := (Prod.mk.inj sourceRun).1
    exact (notError resultEq.symm).elim
  | some value =>
    cases value with
    | word value =>
      rw [sourceLookup] at sourceRun
      have resultEq := (Prod.mk.inj sourceRun).1
      exact (notError resultEq.symm).elim
    | loc block offset =>
      rw [sourceLookup] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
      subst result
      subst postSource
      have targetLookup : StackSemStateOps.getVar register target = some (.loc block offset) :=
        lookupEq.symm.trans sourceLookup
      refine ⟨0, target, ?_, relation⟩
      simpa only [comp, Nat.zero_add] using
        (StackSemEvaluate.evaluate_ret register target).trans (by rw [targetLookup])

/-- Full original Raise case, with no added successful-run or clock premise. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectRaise {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (register : Nat)
    (hypothesis : StackSemEvaluate.evaluate ((.raise register), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.raise register) : HolProg width) pointer) :
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.raise register),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have registerBound : register < pointer := bound
  have lookupEq := RelationLaws.stateRelGetVar jump bounds pointer register source target
    ⟨relation, registerBound⟩
  rw [StackSemEvaluate.evaluate_raise] at sourceRun
  cases sourceLookup : StackSemStateOps.getVar register source with
  | none =>
    rw [sourceLookup] at sourceRun
    have resultEq := (Prod.mk.inj sourceRun).1
    exact (notError resultEq.symm).elim
  | some value =>
    cases value with
    | word value =>
      rw [sourceLookup] at sourceRun
      have resultEq := (Prod.mk.inj sourceRun).1
      exact (notError resultEq.symm).elim
    | loc block offset =>
      rw [sourceLookup] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
      subst result
      subst postSource
      have targetLookup : StackSemStateOps.getVar register target = some (.loc block offset) :=
        lookupEq.symm.trans sourceLookup
      refine ⟨0, target, ?_, relation⟩
      simpa only [comp, Nat.zero_add] using
        (StackSemEvaluate.evaluate_raise register target).trans (by rw [targetLookup])

/-- Full original Break case, with no added successful-run or clock premise. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectBreak {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (label : Nat)
    (hypothesis : StackSemEvaluate.evaluate ((.break label), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.break label) : HolProg width) pointer) :
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.break label),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, _notError, relation, _bound⟩
  rw [StackSemEvaluate.evaluate_break] at sourceRun
  rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
  subst result
  subst postSource
  refine ⟨0, target, ?_, relation⟩
  simp [comp, StackSemEvaluate.evaluate_break]

/-- Full original Continue case, with no added successful-run or clock premise. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectContinue {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (label : Nat)
    (hypothesis : StackSemEvaluate.evaluate ((.continue label), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.continue label) : HolProg width) pointer) :
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.continue label),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, _notError, relation, _bound⟩
  rw [StackSemEvaluate.evaluate_continue] at sourceRun
  rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
  subst result
  subst postSource
  refine ⟨0, target, ?_, relation⟩
  simp [comp, StackSemEvaluate.evaluate_continue]

end Flapjack.Compiler.Backend.StackRemove.CompCorrect.Control
