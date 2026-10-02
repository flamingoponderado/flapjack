import Flapjack.Compiler.Backend.StackRawCall.Proofs.InstructionSimulation

namespace Flapjack.Compiler.Backend.StackRawCall.IfCase
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Canonical codec for the imported full evaluator state, without a duplicate
carrier or assumed representation relation. Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-! Guard transport infrastructure for the genuine recursive If case of
rawcall comp_correct. No source/target evaluation is assumed by these laws. -/

theorem getVar_targetClock {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (register clock : Nat) :
    StackSemStateOps.getVar register { target with clock := clock } =
      StackSemStateOps.getVar register source := by
  obtain ⟨code, _, equality, _⟩ := relation
  subst target
  rfl

theorem getVarImm_targetClock {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target)
    (operand : Compiler.Encoders.Asm.HolRegImm width) (clock : Nat) :
    StackSemStateOps.getVarImm (Compiler.Encoders.Asm.HolRegImm.toWordRegImm operand)
      { target with clock := clock } =
    StackSemStateOps.getVarImm (Compiler.Encoders.Asm.HolRegImm.toWordRegImm operand)
      source := by
  obtain ⟨code, _, equality, _⟩ := relation
  subst target
  cases operand <;> rfl

/-- The actual compiled If dispatch reads exactly the source operands at
every target clock. Both recursive evaluations remain explicit. -/
theorem evaluateCompiledIf {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (comparison : Cmp) (register : Nat)
    (operand : Compiler.Encoders.Asm.HolRegImm width) (first second : HolProg width)
    (clock : Nat) :
    StackSemEvaluate.evaluate
      (comp info (.ite comparison register operand first second), { target with clock := clock }) =
    match StackSemStateOps.getVar register source,
      StackSemStateOps.getVarImm (Compiler.Encoders.Asm.HolRegImm.toWordRegImm operand) source with
    | some left, some right =>
      match wordSemWordCmp comparison left right with
      | some true => StackSemEvaluate.evaluate (comp info first, { target with clock := clock })
      | some false => StackSemEvaluate.evaluate (comp info second, { target with clock := clock })
      | none => (some .error, { target with clock := clock })
    | _, _ => (some .error, { target with clock := clock }) := by
  simp only [comp, StackSemEvaluate.evaluate_ite,
    getVar_targetClock info source target relation,
    getVarImm_targetClock info source target relation]
  rfl

/-! The following abbreviations spell out the original existential conclusion
and its comp component induction hypothesis. They are Flapjack infrastructure,
not alternative evaluators or supplied target results. -/
abbrev SimulationResult {width : Nat} [NeZero width] {C F : Type}
    (compiled : HolProg width) (info : Spt Nat)
    (target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) : Prop :=
  ∃ clock targetState stackSpace,
    stateRel info resultState targetState ∧
    StackSemEvaluate.evaluate (compiled, { target with clock := target.clock + clock }) =
      (result, { targetState with stackSpace := stackSpace }) ∧
    (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
      stackSpace = targetState.stackSpace)

abbrev BranchIH {width : Nat} [NeZero width] (C F : Type) (program : HolProg width) : Prop :=
  ∀ (info : Spt Nat) (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)),
    StackSemEvaluate.evaluate (program, source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target →
    SimulationResult (comp info program) info target resultState result

/-- Genuine recursive If case: only branch-program induction hypotheses are
added to the original three premises. Both original existential conclusions
are retained. The full evaluator inherits its documented real-carrier
assurance limit; this comparison/branch proof introduces no real rendering. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectIf {width : Nat} [NeZero width] {C F : Type}
    (comparison : Cmp) (register : Nat) (operand : Compiler.Encoders.Asm.HolRegImm width)
    (first second : HolProg width) (firstIH : BranchIH C F first) (secondIH : BranchIH C F second)
    (info : Spt Nat) (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.ite comparison register operand first second, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.ite comparison register operand first second))
      info target resultState result ∧
    SimulationResult (comp info (.ite comparison register operand first second))
      info target resultState result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have same : compTop info (.ite comparison register operand first second) =
      comp info (.ite comparison register operand first second) := rfl
  rw [same]
  suffices simulation : SimulationResult
      (comp info (.ite comparison register operand first second)) info target resultState result by
    exact ⟨simulation, simulation⟩
  rw [StackSemEvaluate.evaluate_ite] at execution
  split at execution
  · rename_i left right reads
    split at execution
    · rename_i compared
      obtain ⟨clock, targetState, stackSpace, postRelation, targetExecution, guard⟩ :=
        firstIH info source target resultState result ⟨execution, nonerror, relation⟩
      refine ⟨clock, targetState, stackSpace, postRelation, ?_, guard⟩
      rw [evaluateCompiledIf info source target relation]
      simp_all
    · rename_i compared
      obtain ⟨clock, targetState, stackSpace, postRelation, targetExecution, guard⟩ :=
        secondIH info source target resultState result ⟨execution, nonerror, relation⟩
      refine ⟨clock, targetState, stackSpace, postRelation, ?_, guard⟩
      rw [evaluateCompiledIf info source target relation]
      simp_all
    · simp_all
  · simp_all

end Flapjack.Compiler.Backend.StackRawCall.IfCase
