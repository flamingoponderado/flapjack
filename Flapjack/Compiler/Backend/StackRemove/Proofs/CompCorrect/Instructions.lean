import Flapjack.Compiler.Backend.StackRemove.Proofs.InstructionSimulation
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Atoms

namespace Flapjack.Compiler.Backend.StackRemove.CompCorrect.Instructions
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

/-- Canonical imported-state codec witness, Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full genuine Inst case of comp_correct: the original non-error premise
excludes native instruction failure. Full instruction simulation derives the
target execution with zero extra clock and the complete post-state relation.
Native evaluator closure retains inherited reals_as_rational_cuts. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectInst {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (instruction : HolInst width)
    (hypothesis : StackSemEvaluate.evaluate (.inst instruction, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.inst instruction) pointer) :
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.inst instruction),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  rw [StackSemEvaluate.evaluate_inst] at sourceRun
  cases instRun : StackSemInst.instHOL instruction source with
  | none =>
    rw [instRun] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some state =>
    rw [instRun] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    have instructionBound : StackProps.regBoundInst instruction pointer := bound
    obtain ⟨postTarget, targetRun, postRelation⟩ :=
      InstructionSimulation.stateRelInst jump bounds pointer instruction source target state
        ⟨relation, instructionBound, instRun⟩
    refine ⟨0, postTarget, ?_, postRelation⟩
    simpa only [comp, Nat.zero_add] using
      (StackSemEvaluate.evaluate_inst instruction target).trans (by rw [targetRun])

end Flapjack.Compiler.Backend.StackRemove.CompCorrect.Instructions
