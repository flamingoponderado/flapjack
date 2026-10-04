import Flapjack.Compiler.Backend.StackRawCall.Proofs.InstructionTransport
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef

namespace Flapjack.Compiler.Backend.StackRawCall
open Flapjack Flapjack.Compiler.Backend.StackLang

namespace InstructionSimulationSupport
/-- Canonical imported full-state codec; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness
end InstructionSimulationSupport

/-- Full original instruction simulation. The target execution and post-state
relation are derived from the actual primitive; no target result, clock bound
or postrelation is assumed. All integer/memory and sixteen FP constructors are
covered. Native FP retains the inherited reals_as_rational_cuts external
assumption; this transport proof does not establish HOL/Lean real equivalence. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCompInst {width : Nat} [NeZero width] {C F : Type}
    (instruction : Compiler.Encoders.Asm.HolInst width) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.inst instruction, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    ∃ clock targetState stackSpace,
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate
        (comp info (.inst instruction), { target with clock := clock + target.clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace) := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  rw [StackSemEvaluate.evaluate_inst] at execution
  cases primitive : StackSemInst.instHOL instruction source with
  | none => simp [primitive] at execution; obtain ⟨rfl, _⟩ := execution; exact (nonerror rfl).elim
  | some state =>
    simp only [primitive, Prod.mk.injEq] at execution
    obtain ⟨rfl, rfl⟩ := execution
    obtain ⟨targetState, postRelation, targetExecution⟩ :=
      instHOL_stateRel instruction info source target state relation primitive
    refine ⟨0, targetState, targetState.stackSpace, postRelation, ?_, fun _ => rfl⟩
    have clockSelf : { target with clock := 0 + target.clock } = target := by
      cases target
      simp
    have stackSelf : { targetState with stackSpace := targetState.stackSpace } = targetState := by
      cases targetState
      rfl
    rw [clockSelf, stackSelf]
    simp only [comp, StackSemEvaluate.evaluate_inst, targetExecution]

end Flapjack.Compiler.Backend.StackRawCall
