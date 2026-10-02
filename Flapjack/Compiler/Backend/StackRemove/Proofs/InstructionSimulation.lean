import Flapjack.Compiler.Backend.StackRemove.Proofs.InstructionSimulation.Arithmetic
import Flapjack.Compiler.Backend.StackRemove.Proofs.InstructionSimulation.Binary
import Flapjack.Compiler.Backend.StackRemove.Proofs.InstructionSimulation.Memory
import Flapjack.Compiler.Backend.StackRemove.Proofs.InstructionSimulation.FloatingPoint

namespace Flapjack.Compiler.Backend.StackRemove.InstructionSimulation
open Flapjack Compiler.Encoders.Asm

/-- Canonical actual-state codec witness, Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Complete original arbitrary-instruction simulation, all five outer
constructors, eight arithmetic operations, eight memory opcodes and sixteen FP
opcodes. Only the original full relation, instruction bound and source success
are premises. Successful target execution and its full post-state relation are
proved. Native FP retains the inherited reals_as_rational_cuts assumption. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_inst"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelInst {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (instruction : HolInst width) (source target postSource : StackSemStateFiniteExact width C F)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      StackProps.regBoundInst instruction pointer ∧
      StackSemInst.instHOL instruction source = some postSource) :
    ∃ postTarget, StackSemInst.instHOL instruction target = some postTarget ∧
      stateRelHOL jump bounds pointer postSource postTarget := by
  cases instruction with
  | skip => exact Atoms.stateRelInstSkip jump bounds pointer source target postSource hypothesis
  | const register value =>
    exact Atoms.stateRelInstConst jump bounds pointer register value source target postSource hypothesis
  | mem operator register address =>
    exact Memory.stateRelInstMem jump bounds pointer register operator address source target postSource hypothesis
  | fp operation =>
    exact FloatingPoint.stateRelInstFp jump bounds pointer operation source target postSource hypothesis
  | arith operation =>
    cases operation with
    | binop operator destination input right =>
      exact Binary.stateRelInstBinop jump bounds pointer destination input operator right source target postSource hypothesis
    | shift operator destination input right =>
      exact Binary.stateRelInstShift jump bounds pointer destination input operator right source target postSource hypothesis
    | div r1 r2 r3 =>
      exact Arithmetic.stateRelInstDiv jump bounds pointer r1 r2 r3 source target postSource hypothesis
    | addCarry r1 r2 r3 r4 =>
      exact Arithmetic.stateRelInstAddCarry jump bounds pointer r1 r2 r3 r4 source target postSource hypothesis
    | addOverflow r1 r2 r3 r4 =>
      exact Arithmetic.stateRelInstAddOverflow jump bounds pointer r1 r2 r3 r4 source target postSource hypothesis
    | subOverflow r1 r2 r3 r4 =>
      exact Arithmetic.stateRelInstSubOverflow jump bounds pointer r1 r2 r3 r4 source target postSource hypothesis
    | longMul r1 r2 r3 r4 =>
      exact Arithmetic.stateRelInstLongMul jump bounds pointer r1 r2 r3 r4 source target postSource hypothesis
    | longDiv r1 r2 r3 r4 r5 =>
      exact Arithmetic.stateRelInstLongDiv jump bounds pointer r1 r2 r3 r4 r5 source target postSource hypothesis

end Flapjack.Compiler.Backend.StackRemove.InstructionSimulation
