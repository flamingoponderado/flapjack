import Flapjack.Compiler.Backend.StackRemove.Proofs.StackFreeSimulation
namespace Flapjack.Compiler.Backend.StackRemove.ShiftSimulation
open Flapjack Flapjack.Compiler.Backend.StackRemove
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original arbitrary-count upshift execution theorem.
The sole premise is the original word-valued register lookup. The native
zero-count instruction is retained, and every other state field is unchanged. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateUpshift {width : Nat} [NeZero width] {C F : Type}
    (count register : Nat) (state : StackSemStateFiniteExact width C F) (value : BitVec width)
    (lookup : state.regs.lookup register = some (.word value)) :
    StackSemEvaluate.evaluate (upshift register count, state) =
      (none, StackSemStateOps.setVar register (.word (value + wordOffset count)) state) := by
  induction count using Nat.strongRecOn generalizing state value with
  | ind count ih =>
    rw [upshift]
    split
    · simpa only [singleStackFree] using StackFreeSimulation.runSingle state register count value lookup
    · change StackSemEvaluate.evaluate (.seq (singleStackFree register maxStackAlloc) (upshift register (count - maxStackAlloc)), state) = _
      rw [StackSemEvaluate.evaluate_seq, StackFreeSimulation.runSingle state register maxStackAlloc value lookup]
      simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
      have nextLookup : (StackSemStateOps.setVar register (.word (value + wordOffset maxStackAlloc)) state).regs.lookup register =
          some (.word (value + wordOffset maxStackAlloc)) := by
        simp [StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
      change StackSemEvaluate.evaluate (upshift register (count - maxStackAlloc),
        StackSemStateOps.setVar register (.word (value + wordOffset maxStackAlloc)) state) =
        (none, StackSemStateOps.setVar register (.word (value + wordOffset count)) state)
      rw [ih (count - maxStackAlloc) (by simp only [maxStackAlloc] at *; omega) _ _ nextLookup]
      rw [StackFreeSimulation.setVarTwice]
      have offsets : (wordOffset maxStackAlloc : BitVec width) + wordOffset (count - maxStackAlloc) = wordOffset count := by
        rw [wordOffset, wordOffset, wordOffset, ← BitVec.ofNat_add]
        have countEq : maxStackAlloc + (count - maxStackAlloc) = count := by omega
        rw [← Nat.mul_add, countEq]
      rw [BitVec.add_assoc, offsets]
/-- Native single-Sub execution factoring; Flapjack infrastructure with no
standalone HOL declaration. -/
theorem runSub {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (register count : Nat) (value : BitVec width)
    (lookup : state.regs.lookup register = some (.word value)) :
    StackSemEvaluate.evaluate (.inst (.arith (.binop .sub register register (.imm (wordOffset count)))), state) =
      (none, StackSemStateOps.setVar register (.word (value - wordOffset count)) state) := by
  simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, lookup, wordOpHOL, wordOp]
/-- Full original arbitrary-count downshift execution theorem.
The sole premise is the original word-valued register lookup. The native
zero-count instruction is retained, and every other state field is unchanged. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateDownshift {width : Nat} [NeZero width] {C F : Type}
    (count register : Nat) (state : StackSemStateFiniteExact width C F) (value : BitVec width)
    (lookup : state.regs.lookup register = some (.word value)) :
    StackSemEvaluate.evaluate (downshift register count, state) =
      (none, StackSemStateOps.setVar register (.word (value - wordOffset count)) state) := by
  induction count using Nat.strongRecOn generalizing state value with
  | ind count ih =>
    rw [downshift]
    split
    · exact runSub state register count value lookup
    · rw [StackSemEvaluate.evaluate_seq, runSub state register maxStackAlloc value lookup]
      simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
      have nextLookup : (StackSemStateOps.setVar register (.word (value - wordOffset maxStackAlloc)) state).regs.lookup register =
          some (.word (value - wordOffset maxStackAlloc)) := by
        simp [StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
      change StackSemEvaluate.evaluate (downshift register (count - maxStackAlloc),
        StackSemStateOps.setVar register (.word (value - wordOffset maxStackAlloc)) state) =
        (none, StackSemStateOps.setVar register (.word (value - wordOffset count)) state)
      rw [ih (count - maxStackAlloc) (by simp only [maxStackAlloc] at *; omega) _ _ nextLookup]
      rw [StackFreeSimulation.setVarTwice]
      have offsets : (wordOffset maxStackAlloc : BitVec width) + wordOffset (count - maxStackAlloc) = wordOffset count := by
        rw [wordOffset, wordOffset, wordOffset, ← BitVec.ofNat_add]
        have countEq : maxStackAlloc + (count - maxStackAlloc) = count := by omega
        rw [← Nat.mul_add, countEq]
      rw [BitVec.sub_sub, offsets]
end Flapjack.Compiler.Backend.StackRemove.ShiftSimulation
