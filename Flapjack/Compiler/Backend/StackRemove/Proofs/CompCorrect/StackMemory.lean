import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StackSpace
import Flapjack.Compiler.Backend.StackRemove.Proofs.StackHeap
import Flapjack.Compiler.Backend.StackRemove.Proofs.WordAddressArithmetic
import Flapjack.Compiler.Backend.StackRemove.Proofs.ShiftSimulation
namespace Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackMemory
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Flapjack primitive-load execution factoring; the full constructor below
 derives both lookup and memory-read premises from the source relation.
No standalone HOL declaration is claimed. -/
theorem runLoad {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (destination baseReg : Nat)
    (base offset : BitVec width) (value : WordLocW width)
    (lookup : state.regs.lookup baseReg = some (.word base))
    (read : StackSemStateOps.memLoad (base + offset) state = some value) :
    StackSemEvaluate.evaluate (.inst (.mem .load destination (.addr baseReg offset)), state) =
      (none, StackSemStateOps.setVar destination value state) := by
  simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.wordExp,
    lookup, wordOpHOL, wordOp, read]
/-- Genuine full original StackLoad compiler constructor: direct and large-offset
paths derive native execution and the complete postrelation from the original
four premises. There is no successful target-load or target-state premise. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectStackLoad {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register count pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackLoad register count, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackLoad register count : HolProg width) pointer) :
    ∃ clock postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackLoad register count),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer at lower
  rw [StackSemEvaluate.evaluate_stackLoad] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  by_cases bound : source.stackSpace + count < source.stack.length
  · rw [dif_pos bound] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    obtain ⟨base, pointerLookup, reads⟩ := StackHeap.stateRelStackReads jump bounds pointer source target relation
    change target.regs.lookup pointer = some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) at pointerLookup
    have addressEq : base + bytesInWord width * BitVec.ofNat width source.stackSpace + wordOffset count =
        base + wordOffset (source.stackSpace + count) := by
      simp [WordAddressArithmetic.wordOffsetEq, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
    have read : StackSemStateOps.memLoad
        (base + bytesInWord width * BitVec.ofNat width source.stackSpace + wordOffset count) target =
        some source.stack[source.stackSpace + count] := by
      rw [addressEq]
      exact reads (source.stackSpace + count) bound
    refine ⟨0, StackSemStateOps.setVar register source.stack[source.stackSpace + count] target, ?_, ?_⟩
    · simp only [Nat.zero_add]
      rw [comp]
      split
      · exact runLoad target register pointer _ _ _ pointerLookup read
      · have moveRun : StackSemEvaluate.evaluate (moveInst register pointer, target) =
            (none, StackSemStateOps.setVar register
              (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) target) := by
          simp [moveInst, moveHOL, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
            StackSemIntegerInstructions.instInteger, pointerLookup]
        rw [StackSemEvaluate.evaluate_seq, moveRun]
        simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
        let initial := StackSemStateOps.setVar register
          (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) target
        have initialLookup : initial.regs.lookup register =
            some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) := by
          simp [initial, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
        change StackSemEvaluate.evaluate (stackLoad register count, initial) = _
        rw [stackLoad, StackSemEvaluate.evaluate_seq,
          ShiftSimulation.evaluateUpshift count register initial _ initialLookup]
        simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
        let shifted := StackSemStateOps.setVar register
          (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace + wordOffset count)) initial
        have shiftedLookup : shifted.regs.lookup register =
            some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace + wordOffset count)) := by
          simp [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
        change StackSemEvaluate.evaluate (.inst (.mem .load register (.addr register 0)), shifted) = _
        have shiftedRead : StackSemStateOps.memLoad
            (base + bytesInWord width * BitVec.ofNat width source.stackSpace + wordOffset count + 0) shifted =
            some source.stack[source.stackSpace + count] := by
          simpa [shifted, initial, StackSemStateOps.memLoad, StackSemStateOps.setVar] using read
        rw [runLoad shifted register register _ 0 _ shiftedLookup shiftedRead]
        simp only [shifted, initial, StackFreeSimulation.setVarTwice]
        rfl
    · simpa only [relation.1] using StateUpdates.stateRelSetVar jump bounds pointer register
        source.stack[source.stackSpace + count] source target ⟨relation, lower⟩
  · rw [dif_neg bound] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
end Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackMemory
