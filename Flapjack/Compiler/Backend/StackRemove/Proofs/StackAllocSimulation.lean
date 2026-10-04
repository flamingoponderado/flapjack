import Flapjack.Compiler.Backend.StackRemove.Proofs.StackFreeSimulation
import Flapjack.Compiler.Backend.StackRemove.Proofs.AllocationArithmetic
import Flapjack.Compiler.Backend.StackRemove.StackAlloc
namespace Flapjack.Compiler.Backend.StackRemove.StackAllocSimulation
open Flapjack.Compiler.Backend.StackRemove
open Flapjack
/-- Flapjack factoring of original single_stack_alloc successful post-relation
proof. No separately named HOL declaration corresponds to this helper. The
original available-space condition is discharged in the full theorem below;
all26 relation conjuncts are established rather than assumed. -/
theorem stateRelAllocStep {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target)
    (safe : count ≤ source.stackSpace) :
    stateRelHOL jump bounds pointer {source with stackSpace := source.stackSpace - count}
      (StackSemStateOps.setVar pointer
        (.word ((match target.regs.lookup pointer with | some (.word value) => value | _ => 0) - wordOffset count)) target) := by
  obtain ⟨base, baseLookup, lower, upper, pointerLookup, heap⟩ :=
    StackPointer.stateRelGetVarK jump bounds pointer source target relation
  change target.regs.lookup (pointer + 1) = some (.word base) at baseLookup
  change target.regs.lookup pointer = some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) at pointerLookup
  have arithmetic : (base + bytesInWord width * BitVec.ofNat width source.stackSpace) - wordOffset count =
      base + bytesInWord width * BitVec.ofNat width (source.stackSpace - count) := by
    have parts : BitVec.ofNat width source.stackSpace =
        BitVec.ofNat width (source.stackSpace - count) + BitVec.ofNat width count := by
      rw [← BitVec.ofNat_add, Nat.sub_add_cancel safe]
    have offset : bytesInWord width * BitVec.ofNat width count = wordOffset count := by
      simp [bytesInWord, wordOffset, BitVec.ofNat_mul]
    rw [parts, BitVec.mul_add, offset, ← BitVec.add_assoc]
    exact BitVec.add_sub_cancel _ _
  have baseNe : pointer + 1 ≠ pointer := by omega
  have heapNe : pointer + 2 ≠ pointer := by omega
  simp only [stateRelHOL] at relation
  rcases relation with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩
  have low : ∀ query, query < pointer →
      (target.regs.updateEq (pointer, .word (base + bytesInWord width * BitVec.ofNat width (source.stackSpace - count)))).lookup query = source.regs.lookup query := by
    intro query below
    have ne : query ≠ pointer := by omega
    simpa only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne, ite_false] using h18 query below
  simp only [stateRelHOL, StackSemStateOps.setVar, pointerLookup, arithmetic,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, baseNe, heapNe, ite_false, ite_true, baseLookup]
  exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,low,h19,h20,h21,h22,h23,Nat.le_trans (Nat.sub_le _ _) h24,
    h25.1,lower,upper,True.intro,heap⟩
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Complete original single_stack_alloc simulation, including both native
jump and conditional overflow modes and the original FFI/full-relation split.
Every original conjunct is retained and no target evaluation is assumed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateSingleStackAlloc {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      (result, postSource) = (if source.stackSpace < count then
        (some (.halt (.word 2)), StackSemStateOps.emptyEnv source)
        else (none, {source with stackSpace := source.stackSpace - count})) ∧
      count ≠ 0 ∧ count ≤ maxStackAlloc) :
    ∃ clock postTarget,
      StackSemEvaluate.evaluate (singleStackAlloc jump pointer count,
        {target with clock := target.clock + clock}) = (result, postTarget) ∧
      (if source.stackSpace < count then postTarget.ffi = postSource.ffi
       else stateRelHOL jump bounds pointer postSource postTarget) := by
  classical
  rcases hypothesis with ⟨relation, output, _nonzero, countBound⟩
  obtain ⟨base, baseLookup, lower, upper, pointerLookup, _heap⟩ :=
    StackPointer.stateRelGetVarK jump bounds pointer source target relation
  change target.regs.lookup (pointer + 1) = some (.word base) at baseLookup
  change target.regs.lookup pointer = some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) at pointerLookup
  have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spaceBound : source.stackSpace ≤ source.stack.length := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have comparison := AllocationArithmetic.allocationGuard base source.stackSpace source.stack.length count good lower upper spaceBound countBound
  have guard : Compiler.Encoders.Asm.wordCmpHOL .lower
      (base + bytesInWord width * BitVec.ofNat width source.stackSpace - wordOffset count) base =
      decide (source.stackSpace < count) := by
    simp only [Compiler.Encoders.Asm.wordCmpHOL, comparison]
  have codeLookup : sptLookup stackErrLab target.code = some (haltInst (BitVec.ofNat width 2)) := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have baseNe : pointer + 1 ≠ pointer := by omega
  by_cases overflow : source.stackSpace < count
  · rw [if_pos overflow] at output
    rcases Prod.mk.inj output with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    simp only [overflow, decide_true] at guard
    cases jump with
    | false =>
      refine ⟨1, StackSemStateOps.emptyEnv {target with clock := target.clock + 1}, ?_, ?_⟩
      · simp [singleStackAlloc,  StackSemStateOps.emptyEnv, StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_inst,
          StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
          StackSemExpressions.assign, StackSemExpressions.wordExp, pointerLookup,
          wordOpHOL, wordOp, StackSemControl.fixClock,
          StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          StackSemEvaluate.evaluate_ite,
          StackSemStateOps.getVar, StackSemStateOps.getVarImm, Compiler.Encoders.Asm.HolRegImm.toWordRegImm,
          wordSemWordCmp, baseLookup, guard,
            haltInst,
          StackSemEvaluate.evaluate_halt]
      · simpa [overflow, StackSemStateOps.emptyEnv] using relation.2.2.2.2.2.2.2.2.2.1
    | true =>
      refine ⟨1, StackSemStateOps.emptyEnv target, ?_, ?_⟩
      · simp [singleStackAlloc,  StackSemStateOps.emptyEnv, StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_inst,
          StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
          StackSemExpressions.assign, StackSemExpressions.wordExp, pointerLookup,
          wordOpHOL, wordOp, StackSemControl.fixClock,
          StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
           StackSemEvaluate.evaluate_jumpLower,
          StackSemStateOps.getVar,
           baseLookup, guard,
          StackSemControl.findCode, codeLookup, haltInst,
          StackSemEvaluate.evaluate_halt, StackSemStateOps.decClock, StackSemControl.badFunReturn]
      · simpa [overflow, StackSemStateOps.emptyEnv] using relation.2.2.2.2.2.2.2.2.2.1
  · rw [if_neg overflow] at output
    rcases Prod.mk.inj output with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨0, StackSemStateOps.setVar pointer
      (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace - wordOffset count)) target, ?_, ?_⟩
    · cases jump <;> simp [singleStackAlloc,  StackSemEvaluate.evaluate_seq,
        StackSemEvaluate.evaluate_inst, StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
        StackSemExpressions.assign, StackSemExpressions.wordExp, pointerLookup, wordOpHOL, wordOp,
        StackSemControl.fixClock, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
        StackSemEvaluate.evaluate_ite, StackSemEvaluate.evaluate_jumpLower, StackSemEvaluate.evaluate_skip,
        StackSemStateOps.getVar, StackSemStateOps.getVarImm, Compiler.Encoders.Asm.HolRegImm.toWordRegImm, wordSemWordCmp, baseLookup, guard, overflow]
    · rw [if_neg overflow]
      simpa only [pointerLookup] using stateRelAllocStep jump bounds pointer count source target relation (Nat.le_of_not_gt overflow)
/-- Source-local execution factoring for a successful native allocation chunk at any clock.
No standalone HOL declaration; guard facts are derived from the full relation. -/
theorem runSingleAvailable {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count clock : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target)
    (available : count ≤ source.stackSpace) (countBound : count ≤ maxStackAlloc) :
    StackSemEvaluate.evaluate (singleStackAlloc jump pointer count, {target with clock := clock}) =
      (none, StackSemStateOps.setVar pointer
        (.word ((match target.regs.lookup pointer with | some (.word word) => word | _ => 0) - wordOffset count))
        {target with clock := clock}) := by
  obtain ⟨base, baseLookup, lower, upper, pointerLookup, _heap⟩ :=
    StackPointer.stateRelGetVarK jump bounds pointer source target relation
  change target.regs.lookup (pointer + 1) = some (.word base) at baseLookup
  change target.regs.lookup pointer = some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) at pointerLookup
  have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spaceBound : source.stackSpace ≤ source.stack.length := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have comparison := AllocationArithmetic.allocationGuard base source.stackSpace source.stack.length count good lower upper spaceBound countBound
  have guard : Compiler.Encoders.Asm.wordCmpHOL .lower
      (base + bytesInWord width * BitVec.ofNat width source.stackSpace - wordOffset count) base =
      decide (source.stackSpace < count) := by
    simp only [Compiler.Encoders.Asm.wordCmpHOL, comparison]
  have overflow : ¬ source.stackSpace < count := Nat.not_lt.mpr available
  cases jump <;> simp [singleStackAlloc, StackSemEvaluate.evaluate_seq,
    StackSemEvaluate.evaluate_inst, StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp, pointerLookup, wordOpHOL, wordOp,
    StackSemControl.fixClock, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    StackSemEvaluate.evaluate_ite, StackSemEvaluate.evaluate_jumpLower, StackSemEvaluate.evaluate_skip,
    StackSemStateOps.getVar, StackSemStateOps.getVarImm, Compiler.Encoders.Asm.HolRegImm.toWordRegImm,
    wordSemWordCmp, baseLookup, guard, overflow]
set_option maxRecDepth 2048 in
/-- Source-local strong-induction execution contract for the native recursive builder.
No standalone HOL declaration; this factors the original allocation proof. -/
theorem runAlloc {width : Nat} [NeZero width] {C F : Type}
    (count : Nat) (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target) :
    ∃ clock postTarget,
      StackSemEvaluate.evaluate (stackAlloc jump pointer count, {target with clock := clock + target.clock}) =
        ((if source.stackSpace < count then some (.halt (.word 2)) else none), postTarget) ∧
      (if source.stackSpace < count then postTarget.ffi = source.ffi
       else stateRelHOL jump bounds pointer {source with stackSpace := source.stackSpace - count} postTarget) := by
  classical
  induction count using Nat.strongRecOn generalizing source target with
  | ind count ih =>
    by_cases zero : count = 0
    · subst count
      exact ⟨0, target, by simp [stackAlloc, StackSemEvaluate.evaluate_skip], by simpa using relation⟩
    by_cases small : count ≤ maxStackAlloc
    · let expectedSource := if source.stackSpace < count then StackSemStateOps.emptyEnv source
        else {source with stackSpace := source.stackSpace - count}
      obtain ⟨clock, postTarget, run, post⟩ := evaluateSingleStackAlloc jump bounds pointer count
        source target expectedSource (if source.stackSpace < count then some (.halt (.word 2)) else none)
        ⟨relation, by dsimp [expectedSource]; split <;> rfl, zero, small⟩
      refine ⟨clock, postTarget, ?_, ?_⟩
      · rw [stackAlloc, if_neg zero, if_pos small]
        simpa only [Nat.add_comm] using run
      · by_cases overflow : source.stackSpace < count
        · simpa [overflow, expectedSource, StackSemStateOps.emptyEnv] using post
        · simpa [overflow, expectedSource] using post
    by_cases firstOverflow : source.stackSpace < maxStackAlloc
    · have overflow : source.stackSpace < count := by omega
      obtain ⟨clock, postTarget, run, post⟩ := evaluateSingleStackAlloc jump bounds pointer maxStackAlloc
        source target (StackSemStateOps.emptyEnv source) (some (.halt (.word 2)))
        ⟨relation, by rw [if_pos firstOverflow], by decide, Nat.le_refl _⟩
      have firstRun : StackSemEvaluate.evaluate (singleStackAlloc jump pointer maxStackAlloc,
          {target with clock := clock + target.clock}) = (some (.halt (.word 2)),postTarget) := by
        simpa only [Nat.add_comm] using run
      refine ⟨clock, (StackSemControl.fixClock {target with clock := clock + target.clock}
        ((some (.halt (.word 2)) : Option (StackSemResult width)), postTarget)).2, ?_, ?_⟩
      · rw [stackAlloc, if_neg zero, if_neg small, StackSemEvaluate.evaluate_seq, firstRun]
        simp [StackSemControl.fixClock, overflow]
      · simpa [overflow, firstOverflow, StackSemControl.fixClock, StackSemStateOps.emptyEnv] using post
    · have available : maxStackAlloc ≤ source.stackSpace := Nat.le_of_not_gt firstOverflow
      let nextSource := {source with stackSpace := source.stackSpace - maxStackAlloc}
      let nextTarget := StackSemStateOps.setVar pointer
        (.word ((match target.regs.lookup pointer with | some (.word word) => word | _ => 0) - wordOffset maxStackAlloc)) target
      have nextRelation : stateRelHOL jump bounds pointer nextSource nextTarget :=
        stateRelAllocStep jump bounds pointer maxStackAlloc source target relation available
      obtain ⟨clock, postTarget, run, post⟩ := ih (count - maxStackAlloc)
        (by simp only [maxStackAlloc] at *; omega) nextSource nextTarget nextRelation
      have overflowEq : nextSource.stackSpace < count - maxStackAlloc ↔ source.stackSpace < count := by
        dsimp [nextSource]; omega
      have subtractionEq : (source.stackSpace - maxStackAlloc) - (count - maxStackAlloc) = source.stackSpace - count := by omega
      refine ⟨clock, postTarget, ?_, ?_⟩
      · rw [stackAlloc, if_neg zero, if_neg small, StackSemEvaluate.evaluate_seq]
        have firstRun := runSingleAvailable jump bounds pointer maxStackAlloc (clock + target.clock)
          source target relation available (Nat.le_refl _)
        have presented : StackSemEvaluate.evaluate (singleStackAlloc jump pointer maxStackAlloc,
          {target with clock := clock + target.clock}) = (none, {nextTarget with clock := clock + nextTarget.clock}) := by
          simpa only [nextTarget, StackSemStateOps.setVar] using firstRun
        rw [presented]
        have clamp : StackSemControl.fixClock {target with clock := clock + target.clock}
            ((none : Option (StackSemResult width)), {nextTarget with clock := clock + nextTarget.clock}) =
            (none, {nextTarget with clock := clock + nextTarget.clock}) := by
          simp [StackSemControl.fixClock, nextTarget, StackSemStateOps.setVar]
        rw [clamp]
        simpa only [overflowEq] using run
      · simpa only [overflowEq, nextSource, subtractionEq] using post
attribute [local instance] Classical.propDecidable
/-- Full original arbitrary-count stack allocation simulation, including both
native overflow modes and the original universally quantified non-Halt branch. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateStackAlloc {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.stackAlloc count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target) :
    ∃ clock postTarget,
      StackSemEvaluate.evaluate (stackAlloc jump pointer count,
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (if ∀ word, result ≠ some (.halt word) then
        stateRelHOL jump bounds pointer postSource postTarget else postTarget.ffi = postSource.ffi) := by
  classical
  rcases hypothesis with ⟨sourceRun, _notError, relation⟩
  rw [StackSemEvaluate.evaluate_stackAlloc] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  obtain ⟨clock, postTarget, targetRun, post⟩ := runAlloc count jump bounds pointer source target relation
  by_cases overflow : source.stackSpace < count
  · rw [if_pos overflow] at sourceRun targetRun post
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨clock, postTarget, targetRun, ?_⟩
    simpa [StackSemStateOps.emptyEnv] using post
  · rw [if_neg overflow] at sourceRun targetRun post
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    exact ⟨clock, postTarget, targetRun, by simpa [relation.1] using post⟩
end Flapjack.Compiler.Backend.StackRemove.StackAllocSimulation
