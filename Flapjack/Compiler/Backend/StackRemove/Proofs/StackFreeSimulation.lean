import Flapjack.FiniteMap.MapKeys
import Flapjack.Compiler.Backend.StackRemove.Proofs.StackPointer
import Flapjack.Compiler.Backend.StackRemove.Proofs.StateUpdates
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef
import Flapjack.Compiler.Backend.StackRemove.StackFree
namespace Flapjack.Compiler.Backend.StackRemove.StackFreeSimulation
open Flapjack.Compiler.Backend.StackRemove
open Flapjack
/-- Flapjack factoring of the full state relation transition in original
single-stack-free proof. It has no separately named HOL original: the original
proof unfolds the relation directly. The stack safety premise is discharged
from the original theorem; target evaluation is proved separately below. -/
theorem stateRelFreeStep {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target)
    (safe : source.stackSpace + count ≤ source.stack.length) :
    stateRelHOL jump bounds pointer {source with stackSpace := source.stackSpace + count}
      (StackSemStateOps.setVar pointer
        (.word ((match target.regs.lookup pointer with | some (.word value) => value | _ => 0) + wordOffset count)) target) := by
  obtain ⟨base, baseLookup, lower, upper, pointerLookup, heap⟩ :=
    StackPointer.stateRelGetVarK jump bounds pointer source target relation
  change target.regs.lookup (pointer + 1) = some (.word base) at baseLookup
  change target.regs.lookup pointer = some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) at pointerLookup
  have arithmetic : (base + bytesInWord width * BitVec.ofNat width source.stackSpace) + wordOffset count =
      base + bytesInWord width * BitVec.ofNat width (source.stackSpace + count) := by
    simp [wordOffset, bytesInWord, BitVec.ofNat_mul, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
  have baseNe : pointer + 1 ≠ pointer := by omega
  have heapNe : pointer + 2 ≠ pointer := by omega
  simp only [stateRelHOL] at relation
  rcases relation with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩
  have low : ∀ query, query < pointer →
      (target.regs.updateEq (pointer, .word (base + bytesInWord width * BitVec.ofNat width (source.stackSpace + count)))).lookup query = source.regs.lookup query := by
    intro query below
    have ne : query ≠ pointer := by omega
    simpa only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne, ite_false] using h18 query below
  simp only [stateRelHOL, StackSemStateOps.setVar, pointerLookup, arithmetic,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, baseNe, heapNe, ite_false, ite_true, baseLookup]
  exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,low,h19,h20,h21,h22,h23,safe,
    h25.1,lower,upper,True.intro,heap⟩
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original single_stack_free simulation with exactly its original
relation, output-state, stack-safety, nonzero and chunk-bound conjuncts. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateSingleStackFree {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      (result, postSource) = (none, {source with stackSpace := source.stackSpace + count}) ∧
      ¬ source.stack.length < source.stackSpace + count ∧ count ≠ 0 ∧ count ≤ maxStackAlloc) :
    ∃ clock postTarget,
      StackSemEvaluate.evaluate (singleStackFree pointer count,
        {target with clock := target.clock + clock}) = (result, postTarget) ∧
      stateRelHOL jump bounds pointer postSource postTarget := by
  rcases hypothesis with ⟨relation, output, safe, _nonzero, _small⟩
  rcases Prod.mk.inj output with ⟨resultEq, stateEq⟩
  subst result
  subst postSource
  obtain ⟨base, _baseLookup, _lower, _upper, pointerLookup, _heap⟩ :=
    StackPointer.stateRelGetVarK jump bounds pointer source target relation
  have lookup : target.regs.lookup pointer =
      some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) := pointerLookup
  refine ⟨0, StackSemStateOps.setVar pointer
    (.word ((base + bytesInWord width * BitVec.ofNat width source.stackSpace) + wordOffset count)) target, ?_, ?_⟩
  · simp [singleStackFree, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
      StackSemExpressions.wordExp, lookup,
      wordOpHOL, wordOp]
  · simpa only [lookup] using stateRelFreeStep jump bounds pointer count source target
      relation (Nat.le_of_not_gt safe)
/-- Flapjack-specific native execution/update factoring for the original
recursive StackFree proof; no independently named HOL declaration is claimed. -/
theorem setVarExisting {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (register : Nat) (value : WordLocW width)
    (lookup : state.regs.lookup register = some value) :
    StackSemStateOps.setVar register value state = state := by
  have maps : state.regs.updateEq (register,value) = state.regs := by
    apply HolFiniteMapExact.ext_lookup
    intro query
    by_cases same : query = register
    · subst query; simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, lookup]
    · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same]
  simp [StackSemStateOps.setVar, maps]
/-- Flapjack-specific native execution/update factoring for the original
recursive StackFree proof; no independently named HOL declaration is claimed. -/
theorem setVarTwice {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (register : Nat) (first second : WordLocW width) :
    StackSemStateOps.setVar register second (StackSemStateOps.setVar register first state) =
      StackSemStateOps.setVar register second state := by
  have maps : (state.regs.updateEq (register, first)).updateEq (register, second) =
      state.regs.updateEq (register, second) := by
    apply HolFiniteMapExact.ext_lookup
    intro query
    by_cases same : query = register <;> simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same]
  simp [StackSemStateOps.setVar, maps]
/-- Flapjack-specific native execution/update factoring for the original
recursive StackFree proof; no independently named HOL declaration is claimed. -/
theorem runSingle {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (register count : Nat) (value : BitVec width)
    (lookup : state.regs.lookup register = some (.word value)) :
    StackSemEvaluate.evaluate (singleStackFree register count, state) =
      (none, StackSemStateOps.setVar register (.word (value + wordOffset count)) state) := by
  simp [singleStackFree, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, lookup, wordOpHOL, wordOp]
/-- Flapjack-specific native execution/update factoring for the original
recursive StackFree proof; no independently named HOL declaration is claimed. -/
theorem runFree {width : Nat} [NeZero width] {C F : Type}
    (count register : Nat) (state : StackSemStateFiniteExact width C F) (value : BitVec width)
    (lookup : state.regs.lookup register = some (.word value)) :
    StackSemEvaluate.evaluate (stackFree register count, state) =
      (none, StackSemStateOps.setVar register (.word (value + wordOffset count)) state) := by
  induction count using Nat.strongRecOn generalizing state value with
  | ind count ih =>
    rw [stackFree]
    split
    · rename_i zero
      subst count
      simp [StackSemEvaluate.evaluate_skip, wordOffset, setVarExisting state register (.word value) lookup]
    · split
      · exact runSingle state register count value lookup
      · rw [StackSemEvaluate.evaluate_seq, runSingle state register maxStackAlloc value lookup]
        simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
        have nextLookup : (StackSemStateOps.setVar register (.word (value + wordOffset maxStackAlloc)) state).regs.lookup register =
            some (.word (value + wordOffset maxStackAlloc)) := by
          simp [StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
        change StackSemEvaluate.evaluate (stackFree register (count - maxStackAlloc),
          StackSemStateOps.setVar register (.word (value + wordOffset maxStackAlloc)) state) =
          (none, StackSemStateOps.setVar register (.word (value + wordOffset count)) state)
        rw [ih (count - maxStackAlloc) (by simp only [maxStackAlloc] at *; omega) _ _ nextLookup]
        rw [setVarTwice]
        have offsets : (wordOffset maxStackAlloc : BitVec width) + wordOffset (count - maxStackAlloc) = wordOffset count := by
          rw [wordOffset, wordOffset, wordOffset, ← BitVec.ofNat_add]
          have countEq : maxStackAlloc + (count - maxStackAlloc) = count := by omega
          rw [← Nat.mul_add, countEq]
        rw [BitVec.add_assoc, offsets]
/-- Full original arbitrary-count recursive stack_free simulation. Source
non-error establishes stack safety; all generated chunks are executed and the
complete post-state relation is derived. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateStackFree {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.stackFree count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target) :
    ∃ clock postTarget,
      StackSemEvaluate.evaluate (stackFree pointer count,
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      stateRelHOL jump bounds pointer postSource postTarget := by
  rcases hypothesis with ⟨sourceRun, notError, relation⟩
  rw [StackSemEvaluate.evaluate_stackFree] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  by_cases safe : source.stack.length < source.stackSpace + count
  · rw [if_pos safe] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  · rw [if_neg safe] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    obtain ⟨base, _baseLookup, _lower, _upper, pointerLookup, _heap⟩ :=
      StackPointer.stateRelGetVarK jump bounds pointer source target relation
    have lookup : target.regs.lookup pointer =
        some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) := pointerLookup
    refine ⟨0, StackSemStateOps.setVar pointer
      (.word ((base + bytesInWord width * BitVec.ofNat width source.stackSpace) + wordOffset count)) target, ?_, ?_⟩
    · simpa only [Nat.zero_add] using runFree count pointer target _ lookup
    · simpa only [lookup, relation.1] using stateRelFreeStep jump bounds pointer count source target relation (Nat.le_of_not_gt safe)
end Flapjack.Compiler.Backend.StackRemove.StackFreeSimulation
