import Mathlib.Tactic.Convert
import Flapjack.Compiler.Backend.StackRemove.Proofs.MemoryReads
import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListExists
import Flapjack.Compiler.Backend.StackRemove.Proofs.StackHeap
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Atoms

namespace Flapjack.Compiler.Backend.StackRemove.CompCorrect.DataBufferWrite
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

/-- Flapjack infrastructure for the original DataBufferWrite case: a nonempty
remaining buffer segment exposes the next target-memory cell. This is derived
from the full separated state relation, without a target-domain premise. The
case proof must derive nonempty space from the successful source buffer write. -/
theorem nextBufferCell {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) (count : Nat)
    (relation : stateRelHOL jump bounds pointer source target)
    (space : source.dataBuffer.spaceLeft = count + 1) :
    let bitmapBase := theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric)
      <<< wordShiftAmount width
    let address := bitmapBase + bytesInWord width *
      BitVec.ofNat width (source.bitmaps ++ source.dataBuffer.buffer).length
    target.mdomain address = true := by
  let next := (theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric)
    <<< wordShiftAmount width) + bytesInWord width *
    BitVec.ofNat width (source.bitmaps ++ source.dataBuffer.buffer).length
  have heaps := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  dsimp only at heaps ⊢
  cases baseLookup : target.regs.lookup (pointer + 1) with
  | none => simp only [baseLookup] at heaps; exact heaps.2.elim
  | some value =>
    cases value with
    | loc block offset => simp only [baseLookup] at heaps; exact heaps.2.elim
    | word base =>
      simp only [baseLookup] at heaps
      rcases heaps.2.2.2.2 with ⟨heap4, heapStack, split4, assertion4, _⟩
      rcases assertion4 with ⟨heap3, heapStore, split3, assertion3, _⟩
      rcases assertion3 with ⟨heap2, heapSpace, split2, _, spaceHeap⟩
      rw [space, (WordListExists.wordListExistsThm _ count).2] at spaceHeap
      rcases spaceHeap with ⟨oldValue, head, tail, splitHead, singleton, _⟩
      have memberHead : head (next, oldValue) := by rw [singleton]
      have memberSpace : heapSpace (next, oldValue) := by
        rw [← splitHead.1]; exact Or.inl memberHead
      have member3 : heap3 (next, oldValue) := by
        rw [← split2.1]; exact Or.inr memberSpace
      have member4 : heap4 (next, oldValue) := by
        rw [← split3.1]; exact Or.inl member3
      have memberTarget : SetSep.fun2Set (target.memory, fun a => target.mdomain a = true)
          (next, oldValue) := by
        rw [← split4.1]; exact Or.inl member4
      exact ((SetSep.fun2SetThm _ _ _ _).mp memberTarget).2

/-- Flapjack case infrastructure: the actual successful native buffer write
supplies both the address and available-space facts needed for target membership.
No target-domain or separately supplied successful guard is assumed. -/
theorem bufferWriteTargetDomain {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (address value : BitVec width) (updated : WordSemBuffer width width)
    (relation : stateRelHOL jump bounds pointer source target)
    (written : wordSemBufferWrite source.dataBuffer address value = some updated) :
    target.mdomain address = true := by
  unfold wordSemBufferWrite at written
  split at written
  next guard =>
    have positive := guard.2
    have space : source.dataBuffer.spaceLeft = (source.dataBuffer.spaceLeft - 1) + 1 := by omega
    have member := nextBufferCell jump bounds pointer source target
      (source.dataBuffer.spaceLeft - 1) relation space
    have heaps := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    dsimp only at heaps member
    rw [← guard.1, heaps.1]
    simpa only [List.length_append, BitVec.ofNat_add, BitVec.mul_add,
      BitVec.add_assoc, bytesInWord] using member
  next => simp at written

/-- Native target store execution derived from source operands and actual
buffer-write success. This supports the full case; it assumes no target run. -/
theorem bufferWriteTargetExecution {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer first second : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (address value : BitVec width) (updated : WordSemBuffer width width)
    (relation : stateRelHOL jump bounds pointer source target)
    (firstBound : first < pointer) (secondBound : second < pointer)
    (firstValue : source.regs.lookup first = some (.word address))
    (secondValue : source.regs.lookup second = some (.word value))
    (written : wordSemBufferWrite source.dataBuffer address value = some updated) :
    StackSemEvaluate.evaluate (.inst (.mem .store second (.addr first 0)), target) =
      (none, {target with memory := fun key =>
        if key = address then .word value else target.memory key}) := by
  have registers := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have firstTarget := (registers first firstBound).trans firstValue
  have secondTarget := (registers second secondBound).trans secondValue
  have domain := bufferWriteTargetDomain jump bounds pointer source target
    address value updated relation written
  simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.wordExp,
    StackSemStateOps.getVar, StackSemStateOps.memStore, firstTarget, secondTarget,
    domain, wordOpHOL, wordOp]

/-- Flapjack factoring of the three original surrounding separation frames.
This changes only association/order of STAR, retaining complete predicate heaps. -/
private theorem exposeBufferCell {α : Type} (preceding suffix outer : (α → Prop) → Prop)
    (entry : α) :
    SetSep.star (SetSep.star preceding (SetSep.star (SetSep.one entry) suffix)) outer =
      SetSep.star (SetSep.one entry) (SetSep.star (SetSep.star preceding suffix) outer) := by
  rw [SetSep.starAssoc preceding (SetSep.one entry) suffix,
    SetSep.starComm preceding (SetSep.one entry),
    ← SetSep.starAssoc (SetSep.one entry) preceding suffix,
    ← SetSep.starAssoc]

/-- Derived buffer-cell update with every surrounding separated heap preserved.
The original graph and singleton partition derive unique-address frame safety;
no post-heap, frame-preservation or target-domain fact is supplied. -/
theorem writeBufferCell {width : Nat} [NeZero width]
    (preceding suffix outer : ((BitVec width × WordLocW width) → Prop) → Prop)
    (address : BitVec width) (oldValue newValue : WordLocW width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Prop)
    (heap : SetSep.star
      (SetSep.star preceding (SetSep.star (SetSep.one (address, oldValue)) suffix)) outer
      (SetSep.fun2Set (memory, domain))) :
    SetSep.star
      (SetSep.star preceding (SetSep.star (SetSep.one (address, newValue)) suffix)) outer
      (SetSep.fun2Set ((fun key => if key = address then newValue else memory key), domain)) := by
  rw [exposeBufferCell] at heap ⊢
  have changed := SetSep.writeFun2Set newValue address oldValue
    (SetSep.star (SetSep.star preceding suffix) outer) memory domain heap
  rw [SetSep.starComm] at changed
  convert changed using 1
  congr 2
  funext key
  by_cases same : key = address <;> simp [same]

/-- Exact append/remaining-slot reassociation for the native buffer segment.
Flapjack infrastructure; addresses use modular word arithmetic throughout. -/
theorem bufferListSlot {width : Nat} [NeZero width]
    (base : BitVec width) (values : List (WordLocW width))
    (value : WordLocW width) (count : Nat) :
    SetSep.star (Misc.wordList base (values ++ [value]))
      (Misc.wordListExists
        (base + bytesInWord width * BitVec.ofNat width (values.length + 1)) count) =
    SetSep.star (Misc.wordList base values)
      (SetSep.star (SetSep.one
        (base + bytesInWord width * BitVec.ofNat width values.length, value))
        (Misc.wordListExists
          (base + bytesInWord width * BitVec.ofNat width values.length + bytesInWord width) count)) := by
  rw [StackHeap.wordListAppend values [value] base]
  simp only [Misc.wordList]
  rw [SetSep.starComm (SetSep.one _) SetSep.emp, StackHeap.starEmptyLeft,
    ← SetSep.starAssoc]
  congr 2
  congr 1
  simp [BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]

/-- Native buffer append consumes exactly one existential remaining cell while
preserving its full outer frame. Neither the new heap nor memory-domain success
is a premise: the old separated functional graph supplies them. -/
theorem appendBufferCell {width : Nat} [NeZero width]
    (base : BitVec width) (values : List (WordLocW width))
    (value : WordLocW width) (count : Nat)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Prop)
    (heap : SetSep.star
      (SetSep.star (Misc.wordList base values)
        (Misc.wordListExists (base + bytesInWord width * BitVec.ofNat width values.length) (count + 1)))
      frame (SetSep.fun2Set (memory, domain))) :
    SetSep.star
      (SetSep.star (Misc.wordList base (values ++ [value]))
        (Misc.wordListExists (base + bytesInWord width * BitVec.ofNat width (values.length + 1)) count))
      frame (SetSep.fun2Set
        ((fun key => if key = base + bytesInWord width * BitVec.ofNat width values.length
          then value else memory key), domain)) := by
  rw [bufferListSlot]
  rw [(WordListExists.wordListExistsThm _ count).2] at heap
  rcases heap with ⟨front, back, partition, listHeap, frameHeap⟩
  rcases listHeap with ⟨stored, remaining, splitList, storedHeap, old, oldHeap⟩
  exact writeBufferCell _ _ frame _ old value memory domain
    ⟨front, back, partition, ⟨stored, remaining, splitList, storedHeap, oldHeap⟩, frameHeap⟩

/-- Reassociate the original memory, store and stack frames around the buffer
segment. This is separation-algebra infrastructure, with no HOL port claim. -/
private theorem bufferFrames {α : Type}
    (memory buffer remaining store stack : (α → Prop) → Prop) :
    SetSep.star (SetSep.star (SetSep.star (SetSep.star memory buffer) remaining) store) stack =
      SetSep.star (SetSep.star buffer remaining)
        (SetSep.star memory (SetSep.star store stack)) := by
  rw [← SetSep.starAssoc (SetSep.star (SetSep.star memory buffer) remaining) store stack,
    ← SetSep.starAssoc memory buffer remaining,
    SetSep.starComm memory (SetSep.star buffer remaining),
    ← SetSep.starAssoc]

/-- Successful native buffer writes preserve the full source/target relation.
The old separated heap supplies the target update and every frame. -/
theorem bufferWriteStateRel {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (address value : BitVec width) (updated : WordSemBuffer width width)
    (relation : stateRelHOL jump bounds pointer source target)
    (written : wordSemBufferWrite source.dataBuffer address value = some updated) :
    stateRelHOL jump bounds pointer {source with dataBuffer := updated}
      {target with memory := fun key => if key = address then .word value else target.memory key} := by
  unfold wordSemBufferWrite at written
  split at written
  next guard =>
    have updatedEq := Option.some.inj written
    subst updated
    unfold stateRelHOL at relation ⊢
    rcases relation with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, heaps⟩
    refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, ?_⟩
    dsimp only at heaps ⊢
    refine ⟨heaps.1, ?_⟩
    cases lookup : target.regs.lookup (pointer + 1) with
    | none => simp only [lookup] at heaps; exact heaps.2.elim
    | some entry =>
      cases entry with
      | loc block offset => simp only [lookup] at heaps; exact heaps.2.elim
      | word base =>
        simp only [lookup] at heaps ⊢
        refine ⟨heaps.2.1, heaps.2.2.1, heaps.2.2.2.1, ?_⟩
        have heap := heaps.2.2.2.2
        rw [bufferFrames] at heap ⊢
        have space : source.dataBuffer.spaceLeft = (source.dataBuffer.spaceLeft - 1) + 1 := by
          have positive := guard.2
          omega
        rw [space] at heap
        have changed := appendBufferCell
          (theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric) <<< wordShiftAmount width)
          ((source.bitmaps ++ source.dataBuffer.buffer).map WordLocW.word) (.word value) (source.dataBuffer.spaceLeft - 1)
          _ target.memory (fun key => target.mdomain key = true) (by simpa only [List.length_map] using heap)
        have addressEq : address =
            (theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric)
              <<< wordShiftAmount width) + bytesInWord width *
                BitVec.ofNat width (source.bitmaps ++ source.dataBuffer.buffer).length := by
          rw [← guard.1, heaps.1]
          simp [List.length_append, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc, bytesInWord]
        rw [addressEq]
        simpa only [List.append_assoc, List.map_append, List.map_cons, List.map_nil,
          List.length_append, List.length_cons, List.length_nil, List.length_map,
          Nat.add_assoc, Nat.add_zero] using changed
  next => simp at written

/-- Canonical imported-state codec witness; Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full native DataBufferWrite case of the original simulation statement.
Only original evaluation, non-error, full state relation and register bounds
are premises; the target store and complete postrelation are derived. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectDataBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (first second : Nat)
    (hypothesis : StackSemEvaluate.evaluate (.dataBufferWrite first second, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.dataBufferWrite first second : HolProg width) pointer) :
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.dataBufferWrite first second),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have useStack := relation.1
  rw [StackSemEvaluate.evaluate_dataBufferWrite] at sourceRun
  simp only [useStack, not_true_eq_false, ite_false] at sourceRun
  cases firstLookup : StackSemStateOps.getVar first source with
  | none =>
    simp only [firstLookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some firstValue =>
    cases firstValue with
    | loc block offset =>
      simp only [firstLookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | word address =>
      cases secondLookup : StackSemStateOps.getVar second source with
      | none =>
        simp only [firstLookup, secondLookup] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
      | some secondValue =>
        cases secondValue with
        | loc block offset =>
          simp only [firstLookup, secondLookup] at sourceRun
          exact (notError (Prod.mk.inj sourceRun).1.symm).elim
        | word value =>
          simp only [firstLookup, secondLookup] at sourceRun
          cases written : wordSemBufferWrite source.dataBuffer address value with
          | none =>
            rw [written] at sourceRun
            exact (notError (Prod.mk.inj sourceRun).1.symm).elim
          | some updated =>
            rw [written] at sourceRun
            rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
            subst result
            subst postSource
            refine ⟨0, {target with memory := fun key => if key = address then .word value else target.memory key}, ?_, ?_⟩
            · simpa only [comp, Nat.zero_add] using
                bufferWriteTargetExecution jump bounds pointer first second source target address value updated
                  relation bound.1 bound.2 firstLookup secondLookup written
            · simpa only [useStack] using bufferWriteStateRel jump bounds pointer source target address value updated relation written

end Flapjack.Compiler.Backend.StackRemove.CompCorrect.DataBufferWrite
