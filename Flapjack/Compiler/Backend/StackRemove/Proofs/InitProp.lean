import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Compiler.Backend.StackRemove.Proofs.StackHeapLimitOk
import Flapjack.Misc.Alignment
import Flapjack.Misc.ListEl
import Flapjack.Misc.WordList

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.InitProp
open Flapjack

-- Inhabitedness of the original word_loc type, not a chosen undefined value.
-- The shared holLast's independent opaque nil identity is retained.
private instance {width : Nat} [NeZero width] : Nonempty (WordLocW width) :=
  ⟨.word 0⟩

/-- Genuine canonical roundtrip for the imported actual state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Complete original initialized-state predicate. All four witnesses and
32 conjuncts are retained: seventeen store lookups, the pair limit predicate,
empty buffers, exact use flags/register zero, word/natural resource bounds,
heap relation/alignment, symbolic LAST and the two separated heap regions.
No good-dimension, allocation flag, successful run or post-relation is added. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def initProp {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap dataSpace : Nat) (limits : Nat × Nat)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∃ (current other bitmapBase : BitVec width) (length : Nat),
    source.store.lookup .currHeap = some (.word current) ∧
    source.store.lookup .nextFree = some (.word current) ∧
    source.store.lookup .triggerGC = some (.word (if generateGc then current else other)) ∧
    source.store.lookup .endOfHeap = some (.word other) ∧
    source.store.lookup .otherHeap = some (.word other) ∧
    source.store.lookup .bitmapBase = some (.word bitmapBase) ∧
    source.store.lookup .heapLength =
      some (.word (BitVec.ofNat width length * bytesInWord width)) ∧
    source.store.lookup .progStart = some (.word 0) ∧
    source.store.lookup .allocSize = some (.word 0) ∧
    source.store.lookup .globals = some (.word 0) ∧
    source.store.lookup .globReal = some (.word current) ∧
    source.store.lookup .handler = some (.word 0) ∧
    source.store.lookup .genStart = some (.word 0) ∧
    source.store.lookup .codeBuffer = some (.word source.codeBuffer.position) ∧
    source.store.lookup .codeBufferEnd =
      some (.word (source.codeBuffer.position + BitVec.ofNat width source.codeBuffer.spaceLeft)) ∧
    source.store.lookup .bitmapBuffer = some (.word source.dataBuffer.position) ∧
    source.store.lookup .bitmapBufferEnd =
      some (.word (source.dataBuffer.position +
        bytesInWord width * BitVec.ofNat width source.dataBuffer.spaceLeft)) ∧
    StackHeapLimitOk.stackHeapLimitOk source limits ∧
    source.codeBuffer.buffer = [] ∧ source.dataBuffer.buffer = [] ∧
    source.useStack = true ∧ source.useStore = true ∧
    source.regs.lookup 0 = some (.loc 1 0) ∧
    source.bitmaps.length + dataSpace + 1 < 2 ^ width ∧
    source.stack.length < 2 ^ width ∧
    other = current + bytesInWord width * BitVec.ofNat width length ∧
    holByteAligned current = true ∧
    holLast source.stack = .word 0 ∧
    source.stack.length = source.stackSpace + 1 ∧
    source.stack.length * (width / 8) < 2 ^ width ∧
    length + length ≤ maxHeap ∧
    SetSep.star (Misc.wordListExists current length) (Misc.wordListExists other length)
      (SetSep.fun2Set (source.memory, fun address => source.mdomain address = true))

end Flapjack.Compiler.Backend.StackRemove.Proofs.InitProp
