import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Compiler.Backend.StackRemove
import Flapjack.Misc.Alignment
import Flapjack.Misc.GoodDimindex
import Flapjack.Misc.WordList

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodePre
open Flapjack

/-- Canonical imported state roundtrip for the actual initializer carrier.
This is representation infrastructure, not a premise of the precondition. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Full original initializer precondition. All four existential word pointers,
the original dimension/register/code/FFI-save guards, every header load,
unsigned capacity comparisons, alignments and the complete separated heap
assertion are retained. Memory and save-register domains are the native Bool
characteristic functions, used through their original membership predicates.
The left association of the three heap factors is the original STAR syntax.
No successful execution, initialized output or state relation is assumed. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "init_code_pre_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def initCodePre {width : Nat} [NeZero width] {C F : Type}
    (pointer : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∃ ptr2 ptr3 ptr4 bitmapPointer : BitVec width,
    goodDimindex width ∧ 8 ≤ pointer ∧ sptDomain source.code 1 ∧
    (∀ register, register = pointer ∨ register = pointer + 1 ∨ register = pointer + 2 →
      source.ffiSaveRegs register = true) ∧
    source.useStack = false ∧ source.useStore = false ∧ source.useAlloc = false ∧
    source.regs.lookup 2 = some (.word ptr2) ∧
    source.regs.lookup 3 = some (.word ptr3) ∧
    source.regs.lookup 4 = some (.word ptr4) ∧
    source.memory ptr2 = .word bitmapPointer ∧
    source.memory (ptr2 + bytesInWord width) =
      .word (bitmapPointer + bytesInWord width * BitVec.ofNat width bitmaps.length) ∧
    source.memory (ptr2 + 2 * bytesInWord width) =
      .word (bitmapPointer + bytesInWord width * BitVec.ofNat width bitmaps.length +
        bytesInWord width * BitVec.ofNat width dataSpace) ∧
    source.memory (ptr2 + 3 * bytesInWord width) = .word source.codeBuffer.position ∧
    source.memory (ptr2 + 4 * bytesInWord width) =
      .word (source.codeBuffer.position + BitVec.ofNat width source.codeBuffer.spaceLeft) ∧
    ptr2.toNat ≤ ptr4.toNat ∧
    (1024 * bytesInWord width).toNat ≤ (ptr4 - ptr2).toNat ∧
    holByteAligned ptr2 = true ∧ holByteAligned ptr4 = true ∧
    holByteAligned bitmapPointer = true ∧
    source.codeBuffer.buffer = [] ∧
    SetSep.star
      (SetSep.star
        (Misc.wordList bitmapPointer (bitmaps.map WordLocW.word))
        (Misc.wordListExists
          (bitmapPointer + bytesInWord width * BitVec.ofNat width bitmaps.length) dataSpace))
      (Misc.wordListExists ptr2 ((ptr4 - ptr2).toNat / (bytesInWord width).toNat))
      (SetSep.fun2Set (source.memory, fun address => source.mdomain address = true))

end Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodePre
