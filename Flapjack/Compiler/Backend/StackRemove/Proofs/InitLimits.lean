import Flapjack.Compiler.Backend.StackRemove.Proofs.InitLimitsDouble
import Flapjack.Compiler.Backend.BackendCommon
import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
import Flapjack.Misc.Option

/-! Stack/heap limit calculations of `stack_removeProofScript.sml`
(3053-3077). HOL `shift (:α)` is `backend_common$word_shift`
(`wordShiftAmount width`), `<₊`/`≤₊` are unsigned comparisons (Lean's `BitVec`
order), `⋙` is logical right shift and `≪` left shift, both binding tighter
than `+` and associating to the left as in HOL.
-/

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.InitLimits
open Flapjack Flapjack.Compiler.Backend.StackRemove

/-- Complete original word-to-number limit calculation. As in the captured
HOL type `num -> 'b word -> 'c word -> 'a word -> num # num`, the first two
pointers have independent word widths and are only read through `w2n`; the
arithmetic and byte width are those of the last pointer. The heap bound word
is the original guarded product or `-1w`, the third register is rounded down
to a double-word boundary, and the three numeric arguments are the unsigned
values divided by the byte width. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_stack_heap_limit'_def"
  (words_as_type_indexed_bitvec)]
def getStackHeapLimitPrime {width2 : Nat} {width3 : Nat} {width : Nat} [NeZero width2]
    [NeZero width3] [NeZero width] (maxHeap : Nat)
    (p2 : BitVec width2) (p3 : BitVec width3) (p4 : BitVec width) : Nat × Nat :=
  let ptr2 := p2.toNat
  let ptr3 := p3.toNat
  let ptr4 := p4.toNat
  let d := width / 8
  let maxHeapW : BitVec width :=
    if maxHeap * (bytesInWord width).toNat < 2 ^ width then
      bytesInWord width * BitVec.ofNat width maxHeap
    else -1
  let reg3 := BitVec.ofNat width ptr2 +
    (((-1 * BitVec.ofNat width ptr2 +
      if maxHeapW < -1 * BitVec.ofNat width ptr2 + BitVec.ofNat width ptr3 then
        maxHeapW + BitVec.ofNat width ptr2
      else BitVec.ofNat width ptr3) >>> (wordShiftAmount width + 1)) <<<
        (wordShiftAmount width + 1))
  InitLimitsDouble.getStackHeapLimitDouble (ptr2 / d) (reg3.toNat / d) (ptr4 / d)

/-- Complete original limit calculation from the three initial pointers:
the third pointer is used when it lies within the original stack-allocation
margins, and the rounded midpoint otherwise. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_stack_heap_limit_def"
  (words_as_type_indexed_bitvec)]
def getStackHeapLimit {width : Nat} [NeZero width] (maxHeap : Nat)
    (pointers : BitVec width × BitVec width × BitVec width) : Nat × Nat :=
  let ptr2 := pointers.1
  let ptr3 := pointers.2.1
  let ptr4 := pointers.2.2
  let middle := ptr2 +
    (((-1 * ptr2 + ptr4) >>> (wordShiftAmount width + 1)) <<< wordShiftAmount width)
  let adjPtr2 := ptr2 + bytesInWord width * BitVec.ofNat width maxStackAlloc
  let adjPtr4 := ptr4 - bytesInWord width * BitVec.ofNat width maxStackAlloc
  let adjPtr3 := if adjPtr2 ≤ ptr3 ∧ ptr3 ≤ adjPtr4 then ptr3 else middle
  getStackHeapLimitPrime maxHeap ptr2 adjPtr3 ptr4

-- This supplies only HOL type inhabitedness. Missing registers keep the
-- opaque holTheNone value; this instance does not choose it.
local instance {width : Nat} [NeZero width] : Nonempty (WordLocW width) := ⟨.word 0⟩

/-- Canonical roundtrip for the imported actual state carrier; representation
infrastructure rather than an assumption about the pointer registers. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Complete original pointer read: registers 2, 3 and 4 through `FLOOKUP`,
`THE` and `theWord`. An absent register keeps HOL's unspecified `THE NONE`
value and a location keeps the shared `theWord` ARB completion; no register
presence or word-valuedness premise is added. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
noncomputable def readPointers {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) : BitVec width × BitVec width × BitVec width :=
  (wordSemTheWord (holThe (s.regs.lookup 2)),
   wordSemTheWord (holThe (s.regs.lookup 3)),
   wordSemTheWord (holThe (s.regs.lookup 4)))

end Flapjack.Compiler.Backend.StackRemove.Proofs.InitLimits
