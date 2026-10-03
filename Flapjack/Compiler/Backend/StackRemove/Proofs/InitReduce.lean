import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Compiler.Backend.Semantics.StackSem.RegisterTransfers
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
import Flapjack.Compiler.Backend.StackRemove.ProgComp
import Flapjack.Compiler.Backend.StackRemove.StoreInit
import Flapjack.Misc.FiniteMapApply

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.InitReduce
open Flapjack Flapjack.Compiler.Backend.StackLang

-- This supplies only HOL type inhabitedness. Undefined FAPPLY results remain
-- the opaque holFapplyOutside; this instance does not choose a missing value.
local instance {width : Nat} [NeZero width] : Nonempty (WordLocW width) := ⟨.word 0⟩

/-- Canonical roundtrip for the imported actual state carrier; representation
infrastructure rather than an assumption about the initializer's input. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

open Classical in
/-- Complete original source-state construction after initializer execution.
No register presence, word-valuedness, dimension, alias or successful-run
premise is added. Missing FAPPLY bindings retain the original opaque value;
theWord retains the shared ARB completion on locations. All twelve original
state updates are literal, including the compile callback and plain oracle,
natural heap/stack arithmetic, header buffer and ordered finite-map updates.
The characteristic function for the address set is its exact membership
decision; no pre-existing or finite memory-domain hypothesis is assumed. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "init_reduce_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
noncomputable def initReduce {width : Nat} [NeZero width] {C F : Type}
    (generateGc jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (HolProg width)) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (source : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  let heapPointer := wordSemTheWord (holFapply source.regs (pointer + 2))
  let bitmapPointer := wordSemTheWord (holFapply source.regs 3) <<< wordShiftAmount width
  let stackPointer := wordSemTheWord (holFapply source.regs pointer)
  let basePointer := wordSemTheWord (holFapply source.regs (pointer + 1))
  let heapSpace := (basePointer - heapPointer).toNat / (width / 8) - storeList.length
  let stackSpace := (stackPointer - basePointer).toNat / (width / 8)
  { source with
    useStack := true
    useStore := true
    useAlloc := false
    mdomain := fun address => decide (addresses heapPointer heapSpace address)
    bitmaps := bitmaps
    code := code
    compile := fun config program => source.compile config (program.map (progComp jump bounds pointer))
    compileOracle := oracle
    dataBuffer := { buffer := [], position := bitmapPointer + bytesInWord width * BitVec.ofNat width bitmaps.length, spaceLeft := dataSpace }
    stackSpace := stackSpace
    stack := readMem basePointer source.memory (stackSpace + 1)
    store := HolFiniteMapExact.empty.updateListEq
      ((.currHeap :: storeList).map fun name =>
        match storeInit generateGc pointer name with
        | .inl word => (StackSemRegisterTransfers.storeOfSyntax name, .word word)
        | .inr register =>
          (StackSemRegisterTransfers.storeOfSyntax name, holFapply source.regs register)) }

/-- Full original local stack-space invariant of the actual initializer
state construction. No pointer validity or successful execution is required. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "init_reduce_stack_space"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem initReduceStackSpace {width : Nat} [NeZero width] {C F : Type}
    (generateGc jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (HolProg width)) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (source : StackSemStateFiniteExact width C F) :
    (initReduce generateGc jump bounds pointer code bitmaps dataSpace oracle source).stackSpace ≤
      (initReduce generateGc jump bounds pointer code bitmaps dataSpace oracle source).stack.length := by
  simp [initReduce, length_readMem]

end Flapjack.Compiler.Backend.StackRemove.Proofs.InitReduce
