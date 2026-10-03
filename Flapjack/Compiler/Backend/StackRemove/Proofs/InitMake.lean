import Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodePre
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitLimits
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitProp
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitReduce
import Flapjack.Compiler.Backend.StackRemove.Compile
import Flapjack.Compiler.Backend.StackRemove.InitCode
import Flapjack.Compiler.Backend.StackProps.RegisterBounds
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef

/-! Initializer definitions of `stack_removeProofScript.sml` (3839-3854,
4007-4067): the optional and total initialized states, the initializer
precondition, and the two hypothesis bundles of `make_init_semantics`.
-/

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.InitMake
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.StackSemEvaluate

/-- Canonical roundtrip for the imported actual state carrier; representation
infrastructure rather than an assumption about any initializer input. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

open Classical in
/-- Complete original optional initialized state: run the actual initializer
code with the native evaluator; any result is `NONE`, and a normal return
yields the reduced state exactly when the original `init_prop` holds for the
limits read from the input pointers. No successful run is assumed. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "make_init_opt_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
noncomputable def makeInitOpt {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (HolProg width)) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemStateFiniteExact width C F) :=
  match evaluate (initCode generateGc maxHeap pointer, s) with
  | (some _, _) => none
  | (none, t) =>
    if InitProp.initProp generateGc maxHeap dataSpace
        (InitLimits.getStackHeapLimit maxHeap (InitLimits.readPointers s))
        (InitReduce.initReduce generateGc jump bounds pointer code bitmaps dataSpace oracle t)
    then some (InitReduce.initReduce generateGc jump bounds pointer code bitmaps dataSpace
      oracle t)
    else none

/-- Complete original initializer precondition: entry 0 of the code is the
initializer followed by the tail call to `start`, together with the original
`init_code_pre` and the maximum-heap lower bound. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "init_pre_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def initPre {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (pointer start : Nat) (s : StackSemStateFiniteExact width C F) : Prop :=
  sptLookup 0 s.code =
      some (.seq (initCode generateGc maxHeap pointer) (.call none (.inl start) none)) ∧
    InitCodePre.initCodePre pointer bitmaps dataSpace s ∧ maxStackAlloc ≤ maxHeap

/-- Complete original total initialized state: the optional state when
present, and otherwise the literal fallback record update of `s` with all
fifteen original fields, including the zero-word store over
`CurrHeap :: store_list` and the compile callback through `prog_comp`. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "make_init_any_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
noncomputable def makeInitAny {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (HolProg width)) (s : StackSemStateFiniteExact width C F) :
    StackSemStateFiniteExact width C F :=
  match makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code s with
  | some t => t
  | none =>
    { s with
      regs := HolFiniteMapExact.empty.updateEq (0, .loc 1 0)
      fpRegs := HolFiniteMapExact.empty
      mdomain := fun _ => false
      bitmaps := [4]
      useStack := true
      useStore := true
      useAlloc := false
      stack := [.word 0]
      stackSpace := 0
      compile := fun config program => s.compile config (program.map (progComp jump bounds pointer))
      compileOracle := oracle
      dataBuffer := { buffer := [], position := 0, spaceLeft := 0 }
      codeBuffer := { buffer := [], position := 0, spaceLeft := 0 }
      code := code
      store := HolFiniteMapExact.empty.updateListEq
        ((.currHeap :: storeList).map fun name =>
          (StackSemRegisterTransfers.storeOfSyntax name, .word 0)) }

/-- Complete original compiler-side hypothesis bundle of `make_init_semantics`:
register bounds and stub numbering of the source code and every oracle entry,
the literal compile-oracle and code equations, the register base, entry 1,
the FFI save registers, the three disabled flags and the heap lower bound. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "discharge_these_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def dischargeThese {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maxHeap pointer start : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (code : List (Nat × HolProg width)) (s2 : StackSemStateFiniteExact width C F) : Prop :=
  (∀ entry ∈ code, StackProps.regBound entry.2 pointer ∧ stackNumStubs ≤ entry.1 + 1) ∧
    (∀ (n i : Nat) (p : HolProg width), (i, p) ∈ (oracle n).2.1 →
      StackProps.regBound p pointer ∧ stackNumStubs ≤ i + 1) ∧
    s2.compileOracle = (fun index =>
      let entry := oracle index
      (entry.1, entry.2.1.map (progComp jump bounds pointer), entry.2.2)) ∧
    s2.code = sptFromAList (compileHOL jump bounds generateGc maxHeap pointer start code) ∧
    8 ≤ pointer ∧ sptDomain s2.code 1 ∧
    (∀ register, register = pointer ∨ register = pointer + 1 ∨ register = pointer + 2 →
      s2.ffiSaveRegs register = true) ∧
    s2.useStack = false ∧ s2.useStore = false ∧ s2.useAlloc = false ∧
    maxStackAlloc ≤ maxHeap

/-- Complete original machine-side hypothesis bundle of `make_init_semantics`:
good dimension and four existential pointers with every original register,
header-load, buffer, unsigned-order, alignment and separated-heap conjunct.
The heap size uses the original `w2n (-1w * ptr2 + ptr4)`. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "propagate_these_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def propagateThese {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (bitmaps : List (BitVec width))
    (dataSpace : Nat) : Prop :=
  goodDimindex width ∧
  ∃ ptr2 ptr3 ptr4 bitmapPointer : BitVec width,
    s.regs.lookup 2 = some (.word ptr2) ∧
    s.regs.lookup 3 = some (.word ptr3) ∧
    s.regs.lookup 4 = some (.word ptr4) ∧
    s.memory ptr2 = .word bitmapPointer ∧
    s.memory (ptr2 + bytesInWord width) =
      .word (bitmapPointer + bytesInWord width * BitVec.ofNat width bitmaps.length) ∧
    s.memory (ptr2 + 2 * bytesInWord width) =
      .word (bitmapPointer + bytesInWord width * BitVec.ofNat width bitmaps.length +
        bytesInWord width * BitVec.ofNat width dataSpace) ∧
    s.memory (ptr2 + 3 * bytesInWord width) = .word s.codeBuffer.position ∧
    s.memory (ptr2 + 4 * bytesInWord width) =
      .word (s.codeBuffer.position + BitVec.ofNat width s.codeBuffer.spaceLeft) ∧
    s.codeBuffer.buffer = [] ∧
    ptr2.toNat ≤ ptr4.toNat ∧
    holByteAligned ptr2 = true ∧ holByteAligned ptr4 = true ∧
    holByteAligned bitmapPointer = true ∧
    (1024 * bytesInWord width).toNat ≤ (ptr4 - ptr2).toNat ∧
    SetSep.star
      (SetSep.star
        (Misc.wordList bitmapPointer (bitmaps.map WordLocW.word))
        (Misc.wordListExists
          (bitmapPointer + bytesInWord width * BitVec.ofNat width bitmaps.length) dataSpace))
      (Misc.wordListExists ptr2 ((-1 * ptr2 + ptr4).toNat / (bytesInWord width).toNat))
      (SetSep.fun2Set (s.memory, fun address => s.mdomain address = true))

end Flapjack.Compiler.Backend.StackRemove.Proofs.InitMake
