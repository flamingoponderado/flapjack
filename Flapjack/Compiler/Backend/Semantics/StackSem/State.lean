import Flapjack.Compiler.Backend.Semantics.WordSem.State
import Flapjack.Compiler.Backend.StackLang.Prog

/-!
# Exact StackSem carriers

Counterpart of stackSemScript.sml's `result` and `state` datatypes. The state
has 22 fields in HOL order. Its three `|->` maps use `HolFiniteMapExact`;
`code` remains the reviewed `Spt` num_map, and stack/bitmaps remain lists.
Words, FFI, buffers and the shared GC function use the reviewed WordSem
carriers. `WordStoreHOL` is the same constructor-for-constructor store_name
rendering used by the WordSem GC function, including its fixed five-bit Temp.
The program carrier is StackLang.HolProg, with exact asm payloads and MlString
FFI names. This module supplies no evaluator or executable-path refinement.
-/

namespace Flapjack

/-- Unrestricted-map counterpart used only for the canonical state codec. -/
structure StackSemStateBroad (width : Nat) [NeZero width] (C : Type) (F : Type) where
  regs : Nat → Option (WordLocW width)
  fpRegs : Nat → Option (BitVec 64)
  store : WordStoreHOL → Option (WordLocW width)
  stack : List (WordLocW width)
  stackSpace : Nat
  memory : BitVec width → WordLocW width
  mdomain : BitVec width → Bool
  shMdomain : BitVec width → Bool
  bitmaps : List (BitVec width)
  compile : C → List (Nat × Compiler.Backend.StackLang.HolProg width) →
    Option (List (BitVec 8) × C)
  compileOracle : Nat → C × List (Nat × Compiler.Backend.StackLang.HolProg width) × List (BitVec width)
  codeBuffer : WordSemBuffer width 8
  dataBuffer : WordSemBuffer width width
  gcFun : WordSemGcFun width
  useStack : Bool
  useStore : Bool
  useAlloc : Bool
  clock : Nat
  code : Spt (Compiler.Backend.StackLang.HolProg width)
  ffi : HolFfiState F
  ffiSaveRegs : Nat → Bool
  be : Bool

/-- Flapjack-specific finite-support predicate for the three broad maps. -/
def StackSemStateBroad.FiniteSupport {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateBroad width C F) : Prop :=
  (∃ keys : List Nat, ∀ key, state.regs key ≠ none → key ∈ keys) ∧
  (∃ keys : List Nat, ∀ key, state.fpRegs key ≠ none → key ∈ keys) ∧
  (∃ keys : List WordStoreHOL, ∀ key, state.store key ≠ none → key ∈ keys)

/-- Exact HOL stackSem state, preserving all 22 source fields. The only
    finite-map fields translated here are regs/fp_regs/store; code is Spt,
    and ffi_save_regs is a set, not a finite-map field. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
structure StackSemStateFiniteExact (width : Nat) [NeZero width] (C : Type) (F : Type) where
  regs : HolFiniteMapExact Nat (WordLocW width)
  fpRegs : HolFiniteMapExact Nat (BitVec 64)
  store : HolFiniteMapExact WordStoreHOL (WordLocW width)
  stack : List (WordLocW width)
  stackSpace : Nat
  memory : BitVec width → WordLocW width
  mdomain : BitVec width → Bool
  shMdomain : BitVec width → Bool
  bitmaps : List (BitVec width)
  compile : C → List (Nat × Compiler.Backend.StackLang.HolProg width) →
    Option (List (BitVec 8) × C)
  compileOracle : Nat → C × List (Nat × Compiler.Backend.StackLang.HolProg width) × List (BitVec width)
  codeBuffer : WordSemBuffer width 8
  dataBuffer : WordSemBuffer width width
  gcFun : WordSemGcFun width
  useStack : Bool
  useStore : Bool
  useAlloc : Bool
  clock : Nat
  code : Spt (Compiler.Backend.StackLang.HolProg width)
  ffi : HolFfiState F
  ffiSaveRegs : Nat → Bool
  be : Bool

/-- Flapjack-specific projection to raw lookup functions, preserving all other fields. -/
def StackSemStateFiniteExact.toBroad {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) : StackSemStateBroad width C F where
  regs := s.regs.lookup
  fpRegs := s.fpRegs.lookup
  store := s.store.lookup
  stack := s.stack
  stackSpace := s.stackSpace
  memory := s.memory
  mdomain := s.mdomain
  shMdomain := s.shMdomain
  bitmaps := s.bitmaps
  compile := s.compile
  compileOracle := s.compileOracle
  codeBuffer := s.codeBuffer
  dataBuffer := s.dataBuffer
  gcFun := s.gcFun
  useStack := s.useStack
  useStore := s.useStore
  useAlloc := s.useAlloc
  clock := s.clock
  code := s.code
  ffi := s.ffi
  ffiSaveRegs := s.ffiSaveRegs
  be := s.be

/-- Flapjack-specific proof that projection lies in the HOL-image subcarrier. -/
theorem StackSemStateFiniteExact.toBroad_finiteSupport {width : Nat} [NeZero width]
    {C F : Type} (s : StackSemStateFiniteExact width C F) : s.toBroad.FiniteSupport :=
  ⟨s.regs.finiteSupport, s.fpRegs.finiteSupport, s.store.finiteSupport⟩

/-- Flapjack-specific reconstruction from a finite-support broad state. -/
def StackSemStateBroad.ofBroad {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateBroad width C F) (h : s.FiniteSupport) :
    StackSemStateFiniteExact width C F where
  regs := { lookup := s.regs, finiteSupport := h.1 }
  fpRegs := { lookup := s.fpRegs, finiteSupport := h.2.1 }
  store := { lookup := s.store, finiteSupport := h.2.2 }
  stack := s.stack
  stackSpace := s.stackSpace
  memory := s.memory
  mdomain := s.mdomain
  shMdomain := s.shMdomain
  bitmaps := s.bitmaps
  compile := s.compile
  compileOracle := s.compileOracle
  codeBuffer := s.codeBuffer
  dataBuffer := s.dataBuffer
  gcFun := s.gcFun
  useStack := s.useStack
  useStore := s.useStore
  useAlloc := s.useAlloc
  clock := s.clock
  code := s.code
  ffi := s.ffi
  ffiSaveRegs := s.ffiSaveRegs
  be := s.be

namespace StackSemStateSupport

/-- Non-vacuous canonical finite-map codec witness for the owning state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  ⟨fun _ _ => rfl, fun state => by cases state; rfl⟩

end StackSemStateSupport

/-- Exact HOL stackSem result: eight constructors with their source payloads. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "result"
  (words_as_type_indexed_bitvec)]
inductive StackSemResult (width : Nat) [NeZero width] where
  | result (value : WordLocW width)
  | exception (value : WordLocW width)
  | break (label : Nat)
  | continue (label : Nat)
  | halt (value : WordLocW width)
  | timeOut
  | finalFFI (event : HolFinalEvent)
  | error

end Flapjack
