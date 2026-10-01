import Flapjack.Compiler.Backend.LabSem.Updates
import Flapjack.Compiler.Backend.Semantics.WordSem

/-! Literal ordinary LabSem memory operations. Full-word Load/Store perform
writes before checking the original alignment and domain assertion, including
Loc payloads. Narrow operations reuse the reviewed WordSem byte/32-bit helpers
and propagate their failures without writes. Ordinary Load16/Store16 always
fail; the shared-memory sixteen-bit operations are a different source path.
The unused original is_Loc declaration classifies semanticPrimitives.v, whose
Loc has Bool/Nat payloads, and is separately tracked; it is not a word_loc
classifier or a prerequisite of any operation below. -/

namespace Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "addr_def"
  (words_as_type_indexed_bitvec)]
def addrValue {width : Nat} [NeZero width] {C F : Type} (address : HolAddr width)
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) : Option (BitVec width) :=
  match address with
  | .addr register offset =>
      match state.regs register with
      | .word value => some (value + offset)
      | .loc _ _ => none

@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "mem_store_def"
  (words_as_type_indexed_bitvec)]
def memStore {width : Nat} [NeZero width] {C F : Type} (register : Nat)
    (address : HolAddr width) (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  match addrValue address state with
  | none => assertState false state
  | some value =>
      assertState (decide (value.toNat % (width / 8) = 0) && state.memDomain value)
        (updMem value (state.regs register) state)

@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "mem_load_def"
  (words_as_type_indexed_bitvec)]
def memLoad {width : Nat} [NeZero width] {C F : Type} (register : Nat)
    (address : HolAddr width) (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  match addrValue address state with
  | none => assertState false state
  | some value =>
      assertState (decide (value.toNat % (width / 8) = 0) && state.memDomain value)
        (updReg register (state.memory value) state)

@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "mem_load32_def"
  (words_as_type_indexed_bitvec)]
def memLoad32 {width : Nat} [NeZero width] {C F : Type} (register : Nat)
    (address : HolAddr width) (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  match addrValue address state with
  | none => assertState false state
  | some value =>
      match Flapjack.memLoad32Exact state.memory state.memDomain state.be value with
      | some word => updReg register (.word (word.setWidth width)) state
      | none => assertState false state

@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "mem_store32_def"
  (words_as_type_indexed_bitvec)]
def memStore32 {width : Nat} [NeZero width] {C F : Type} (register : Nat)
    (address : HolAddr width) (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  match addrValue address state with
  | none => assertState false state
  | some value =>
      match state.regs register with
      | .word word =>
          match Flapjack.memStore32Exact state.memory state.memDomain state.be value (word.setWidth 32) with
          | some memory => { state with memory := memory }
          | none => assertState false state
      | .loc _ _ => assertState false state

@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "mem_load_byte_def"
  (words_as_type_indexed_bitvec)]
def memLoadByte {width : Nat} [NeZero width] {C F : Type} (register : Nat)
    (address : HolAddr width) (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  match addrValue address state with
  | none => assertState false state
  | some value =>
      match Flapjack.memLoadByteAuxExact state.memory state.memDomain state.be value with
      | some byte => updReg register (.word (byte.setWidth width)) state
      | none => assertState false state

@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "mem_store_byte_def"
  (words_as_type_indexed_bitvec)]
def memStoreByte {width : Nat} [NeZero width] {C F : Type} (register : Nat)
    (address : HolAddr width) (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  match addrValue address state with
  | none => assertState false state
  | some value =>
      match state.regs register with
      | .word word =>
          match Flapjack.memStoreByteAuxExact state.memory state.memDomain state.be value (word.setWidth 8) with
          | some memory => { state with memory := memory }
          | none => assertState false state
      | .loc _ _ => assertState false state

@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "mem_op_def"
  (words_as_type_indexed_bitvec)]
def memOp {width : Nat} [NeZero width] {C F : Type} (operator : HolMemop) (register : Nat)
    (address : HolAddr width) (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  match operator with
  | .load => memLoad register address state
  | .store => memStore register address state
  | .load32 => memLoad32 register address state
  | .store32 => memStore32 register address state
  | .load8 => memLoadByte register address state
  | .store8 => memStoreByte register address state
  | .load16 => assertState false state
  | .store16 => assertState false state

end Flapjack.Compiler.Backend.LabSem
