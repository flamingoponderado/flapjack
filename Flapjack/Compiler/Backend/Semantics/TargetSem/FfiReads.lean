import Flapjack.Compiler.Backend.Semantics.TargetSem.Machine
import Flapjack.Pancake.Semantics.LoopSem

/-
Counterpart of `cakeml/compiler/backend/semantics/targetSemScript.sml` FFI read
prerequisites.  These are the exact `read_ffi_bytearray_def` and
`read_ffi_bytearrays_def` definitions used by `start_pc_ok` /
`ffi_interfer_ok`.
-/

namespace Flapjack

open Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `read_ffi_bytearray_def`
    (`cakeml/compiler/backend/semantics/targetSemScript.sml:60-68`): read
    `w2n (target.get_reg ms len_reg)` bytes from `target.get_reg ms ptr_reg`,
    restricted to the program addresses.  HOL `'a word` renders as
    `BitVec width` and `word8` as `BitVec 8`, so the words qualifier applies. -/
@[hol "cakeml/compiler/backend/semantics/targetSemScript.sml" "read_ffi_bytearray_def"
  (words_as_type_indexed_bitvec)]
noncomputable def readFfiBytearrayHOL {width : Nat} [NeZero width]
    {state projection : Type}
    (mc : MachineConfig width state projection) (ptrReg lenReg : Nat) (ms : state) :
    Option (List (BitVec 8)) :=
  open Classical in
  readBytearrayWordHOL (byteWidth := 8) (mc.target.getReg ms ptrReg)
    (mc.target.getReg ms lenReg).toNat
    (fun address =>
      if mc.progAddresses address then some (mc.target.getByte ms address) else none)

/-- Exact HOL `read_ffi_bytearrays_def`
    (`cakeml/compiler/backend/semantics/targetSemScript.sml:70-74`): the pair of
    the first and second FFI read. -/
@[hol "cakeml/compiler/backend/semantics/targetSemScript.sml" "read_ffi_bytearrays_def"
  (words_as_type_indexed_bitvec)]
noncomputable def readFfiBytearraysHOL {width : Nat} [NeZero width]
    {state projection : Type}
    (mc : MachineConfig width state projection) (ms : state) :
    Option (List (BitVec 8)) × Option (List (BitVec 8)) :=
  (readFfiBytearrayHOL mc mc.ptrReg mc.lenReg ms,
    readFfiBytearrayHOL mc mc.ptr2Reg mc.len2Reg ms)

end Flapjack
