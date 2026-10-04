import Flapjack.Compiler.Backend.LabToTarget.Encoding
import Flapjack.Compiler.Encoders.Asm
import Flapjack.FfiHOL
import Flapjack.Basis.Pure.MlString

/-!
# Faithful Cake shared-memory/FFI name collection (`lab_to_target`)

Exact definitions from `cakeml/compiler/backend/lab_to_targetScript.sml:349-430`.
`shmem_info_num` is the record describing a shared-memory instruction;
`list_add_if_fresh` appends an element only when it is not already present; `find_ffi_names` collects the `ExtCall` names of `CallFFI`
instructions across a program; `get_memop_info` maps each `memop` to its
`shmem_op`/`word8` size pair; and `get_shmem_info` walks a program threading a
byte position and accumulating the `SharedMem` names and `shmem_info_num`
records of `ShareMem` instructions.

HOL `line` and `sec` share a single type-indexed word parameter `'a`, so the
imported LabLang carriers are instantiated at HOL's actual carriers: `HolAsm`,
`HolMemop`, `HolAddr`, `HolCmp`, `HolRegImm` and the opaque `MlString`, with
only HOL's `'a word` translated to the positive-width `BitVec width`.  The
fixed `word8` byte size stays the literal `BitVec 8`.  HOL `LENGTH` is
`.length` and `w2n` is `.toNat`.
-/

namespace Flapjack.Compiler.Backend.LabToTarget

open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack

/-- Exact HOL `lab_to_target$shmem_info_num`
(`lab_to_targetScript.sml:349-357`): the record
`<| entry_pc: num; nbytes: word8; addr_reg: num; addr_off: num; reg: num;
exit_pc: num |>`.  Field order matches HOL; the fixed `word8` byte size is the
literal `BitVec 8`. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "shmem_info_num"]
structure ShmemInfoNum where
  entryPc : Nat
  nbytes : BitVec 8
  addrReg : Nat
  addrOff : Nat
  reg : Nat
  exitPc : Nat
  deriving DecidableEq, Repr

/-- Exact HOL `lab_to_target$list_add_if_fresh_def`
(`lab_to_targetScript.sml:372`): `list_add_if_fresh e [] = [e]` and
`list_add_if_fresh e (f::r) = if e = f then f::r else f::list_add_if_fresh e r`.
The element type is HOL's generic `'a`, so this carries no type-indexed word
and no qualifier; HOL `=` is the standard decidable equality. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "list_add_if_fresh_def"]
def listAddIfFresh {α : Type} [DecidableEq α] (e : α) : List α → List α
  | [] => [e]
  | f :: r => if e = f then f :: r else f :: listAddIfFresh e r

/-- Exact HOL `lab_to_target$find_ffi_names_def`
(`lab_to_targetScript.sml:378`), clause for clause: `[]` is `[]`; a section
with no lines is skipped; a section whose first line is
`LabAsm (CallFFI s) _ _ _` adds `ExtCall s` (when fresh) after the names
found in the remaining lines; every other line is skipped. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def findFfiNames {width : Nat} [NeZero width] :
    List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) → List HolFfiName
  | [] => []
  | ⟨_, []⟩ :: rest => findFfiNames rest
  | ⟨k, x :: xs⟩ :: rest =>
      match x with
      | .labAsm (.callFFI s) _ _ _ =>
          listAddIfFresh (.extCall s) (findFfiNames (⟨k, xs⟩ :: rest))
      | _ => findFfiNames (⟨k, xs⟩ :: rest)

/-- Exact HOL `lab_to_target$get_memop_info_def`
(`lab_to_targetScript.sml:388`): `Load`/`Load32`/`Load16`/`Load8` map to
`MappedRead` with byte sizes `0`/`4`/`2`/`1`, and `Store`/`Store32`/`Store16`/
`Store8` map to `MappedWrite` with the same sizes.  The byte sizes are the
fixed HOL `word8`, so this carries no type-indexed word and no qualifier. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "get_memop_info_def"]
def getMemopInfo : HolMemop → HolShmemOp × BitVec 8
  | .load => (.mappedRead, 0)
  | .load32 => (.mappedRead, 4)
  | .load16 => (.mappedRead, 2)
  | .load8 => (.mappedRead, 1)
  | .store => (.mappedWrite, 0)
  | .store32 => (.mappedWrite, 4)
  | .store16 => (.mappedWrite, 2)
  | .store8 => (.mappedWrite, 1)

/-- Exact HOL `lab_to_target$get_shmem_info_def`
(`lab_to_targetScript.sml:401`), clause for clause.  `[]` returns the threaded
`(ffi_names, shmem_info)`; a section with no lines is skipped; a `Label` is
skipped without advancing `pos`; an `Asm (ShareMem m r ad) bytes _` looks up
`(name, nb) = get_memop_info m`, appends `SharedMem name`, records
`<|entry_pc := pos; nbytes := nb; addr_reg := (case ad of Addr r off => r);
addr_off := (case ad of Addr r off => w2n off); reg := r;
exit_pc := pos + LENGTH bytes|>` and recurses at `pos + LENGTH bytes`; every
other `LabAsm`/`Asm` line recurses at `pos + LENGTH bytes` recording nothing. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def getShmemInfo {width : Nat} [NeZero width]
    (secs : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (pos : Nat) (ffiNames : List HolFfiName) (shmemInfo : List ShmemInfoNum) :
    List HolFfiName × List ShmemInfoNum :=
  match secs with
  | [] => (ffiNames, shmemInfo)
  | ⟨_, []⟩ :: rest => getShmemInfo rest pos ffiNames shmemInfo
  | ⟨k, .label _ _ _ :: xs⟩ :: rest =>
      getShmemInfo (⟨k, xs⟩ :: rest) pos ffiNames shmemInfo
  | ⟨k, .asm (.shareMem m r (.addr base offset)) bytes _ :: xs⟩ :: rest =>
      let (name, nb) := getMemopInfo m
      getShmemInfo (⟨k, xs⟩ :: rest) (pos + bytes.length)
        (ffiNames ++ [.sharedMem name])
        (shmemInfo ++
          [{ entryPc := pos, nbytes := nb, addrReg := base, addrOff := offset.toNat,
             reg := r, exitPc := pos + bytes.length }])
  | ⟨k, .labAsm _ _ bytes _ :: xs⟩ :: rest =>
      getShmemInfo (⟨k, xs⟩ :: rest) (pos + bytes.length) ffiNames shmemInfo
  | ⟨k, .asm _ bytes _ :: xs⟩ :: rest =>
      getShmemInfo (⟨k, xs⟩ :: rest) (pos + bytes.length) ffiNames shmemInfo

end Flapjack.Compiler.Backend.LabToTarget