import Flapjack.Compiler.Backend.LabLang
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Compiler.Backend.Semantics.WordSem.State

/-!
Faithful carriers for `labSemScript.sml:10-44`. The source state has 23 fields.
Registers and memory are total functions, domains are sets, and code is a list
of sections. None of these fields is a HOL finite map. Compiler configuration
and the FFI host state remain independent universe-zero type parameters.
This module supplies carriers, not the still-missing evaluator or its simulation.
-/

namespace Flapjack.Compiler.Backend.LabSem

open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm

/-- Exact fixed-byte/location sum from HOL; the three LocByte payloads are
natural numbers, not word-sized offsets. -/
@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "word8_loc"]
inductive Word8Loc where
  | byte (value : BitVec 8)
  | locByte (sectionId labelId byteIndex : Nat)
  deriving DecidableEq, Repr

/-- Flapjack-specific instantiation of the imported constructor-for-constructor
LabLang syntax at HOL's actual ASM, register-immediate, mlstring and word
carriers. These aliases have no independent HOL declarations. -/
abbrev LabLineHOL (width : Nat) [NeZero width] :=
  Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
    (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
    (BitVec width)

/-- Concrete section instantiation, with the original list of lines. -/
abbrev LabSectionHOL (width : Nat) [NeZero width] := Section (LabLineHOL width)

/-- Concrete program instantiation, with the original list of sections. -/
abbrev LabProgHOL (width : Nat) [NeZero width] := List (LabSectionHOL width)

/-- All 23 HOL LabSem state fields, in source order. The compile function and
its oracle use the same concrete LabLang program and compiler configuration.
The word-dimension qualifier translates only HOL's type-indexed words; fixed
word8/word64 fields retain their literal dimensions. -/
@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "state"
  (words_as_type_indexed_bitvec)]
structure State (width : Nat) [NeZero width] (C : Type) (F : Type) where
  regs : Nat → WordLocW width
  fpRegs : Nat → BitVec 64
  memory : BitVec width → WordLocW width
  memDomain : BitVec width → Bool
  sharedMemDomain : BitVec width → Bool
  pc : Nat
  be : Bool
  ffi : HolFfiState F
  ioRegs : Nat → HolFfiName → Nat → Option (BitVec width)
  ccRegs : Nat → Nat → Option (BitVec width)
  ioFpRegs : Nat → Nat → BitVec 64
  ccFpRegs : Nat → Nat → BitVec 64
  code : LabProgHOL width
  compile : C → LabProgHOL width → Option (List (BitVec 8) × C)
  compileOracle : Nat → C × LabProgHOL width
  codeBuffer : WordSemBuffer width 8
  clock : Nat
  failed : Bool
  ptrReg : Nat
  lenReg : Nat
  ptr2Reg : Nat
  len2Reg : Nat
  linkReg : Nat

end Flapjack.Compiler.Backend.LabSem
