import Flapjack.Compiler.Backend.LabSem.State

/-! Literal shared state primitives of `labSemScript.sml`. Registers and
memory remain total functions; failure is sticky and does not undo updates.
-/

namespace Flapjack.Compiler.Backend.LabSem

open Flapjack.Compiler.Encoders.Asm

@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "upd_pc_def"
  (words_as_type_indexed_bitvec)]
def updPc {width : Nat} [NeZero width] {C F : Type} (pc : Nat)
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  { state with pc := pc }

@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "upd_reg_def"
  (words_as_type_indexed_bitvec)]
def updReg {width : Nat} [NeZero width] {C F : Type} (register : Nat)
    (value : WordLocW width) (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  { state with regs := fun key => if key = register then value else state.regs key }

@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "upd_mem_def"
  (words_as_type_indexed_bitvec)]
def updMem {width : Nat} [NeZero width] {C F : Type} (address : BitVec width)
    (value : WordLocW width) (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  { state with memory := fun key => if key = address then value else state.memory key }

@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "assert_def"
  (words_as_type_indexed_bitvec)]
def assertState {width : Nat} [NeZero width] {C F : Type} (condition : Bool)
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  { state with failed := !condition || state.failed }

@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "reg_imm_def"
  (words_as_type_indexed_bitvec)]
def regImm {width : Nat} [NeZero width] {C F : Type} (operand : HolRegImm width)
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) : WordLocW width :=
  match operand with
  | .reg register => state.regs register
  | .imm value => .word value

@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "upd_fp_reg_def"
  (words_as_type_indexed_bitvec)]
def updFpReg {width : Nat} [NeZero width] {C F : Type} (register : Nat)
    (value : BitVec 64) (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  { state with fpRegs := fun key => if key = register then value else state.fpRegs key }

@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "read_fp_reg_def"
  (words_as_type_indexed_bitvec)]
def readFpReg {width : Nat} [NeZero width] {C F : Type} (register : Nat)
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) : BitVec 64 :=
  state.fpRegs register

@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "dec_clock_def"
  (words_as_type_indexed_bitvec)]
def decClock {width : Nat} [NeZero width] {C F : Type}
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  { state with clock := state.clock - 1 }

@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "inc_pc_def"
  (words_as_type_indexed_bitvec)]
def incPc {width : Nat} [NeZero width] {C F : Type}
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  { state with pc := state.pc + 1 }

end Flapjack.Compiler.Backend.LabSem
