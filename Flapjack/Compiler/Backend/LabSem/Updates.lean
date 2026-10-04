import Flapjack.Compiler.Backend.LabSem.State

/-! Literal shared state primitives of `labSemScript.sml`. Registers and
memory remain total functions; failure is sticky and does not undo updates.
-/

namespace Flapjack.Compiler.Backend.LabSem

open Flapjack.Compiler.Encoders.Asm

def updPc {width : Nat} [NeZero width] {C F : Type} (pc : Nat)
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  { state with pc := pc }

def updReg {width : Nat} [NeZero width] {C F : Type} (register : Nat)
    (value : WordLocW width) (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  { state with regs := fun key => if key = register then value else state.regs key }

def updMem {width : Nat} [NeZero width] {C F : Type} (address : BitVec width)
    (value : WordLocW width) (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  { state with memory := fun key => if key = address then value else state.memory key }

def assertState {width : Nat} [NeZero width] {C F : Type} (condition : Bool)
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  { state with failed := !condition || state.failed }

def regImm {width : Nat} [NeZero width] {C F : Type} (operand : HolRegImm width)
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) : WordLocW width :=
  match operand with
  | .reg register => state.regs register
  | .imm value => .word value

def decClock {width : Nat} [NeZero width] {C F : Type}
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  { state with clock := state.clock - 1 }

def incPc {width : Nat} [NeZero width] {C F : Type}
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  { state with pc := state.pc + 1 }

end Flapjack.Compiler.Backend.LabSem
