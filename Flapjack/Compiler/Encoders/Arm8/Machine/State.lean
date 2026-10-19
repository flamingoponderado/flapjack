import Flapjack.Compiler.Encoders.Arm8.Target
import Flapjack.Compiler.Encoders.AsmProps.Target
import Flapjack.Misc.Alignment
import Flapjack.Misc.SetSep

/-!
# A closed ARMv8 machine state for the Pancake instruction subset

This module starts the machine-semantics side of the ARMv8 backend.  It models
only the architectural state that CakeML's `arm8_ast` actually touches: the 31
general-purpose registers (plus the zero register), the program counter, the
four condition flags, byte-addressable memory, and a failure flag.  System
registers, exception levels, floating point, and the memory-management unit are
not modelled; they are outside the emitted instruction subset.  The full L3
model in `HOL/examples/l3-machine-code/arm8/model/arm8Script.sml` is not ported
here, and no declaration in this file is tagged as an exact L3 port.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm

/-- Architectural state of the closed ARMv8 subset.  `regs 31` is not read as a
stack pointer by the emitted subset; `readReg` below maps it to zero, matching
the zero-register role that `arm8_ast` uses for register 31. -/
structure Arm8State where
  regs : Nat → BitVec 64
  pc : BitVec 64
  n : Bool
  z : Bool
  c : Bool
  v : Bool
  mem : BitVec 64 → BitVec 8
  memDomain : BitVec 64 → Prop
  failed : Bool

/-- Data-processing register read: register 31 is the ARM zero register. -/
def readReg (s : Arm8State) (register : Nat) : BitVec 64 :=
  if register = 31 then 0 else s.regs register

/-- Write a data-processing register, ignoring writes to the zero register. -/
def writeReg (s : Arm8State) (register : Nat) (value : BitVec 64) : Arm8State :=
  if register = 31 then s else { s with regs := fun r => if r = register then value else s.regs r }

/-- Read one byte. -/
def readByte (s : Arm8State) (address : BitVec 64) : BitVec 8 := s.mem address

/-- Little-endian read of `n` bytes.  The result is returned at 64 bits, which is
enough for every load in the emitted subset. -/
def readMemN (s : Arm8State) (size : Nat) (address : BitVec 64) : BitVec 64 :=
  match size with
  | 0 => 0
  | 1 => (s.mem address).setWidth 64
  | 2 => ((s.mem (address + 1)).setWidth 64 <<< 8) ||| (s.mem address).setWidth 64
  | 3 => ((s.mem (address + 2)).setWidth 64 <<< 16) |||
      ((s.mem (address + 1)).setWidth 64 <<< 8) ||| (s.mem address).setWidth 64
  | 4 => ((s.mem (address + 3)).setWidth 64 <<< 24) |||
      ((s.mem (address + 2)).setWidth 64 <<< 16) |||
      ((s.mem (address + 1)).setWidth 64 <<< 8) ||| (s.mem address).setWidth 64
  | _ => ((s.mem (address + 7)).setWidth 64 <<< 56) |||
      ((s.mem (address + 6)).setWidth 64 <<< 48) |||
      ((s.mem (address + 5)).setWidth 64 <<< 40) |||
      ((s.mem (address + 4)).setWidth 64 <<< 32) |||
      ((s.mem (address + 3)).setWidth 64 <<< 24) |||
      ((s.mem (address + 2)).setWidth 64 <<< 16) |||
      ((s.mem (address + 1)).setWidth 64 <<< 8) ||| (s.mem address).setWidth 64

/-- Little-endian write of `n` bytes. -/
def writeMemN (s : Arm8State) (size : Nat) (address : BitVec 64) (value : BitVec 64) : Arm8State :=
  let byteAt (n : Nat) : BitVec 8 := (value >>> (8 * n)).setWidth 8
  match size with
  | 0 => s
  | 1 => { s with mem := fun a => (if a = address then byteAt 0 else s.mem a) }
  | 2 => { s with mem := fun a => (
      if a = address then byteAt 0
      else if a = address + 1 then byteAt 1
      else s.mem a) }
  | 3 => { s with mem := fun a => (
      if a = address then byteAt 0
      else if a = address + 1 then byteAt 1
      else if a = address + 2 then byteAt 2
      else s.mem a) }
  | 4 => { s with mem := fun a => (
      if a = address then byteAt 0
      else if a = address + 1 then byteAt 1
      else if a = address + 2 then byteAt 2
      else if a = address + 3 then byteAt 3
      else s.mem a) }
  | _ => { s with mem := fun a => (
      if a = address then byteAt 0
      else if a = address + 1 then byteAt 1
      else if a = address + 2 then byteAt 2
      else if a = address + 3 then byteAt 3
      else if a = address + 4 then byteAt 4
      else if a = address + 5 then byteAt 5
      else if a = address + 6 then byteAt 6
      else if a = address + 7 then byteAt 7
      else s.mem a) }

/-- ARM condition flags in the order `N`, `Z`, `C`, `V`. -/
abbrev Arm8Flags := Bool × Bool × Bool × Bool

/-- Read the flags. -/
def readFlags (s : Arm8State) : Arm8Flags := (s.n, s.z, s.c, s.v)

/-- Write the flags. -/
def writeFlags (s : Arm8State) (f : Arm8Flags) : Arm8State :=
  { s with n := f.1, z := f.2.1, c := f.2.2.1, v := f.2.2.2 }

/-- Valid machine states: word-aligned PC and no failed assertion. -/
def arm8StateOk (s : Arm8State) : Bool :=
  holAligned 2 s.pc && !s.failed

/-- Projection used by `target_ok`: the PC, registers, flags, failure flag, and
the memory graph restricted to the source memory domain. -/
abbrev Arm8Projection :=
  BitVec 64 × Arm8Flags × Bool × (Nat → BitVec 64) × ((BitVec 64 × BitVec 8) → Prop)

/-- Everything `arm8Next` reads. -/
def arm8Proj (d : BitVec 64 → Prop) (s : Arm8State) : Arm8Projection :=
  (s.pc, readFlags s, s.failed, s.regs, SetSep.fun2Set (s.mem, d))

end Flapjack.Compiler.Encoders.Arm8
