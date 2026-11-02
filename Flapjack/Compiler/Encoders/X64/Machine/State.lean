import Flapjack.Compiler.Encoders.X64.Target
import Flapjack.Compiler.Encoders.AsmProps.Target
import Flapjack.Misc.SetSep

/-!
# A closed x86-64 machine state for the emitted instruction subset

This module models only the architectural state that CakeML's `x64_ast`
touches: sixteen general-purpose registers, the program counter (RIP), the six
arithmetic flags, byte-addressable memory, eight XMM registers (as 128-bit
vectors, read at 64 bits), and a failure flag.  Segment registers, control
registers, the FPU control word, and the full L3 x86-64 model in
`HOL/examples/l3-machine-code/x64/model/x64Script.sml` are not modelled here.
No declaration in this file is tagged as an exact L3 port.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm

/-- The six arithmetic flags used by the emitted conditional instructions. -/
structure X64Flags where
  cf : Bool
  pf : Bool
  af : Bool
  zf : Bool
  sf : Bool
  of : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Architectural state of the closed x86-64 subset.  Register numbers are
L3's `Zreg` numbers (0 = RAX, ..., 15 = R15); `num2Zreg` reduces a source
register number modulo 16. -/
structure X64State where
  regs : Nat → BitVec 64
  pc : BitVec 64
  flags : X64Flags
  mem : BitVec 64 → BitVec 8
  memDomain : BitVec 64 → Prop
  xmm : Nat → BitVec 128
  failed : Bool

/-- Read a general-purpose register. -/
def readReg (s : X64State) (register : Nat) : BitVec 64 := s.regs (num2Zreg register)

/-- Write a general-purpose register. -/
def writeReg (s : X64State) (register : Nat) (value : BitVec 64) : X64State :=
  { s with regs := fun r => if r = num2Zreg register then value else s.regs r }

/-- Read the low 64 bits of an XMM register. -/
def readXmm (s : X64State) (register : Nat) : BitVec 64 :=
  (s.xmm (register % 8)).setWidth 64

/-- Write the low 64 bits of an XMM register, preserving the high bits. -/
def writeXmm (s : X64State) (register : Nat) (value : BitVec 64) : X64State :=
  { s with xmm := fun r =>
      if r = register % 8 then
        ((s.xmm (register % 8)).setWidth 128 &&& BitVec.ofNat 128 (2 ^ 128 - 2 ^ 64)) |||
          (value.setWidth 128)
      else s.xmm r }

/-- Read one byte of memory. -/
def readByte (s : X64State) (address : BitVec 64) : BitVec 8 := s.mem address

/-- Little-endian read of `n` bytes, zero-extended to 64 bits. -/
def readMemN (s : X64State) (size : Nat) (address : BitVec 64) : BitVec 64 :=
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

/-- Little-endian write of `n` bytes, taking the low bytes of `value`. -/
def writeMemN (s : X64State) (size : Nat) (address : BitVec 64) (value : BitVec 64) :
    X64State :=
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

/-- Valid machine states: the failure flag is clear.  `x64_config` has
`code_alignment = 0`, so there is no PC alignment requirement. -/
def x64StateOk (s : X64State) : Bool := !s.failed

/-- Projection used by `target_ok`: the PC, registers, XMM registers, flags,
failure flag, and the memory graph restricted to the source domain. -/
abbrev X64Projection :=
  BitVec 64 × (Nat → BitVec 64) × (Nat → BitVec 128) × X64Flags × Bool ×
    ((BitVec 64 × BitVec 8) → Prop)

/-- Everything `x64Next` reads. -/
def x64Proj (d : BitVec 64 → Prop) (s : X64State) : X64Projection :=
  (s.pc, s.regs, s.xmm, s.flags, s.failed, SetSep.fun2Set (s.mem, d))

end Flapjack.Compiler.Encoders.X64
