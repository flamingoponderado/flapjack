import Flapjack.Compiler.Encoders.AsmSem.State
import Flapjack.Compiler.Encoders.AsmSem

/-! Faithful asmSem state primitives and the complete arithmetic transition.
Assertions retain completed writes and previous failures. Constructor arguments
follow the original positional registers even where carrier binder labels differ. -/
namespace Flapjack.Compiler.Encoders.AsmSem
open Flapjack Flapjack.Compiler.Encoders.Asm

def updPc {width : Nat} [NeZero width] (pc : BitVec width) (s : AsmState width) : AsmState width :=
  { s with pc := pc }
def updReg {width : Nat} [NeZero width] (register : Nat) (value : BitVec width)
    (s : AsmState width) : AsmState width :=
  { s with regs := fun r => if r = register then value else s.regs r }
def updMem {width : Nat} [NeZero width] (address : BitVec width) (value : BitVec 8)
    (s : AsmState width) : AsmState width :=
  { s with mem := fun a => if a = address then value else s.mem a }
def readReg {width : Nat} [NeZero width] (register : Nat) (s : AsmState width) : BitVec width := s.regs register
def readMem {width : Nat} [NeZero width] (address : BitVec width) (s : AsmState width) : BitVec 8 := s.mem address
def assertState {width : Nat} [NeZero width] (condition : Bool) (s : AsmState width) : AsmState width :=
  { s with failed := !condition || s.failed }
def regImm {width : Nat} [NeZero width] (operand : HolRegImm width) (s : AsmState width) : BitVec width :=
  match operand with | .reg register => readReg register s | .imm value => value
def binopUpd {width : Nat} [NeZero width] (register : Nat) (operator : HolBinop)
    (w1 w2 : BitVec width) (s : AsmState width) : AsmState width :=
  updReg register (match operator with
    | .add => w1 + w2 | .sub => w1 - w2 | .and => w1 &&& w2
    | .or => w1 ||| w2 | .xor => w1 ^^^ w2) s
def isTest (comparison : HolCmp) : Bool :=
  match comparison with | .test | .notTest => true | _ => false

def arithUpd {width : Nat} [NeZero width] (operation : HolArith width)
    (s : AsmState width) : AsmState width :=
  match operation with
  | .binop operator r1 r2 ri => binopUpd r1 operator (readReg r2 s) (regImm ri s) s
  | .shift operator r1 r2 ri =>
    assertState (match ri with | .reg r => decide ((readReg r s).toNat < width) | .imm _ => true)
      (updReg r1 (wordShift operator (readReg r2 s) (regImm ri s).toNat) s)
  | .div r1 r2 r3 =>
    -- HOL `/` on words is the signed `word_quot` (wordsScript.sml:355-366,
    -- overloaded at 397-398); `BitVec.sdiv` has exactly its four sign cases.
    let q := readReg r3 s
    assertState (q != 0) (updReg r1 ((readReg r2 s).sdiv q) s)
  | .longMul r1 r2 r3 r4 =>
    let r := (readReg r3 s).toNat * (readReg r4 s).toNat
    updReg r2 (BitVec.ofNat width r) (updReg r1 (BitVec.ofNat width (r / 2 ^ width)) s)
  | .longDiv r1 r2 r3 r4 r5 =>
    let n := (readReg r3 s).toNat * 2 ^ width + (readReg r4 s).toNat
    let d := (readReg r5 s).toNat
    let q := n / d
    assertState (decide (d ≠ 0 ∧ q < 2 ^ width))
      (updReg r1 (BitVec.ofNat width q) (updReg r2 (BitVec.ofNat width (n % d)) s))
  | .addCarry r1 r2 r3 r4 =>
    let r := (readReg r2 s).toNat + (readReg r3 s).toNat + (if readReg r4 s = 0 then 0 else 1)
    updReg r4 (if 2 ^ width ≤ r then 1 else 0) (updReg r1 (BitVec.ofNat width r) s)
  | .addOverflow r1 r2 r3 r4 =>
    let w2 := readReg r2 s
    let w3 := readReg r3 s
    updReg r4 (if (w2 + w3).toInt ≠ w2.toInt + w3.toInt then 1 else 0) (updReg r1 (w2 + w3) s)
  | .subOverflow r1 r2 r3 r4 =>
    let w2 := readReg r2 s
    let w3 := readReg r3 s
    updReg r4 (if (w2 - w3).toInt ≠ w2.toInt - w3.toInt then 1 else 0) (updReg r1 (w2 - w3) s)

end Flapjack.Compiler.Encoders.AsmSem
