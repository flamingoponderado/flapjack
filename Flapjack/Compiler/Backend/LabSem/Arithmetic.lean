import Flapjack.Compiler.Backend.LabSem.Updates
import Flapjack.Compiler.Encoders.AsmSem

/-! Literal native LabSem integer arithmetic. Destination writes precede the
source assertions, so failure does not roll back a shift/division result.
Constructor fields are matched by source position (r1 ... r5), rather than
by the descriptive binder labels in HolArith. Sequential writes determine the
winner for aliased destinations. HOL DIV_0/MOD_0 match Nat and BitVec
udiv: zero quotient and unchanged numerator as remainder at a zero divisor. No clock, memory or FP transition is changed. -/

namespace Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def binopUpd {width : Nat} [NeZero width] {C F : Type} (register : Nat)
    (operator : Flapjack.BinOp) (left right : BitVec width)
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  updReg register (.word (match operator with
    | .add => left + right
    | .sub => left - right
    | .and => left &&& right
    | .or => left ||| right
    | .xor => left ^^^ right)) state

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def arithUpd {width : Nat} [NeZero width] {C F : Type} (operation : HolArith width)
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  match operation with
  | .binop operator r1 r2 operand =>
      match state.regs r2, regImm operand state with
      | .word w1, .word w2 => binopUpd r1 operator w1 w2 state
      | value, _ =>
          let sameRegister := match operand with
            | .reg register => register == r2
            | .imm _ => false
          if operator = .or ∧ sameRegister = true then updReg r1 value state
          else assertState false state
  | .shift operator r1 r2 operand =>
      match state.regs r2, regImm operand state with
      | .word w1, .word w2 =>
          assertState (decide (w2.toNat < width))
            (updReg r1 (.word (Flapjack.Compiler.Encoders.AsmSem.wordShift operator w1 w2.toNat)) state)
      | _, _ => assertState false state
  | .div r1 r2 r3 =>
      match state.regs r3, state.regs r2 with
      | .word divisor, .word dividend =>
          -- HOL `/` on words is the signed `word_quot` (wordsScript.sml:355-366,
          -- overloaded at 397-398); `BitVec.sdiv` has exactly its four sign cases.
          assertState (decide (divisor ≠ 0)) (updReg r1 (.word (dividend.sdiv divisor)) state)
      | _, _ => assertState false state
  | .addCarry r1 r2 r3 r4 =>
      match state.regs r2, state.regs r3, state.regs r4 with
      | .word w2, .word w3, .word w4 =>
          let result := w2.toNat + w3.toNat + if w4 = 0 then 0 else 1
          updReg r4 (.word (if 2 ^ width ≤ result then 1 else 0))
            (updReg r1 (.word (BitVec.ofNat width result)) state)
      | _, _, _ => assertState false state
  | .longMul r1 r2 r3 r4 =>
      match state.regs r3, state.regs r4 with
      | .word w3, .word w4 =>
          let result := w3.toNat * w4.toNat
          updReg r2 (.word (BitVec.ofNat width result))
            (updReg r1 (.word (BitVec.ofNat width (result / 2 ^ width))) state)
      | _, _ => assertState false state
  | .longDiv r1 r2 r3 r4 r5 =>
      match state.regs r3, state.regs r4, state.regs r5 with
      | .word w3, .word w4, .word w5 =>
          let numerator := w3.toNat * 2 ^ width + w4.toNat
          let divisor := w5.toNat
          let quotient := numerator / divisor
          assertState (decide (divisor ≠ 0 ∧ quotient < 2 ^ width))
            (updReg r1 (.word (BitVec.ofNat width quotient))
              (updReg r2 (.word (BitVec.ofNat width (numerator % divisor))) state))
      | _, _, _ => assertState false state
  | .addOverflow r1 r2 r3 r4 =>
      match state.regs r2, state.regs r3 with
      | .word w2, .word w3 =>
          updReg r4 (.word (if (w2 + w3).toInt ≠ w2.toInt + w3.toInt then 1 else 0))
            (updReg r1 (.word (w2 + w3)) state)
      | _, _ => assertState false state
  | .subOverflow r1 r2 r3 r4 =>
      match state.regs r2, state.regs r3 with
      | .word w2, .word w3 =>
          updReg r4 (.word (if (w2 - w3).toInt ≠ w2.toInt - w3.toInt then 1 else 0))
            (updReg r1 (.word (w2 - w3)) state)
      | _, _ => assertState false state

end Flapjack.Compiler.Backend.LabSem
