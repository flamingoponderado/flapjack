import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Compare
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.JumpCmp
import Flapjack.Compiler.Encoders.Arm8.Machine.MulCarryCase

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# `addCarry`

`arm8_ast` lowers `AddCarry r1 r2 r3 r4` to five instructions: a flag-setting
`SUBS XZR, r4, #0`, a `ConditionalCompareImmediate@64` on `r2` against zero
under the `EQ` condition, an `AddSubCarry@64` into `r1`, a `MoveWide .z` that
zeroes `r4`, and a final `AddSubCarry@64` into `r4`.  This module records the
step lemmas, the byte lists and the agreement facts, then assembles the case.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The unsigned comparison with zero is false. -/
theorem arm8Ult_zero (x : BitVec 64) : x.ult (0 : BitVec 64) = false := by
  show decide (x.toNat < (0 : BitVec 64).toNat) = false
  simp

/-- `BitVec.msb` at 64 bits is the top bit. -/
theorem arm8Msb_eq_getLsbD (x : BitVec 64) : BitVec.msb x = x.getLsbD 63 := by
  rw [BitVec.msb, arm8GetMsbD_zero_64]

/-- The rendered `Decode` inverts `arm8AddSubCarryWord` for both `opc`/`s`
combinations. -/
theorem arm8Decode_addSubCarry_gen (opc s : Bool) (rm rn rd : BitVec 5) :
    Decode (arm8AddSubCarryWord opc s rm rn rd) =
      instruction.Data (Data.«AddSubCarry@64»
        ((1 : BitVec 64), (opc, (s, (rm, (rn, rd)))))) := by
  simp only [arm8AddSubCarryWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  cases opc <;> cases s <;> simp [holV2w_one_false, holV2w_one_true, holV2w_five]

/-- `AddWithCarry` of `x` with the complemented zero is `x` with the flags of
`x - 0`. -/
theorem arm8AddWithCarry_subs_zero (x : BitVec 64) :
    AddWithCarry (TN := 64) (x, (~~~(0 : BitVec 64), true)) =
      (x, (BitVec.msb x, ((x == (0 : BitVec 64)), (true, false)))) := by
  rw [arm8AddWithCarry_machine, addWithCarry_subFlags]
  simp only [subFlags]
  have hx : x - (0 : BitVec 64) = x := by simp
  have hC : decide (x.toNat ≠ x.toNat + (~~~(0 : BitVec 64)).toNat + 1) = true := by
    have h : (~~~(0 : BitVec 64)).toNat = 2 ^ 64 - 1 := by decide
    rw [h, decide_eq_true_iff]
    omega
  have hV : decide (x.toInt ≠ x.toInt + (~~~(0 : BitVec 64)).toInt + 1) = false := by
    have h : (~~~(0 : BitVec 64)).toInt = -1 := by decide
    rw [h, decide_eq_false_iff_not]
    omega
  rw [hx, hC, hV, arm8Msb_eq_getLsbD]
  rw [← arm8Beq_eq_decide x 0]

/-- `AddWithCarry` of `x` with the zero immediate and no carry is `x` with the
flags of `x + 0`. -/
theorem arm8AddWithCarry_add_zero (x : BitVec 64) :
    AddWithCarry (TN := 64) (x, ((0 : BitVec 64), false)) =
      (x, (BitVec.msb x, ((x == (0 : BitVec 64)), (false, false)))) := by
  rw [arm8AddWithCarry_machine, addWithCarry_addFlags]
  simp only [addFlags]
  have hx : x + (0 : BitVec 64) = x := by simp
  have hC : decide (x.toNat ≠ x.toNat + (0 : BitVec 64).toNat) = false := by
    have h : (0 : BitVec 64).toNat = 0 := by decide
    rw [h, decide_eq_false_iff_not]
    omega
  have hV : decide (x.toInt ≠ x.toInt + (0 : BitVec 64).toInt) = false := by
    have h : (0 : BitVec 64).toInt = 0 := by decide
    rw [h, decide_eq_false_iff_not]
    omega
  rw [hx, hC, hV, arm8Msb_eq_getLsbD]
  rw [← arm8Beq_eq_decide x 0]

end Flapjack.Compiler.Encoders.Arm8.L3
