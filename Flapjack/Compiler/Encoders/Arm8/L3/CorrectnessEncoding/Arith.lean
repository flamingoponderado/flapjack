import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.MoveWide
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.LogicalImmediate

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# The `arith` constructors of `encoder_correct arm8TargetL3`

Encoding facts for the arithmetic instruction forms used by `arm8_ast`.
The `binop` case proof itself is built on these in the next layer.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The word emitted for `AddSubShiftedRegister@64`, in the shape produced by
the rendered `e_data` (Flapjack infrastructure: a readable abbreviation for a
mechanically rendered term). -/
def arm8AddSubShiftedRegisterWord (op : Bool) (s : Bool) (shift : ShiftType)
    (rm : BitVec 5) (amount : BitVec 6) (rn rd : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((1 : BitVec 1) ++ BitVec.setWidth 31 (holV2w 1 [op] ++ BitVec.setWidth 30 (holV2w 1 [s] ++ BitVec.setWidth 29 ((11 : BitVec 5) ++ BitVec.setWidth 24 (BitVec.ofNat 2 (ShiftType2num shift) ++ BitVec.setWidth 22 ((0 : BitVec 1) ++ BitVec.setWidth 21 (rm ++ BitVec.setWidth 16 (amount ++ BitVec.setWidth 10 (rn ++ rd)))))))))

/-- `Encode` of `AddSubShiftedRegister@64` is the shifted-register word
(Flapjack infrastructure; no separately named HOL declaration). -/
theorem arm8Encode_addSubShiftedRegister (op : Bool) (s : Bool) (shift : ShiftType)
    (rm : BitVec 5) (amount : BitVec 6) (rn rd : BitVec 5) :
    Encode (.Data (.«AddSubShiftedRegister@64»
      ((1 : BitVec 64), (op, (s, (shift, (rm, (amount, (rn, rd))))))))) =
      MachineCode.ARM8 (arm8AddSubShiftedRegisterWord op s shift rm amount rn rd) := by
  simp only [Encode, e_data, arm8AddSubShiftedRegisterWord]
  rfl

theorem holV2w_one_false : holV2w 1 [false] = (0 : BitVec 1) := by decide

/-- The rendered `Decode` inverts `arm8AddSubShiftedRegisterWord` for the
`lsl` shift used by `arm8_ast` (the other shifts encode other instructions,
and `ror` decodes as `Reserved`). -/
theorem arm8Decode_addSubShiftedRegister (op : Bool) (s : Bool)
    (rm : BitVec 5) (amount : BitVec 6) (rn rd : BitVec 5) :
    Decode (arm8AddSubShiftedRegisterWord op s ShiftType.lsl rm amount rn rd) =
      instruction.Data (Data.«AddSubShiftedRegister@64»
        ((1 : BitVec 64), (op, (s, (ShiftType.lsl, (rm, (amount, (rn, rd)))))))) := by
  simp only [arm8AddSubShiftedRegisterWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  cases op <;> cases s <;>
    simp [holV2w_one_true, holV2w_one_false, holV2w_two_zero, holV2w_five,
      holV2w_six, DecodeShift, ShiftType2num, num2ShiftType]

/-- `Run` of `AddSubShiftedRegister@64` with the `lsl` shift: add or subtract
the shifted register through `AddWithCarry`, write the result to `rd`, and
optionally set the flags. -/
theorem arm8Run_addSubShiftedRegister (op : Bool) (rm : BitVec 5) (amount : BitVec 6)
    (rn rd : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.«AddSubShiftedRegister@64»
      ((1 : BitVec 64), (op, (false, (ShiftType.lsl, (rm, (amount, (rn, rd))))))))) st =
      let p := if op then (~~~ShiftReg (TN := 64) (rm, ShiftType.lsl, amount.toNat) st, true)
        else (ShiftReg (TN := 64) (rm, ShiftType.lsl, amount.toNat) st, false)
      let r := AddWithCarry (X rn st, p.1, p.2)
      write'X (r.1, rd) (SetTheFlags (false, r.2) st) := by
  cases op <;>
    simp only [Run, «dfn'AddSubShiftedRegister», Bool.false_eq_true, if_true, if_false]

end Flapjack.Compiler.Encoders.Arm8.L3


