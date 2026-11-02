import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Infrastructure

set_option maxHeartbeats 4000000
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

end Flapjack.Compiler.Encoders.Arm8.L3
