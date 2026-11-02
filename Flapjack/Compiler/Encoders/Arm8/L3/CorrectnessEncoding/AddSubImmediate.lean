import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.LogicalShiftedRegister

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# `AddSubImmediate@64`: the word, `Encode`, `Decode` and `Run`

`arm8_ast` lowers `Binop Add`/`Binop Sub` with an immediate operand to
`AddSubImmediate@64 (1, op, false, imm, rn, rd)`.  `Encode` accepts the
immediate only when it fits the low twelve bits or the twelve bits shifted by
twelve; this module records the two words and their semantic facts.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The word emitted for `AddSubImmediate@64` (Flapjack infrastructure: a
readable abbreviation for the rendered `e_data` term). -/
def arm8AddSubImmediateWord (op : Bool) (hi : Bool) (imm12 : BitVec 12)
    (rn rd : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((1 : BitVec 1) ++
    BitVec.setWidth 31 (holV2w 1 [op] ++
      BitVec.setWidth 30 (holV2w 1 [false] ++
        BitVec.setWidth 29 ((BitVec.ofNat 7 (if hi then 69 else 68)) ++
          BitVec.setWidth 22 (imm12 ++ BitVec.setWidth 10 (rn ++ rd))))))

/-- The two-branch body of the rendered `e_data` for `AddSubImmediate@64`. -/
theorem arm8EData_addSubImmediate (op : Bool) (imm : BitVec 64) (rn rd : BitVec 5) :
    e_data (.«AddSubImmediate@64» (1, op, false, imm, rn, rd)) =
      (if ((imm &&& ~~~(4095 : BitVec 64)) == (0 : BitVec 64)) then
        MachineCode.ARM8 (arm8AddSubImmediateWord op false (holWordExtract 12 11 0 imm) rn rd)
      else if ((imm &&& ~~~(16773120 : BitVec 64)) == (0 : BitVec 64)) then
        MachineCode.ARM8 (arm8AddSubImmediateWord op true (holWordExtract 12 23 12 imm) rn rd)
      else MachineCode.BadCode [BitVec.ofNat 8 65, BitVec.ofNat 8 100, BitVec.ofNat 8 100,
        BitVec.ofNat 8 83, BitVec.ofNat 8 117, BitVec.ofNat 8 98, BitVec.ofNat 8 73,
        BitVec.ofNat 8 109, BitVec.ofNat 8 109, BitVec.ofNat 8 101, BitVec.ofNat 8 100,
        BitVec.ofNat 8 105, BitVec.ofNat 8 97, BitVec.ofNat 8 116, BitVec.ofNat 8 101]) := rfl

/-- `Encode` of an immediate that fits the low twelve bits. -/
theorem arm8Encode_addSubImmediate_low (op : Bool) (imm : BitVec 64) (rn rd : BitVec 5)
    (hlow : imm &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)) :
    Encode (.Data (.«AddSubImmediate@64» (1, op, false, imm, rn, rd))) =
      MachineCode.ARM8 (arm8AddSubImmediateWord op false (holWordExtract 12 11 0 imm) rn rd) := by
  have hc : ((imm &&& ~~~(4095 : BitVec 64)) == (0 : BitVec 64)) = true := by
    rw [beq_iff_eq]; exact hlow
  rw [show Encode (.Data (.«AddSubImmediate@64» (1, op, false, imm, rn, rd))) =
      e_data (.«AddSubImmediate@64» (1, op, false, imm, rn, rd)) from rfl,
    arm8EData_addSubImmediate, hc]
  rw [if_pos rfl]


/-- `Encode` of an immediate whose twelve bits are shifted by twelve. -/
theorem arm8Encode_addSubImmediate_high (op : Bool) (imm : BitVec 64) (rn rd : BitVec 5)
    (hne : ¬ ((imm &&& ~~~(4095 : BitVec 64)) == (0 : BitVec 64)) = true)
    (hhigh : imm &&& ~~~(16773120 : BitVec 64) = (0 : BitVec 64)) :
    Encode (.Data (.«AddSubImmediate@64» (1, op, false, imm, rn, rd))) =
      MachineCode.ARM8 (arm8AddSubImmediateWord op true (holWordExtract 12 23 12 imm) rn rd) := by
  have hc2 : ((imm &&& ~~~(16773120 : BitVec 64)) == (0 : BitVec 64)) = true := by
    rw [beq_iff_eq]; exact hhigh
  rw [show Encode (.Data (.«AddSubImmediate@64» (1, op, false, imm, rn, rd))) =
      e_data (.«AddSubImmediate@64» (1, op, false, imm, rn, rd)) from rfl,
    arm8EData_addSubImmediate, hc2, if_neg hne]
  rw [if_pos rfl]

end Flapjack.Compiler.Encoders.Arm8.L3
