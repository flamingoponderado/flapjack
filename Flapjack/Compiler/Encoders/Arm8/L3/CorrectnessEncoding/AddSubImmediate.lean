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


/-- Twelve-bit roundtrip through the `getElem` bit list used by `Decode`. -/
theorem holV2w_twelve (w : BitVec 12) :
    holV2w 12 [w[11], w[10], w[9], w[8], w[7], w[6], w[5], w[4], w[3], w[2], w[1], w[0]] = w :=
  holV2w_holW2v w

/-- An immediate that fits the low twelve bits is recovered by truncating to
twelve bits and widening back. -/
theorem arm8AddSubImmediate_low_eq (imm : BitVec 64)
    (hlow : imm &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)) :
    BitVec.setWidth 64 (holWordExtract 12 11 0 imm) = imm := by
  have heq : imm &&& (4095 : BitVec 64) = imm := and_not_eq_zero_eq imm 4095 hlow
  have hlt : imm.toNat < 4096 := by
    have h := congrArg BitVec.toNat heq
    rw [BitVec.toNat_and] at h
    have h2 : imm.toNat &&& 4095 ≤ 4095 := Nat.and_le_right
    have hle : imm.toNat ≤ 4095 := by rw [← h]; exact h2
    omega
  have hx : (holWordExtract 12 11 0 imm).toNat = imm.toNat := by
    have h1 : holWordExtract 12 11 0 imm = BitVec.setWidth 12 imm := by
      simp only [Flapjack.RiscV.L3.holWordExtract]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
    rw [h1, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt]
  rw [← BitVec.ofNat_toNat, hx, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The rendered `Decode` inverts the low-immediate word. -/
theorem arm8Decode_addSubImmediate_low (op : Bool) (imm : BitVec 64) (rn rd : BitVec 5)
    (hlow : imm &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)) :
    Decode (arm8AddSubImmediateWord op false (holWordExtract 12 11 0 imm) rn rd) =
      instruction.Data (Data.«AddSubImmediate@64» (1, op, false, imm, rn, rd)) := by
  have himm := arm8AddSubImmediate_low_eq imm hlow
  simp only [arm8AddSubImmediateWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  cases op <;>
    simp [holV2w_two_zero, holV2w_five, holV2w_twelve,
      arm8HolV2w_one_false, arm8HolV2w_one_true, himm]

end Flapjack.Compiler.Encoders.Arm8.L3
