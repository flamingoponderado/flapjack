import Flapjack.Compiler.Encoders.Arm8.L3.Executable.Encoder
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.LogicalShiftedRegister

/-!
# Logical instructions: bytes for the L3 bridge

`Arm8.encodeInsn32` encodes `LogicalShiftedRegister` from `EncodeLogicalOp` and
the six-bit shift amount, returning `none` when the opcode pair is unspecified
or the amount does not fit six bits.  The L3 `Encode` has the same opcode guard
and the same range guard on the `word6` cast.  This module proves
`Arm8.encodeBytes` equals `L3.arm8Encode` for that form.

The computable `Insn` carries `Arm8.LogicalOp` and the L3 `instruction` carries
`LogicalOp`, so the lemma takes the two opcodes separately together with a
hypothesis that both encoders give them the same two-bit field.  The caller
supplies that hypothesis from the shared `arm8BopEnc` lowering.

No new HOL claim is introduced: the bridge relates two Lean renderings of the
same instruction word.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem

/-- `e_sf (TN := 64)` is the one-bit `sf` field. -/
theorem e_sf_64 (sf : BitVec 64) : e_sf (TN := 64) sf = (1 : BitVec 1) := by
  simp [e_sf, holV2w_one_true]

/-- The `LogicalShiftedRegister@64` word: `fields` and the L3 concatenation
agree. -/
theorem fields_logicalShiftedRegister (opc : Nat) (invert : Bool) (sh : ShiftType)
    (imm rm rn rd : Nat) :
    fields [(1, 1), (2, opc), (5, 0b01010), (2, shiftTypeBits sh), (1, bit invert),
      (5, rm), (6, imm), (5, rn), (5, rd)] =
      arm8LogicalShiftedRegisterWord (BitVec.ofNat 2 opc) invert sh imm
        (BitVec.ofNat 5 rm) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  cases invert <;> cases sh <;>
    · simp only [fields, List.foldl_cons, List.foldl_nil, arm8LogicalShiftedRegisterWord,
        shiftTypeBits, ShiftType2num, bit_false, bit_true, holV2w_one_true, holV2w_one_false]
      rw [ofNat_mod_setWidth 1, ofNat_mod_setWidth 2, ofNat_mod_setWidth 5, ofNat_mod_setWidth 6]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
        BitVec.getLsbD_append, BitVec.getLsbD_setWidth, Nat.testBit_mod_two_pow]
      interval_cases i <;> simp
      all_goals decide

/-- `arm8Encode` of the L3 `LogicalShiftedRegister@64` is the word's bytes,
provided the opcode exists and the shift amount fits six bits. -/
theorem arm8Encode_logicalShiftedRegister (opL3 : LogicalOp) (invert setFlags : Bool)
    (sh : ShiftType) (imm : Nat) (rm rn rd : BitVec 5) (opcbits : BitVec 2)
    (hopc : EncodeLogicalOp (opL3, setFlags) = some opcbits)
    (himm : imm < 64) :
    arm8Encode (.Data (.«LogicalShiftedRegister@64»
      ((1 : BitVec 64), (opL3, (invert, (setFlags, (sh,
        (imm, (rm, (rn, rd)))))))))) =
      [BitVec.ofNat 8 ((arm8LogicalShiftedRegisterWord opcbits invert sh imm
          rm rn rd >>> 0).toNat),
       BitVec.ofNat 8 ((arm8LogicalShiftedRegisterWord opcbits invert sh imm
          rm rn rd >>> 8).toNat),
       BitVec.ofNat 8 ((arm8LogicalShiftedRegisterWord opcbits invert sh imm
          rm rn rd >>> 16).toNat),
       BitVec.ofNat 8 ((arm8LogicalShiftedRegisterWord opcbits invert sh imm
          rm rn rd >>> 24).toNat)] := by
  have himm' : (imm == (BitVec.ofNat 6 imm).toNat) = true := by
    have hpow : (2 : Nat) ^ 6 = 64 := by norm_num
    rw [BitVec.toNat_ofNat, hpow, Nat.mod_eq_of_lt himm]
    exact beq_self_eq_true imm
  simp only [arm8Encode, Encode, e_data, hopc, himm', if_true, e_sf_64,
    arm8LogicalShiftedRegisterWord]
  rfl

/-- A `LogicalShiftedRegister` encodes to the same four bytes on both sides. -/
theorem encodeBytes_logicalShiftedRegister (op : Arm8.LogicalOp) (opL3 : LogicalOp)
    (invert setFlags : Bool) (sh : ShiftType) (imm rm rn rd : Nat) (n : Nat)
    (hlog : encodeLogicalOp op setFlags = some n)
    (hopc : EncodeLogicalOp (opL3, setFlags) = some (BitVec.ofNat 2 n))
    (himm : imm < 64) :
    encodeBytes (.logicalShiftedRegister op invert setFlags sh imm rm rn rd) =
      arm8Encode (.Data (.«LogicalShiftedRegister@64»
        ((1 : BitVec 64), (opL3, (invert, (setFlags, (sh,
          (imm, (BitVec.ofNat 5 rm, (BitVec.ofNat 5 rn, BitVec.ofNat 5 rd)))))))))) := by
  have hw : encodeInsn32 (.logicalShiftedRegister op invert setFlags sh imm rm rn rd) =
      some (fields [(1, 1), (2, n), (5, 0b01010), (2, shiftTypeBits sh), (1, bit invert),
        (5, rm), (6, imm), (5, rn), (5, rd)]) := by
    simp only [encodeInsn32]
    simp only [hlog, himm, if_true]
  rw [encodeBytes_eq_of_encodeInsn32 _ _ hw]
  rw [fields_logicalShiftedRegister]
  exact (arm8Encode_logicalShiftedRegister opL3 invert setFlags sh imm
    (BitVec.ofNat 5 rm) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) (BitVec.ofNat 2 n)
    hopc himm).symm

end Flapjack.Compiler.Encoders.Arm8.L3
