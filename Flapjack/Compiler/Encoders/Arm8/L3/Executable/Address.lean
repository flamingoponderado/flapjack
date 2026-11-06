import Flapjack.Compiler.Encoders.Arm8.L3.Executable.Branch
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Loc

/-!
# Address: bytes for the L3 bridge

`Arm8.encodeInsn32` encodes `Address` (the `ADR` form, page `false`) from the
low 21 bits of the offset, guarded by `fitsSigned 21`.  The L3 `Encode` tests
that the offset is the sign extension of those 21 bits, which is the same
condition.  This module proves `Arm8.encodeBytes` equals `L3.arm8Encode` for
this form, including the out-of-range case where both sides fall back to four
zero bytes.

`arm8Ast` only emits `Address` with page `false` (from `.loc`), so the `ADRP`
form is not bridged here.

No new HOL claim is introduced: the bridge relates two Lean renderings of the
same instruction word.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem

/-- `holWordExtract 2 1 0` is the low two bits. -/
theorem holWordExtract_two (imm : BitVec 64) :
    holWordExtract 2 1 0 imm = BitVec.ofNat 2 (imm.toNat % 4) := by
  simp only [holWordExtract]
  rw [holWordExtract_eq_setWidth 2 1 0 imm (by decide) (by decide) (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
  norm_num

/-- The `Address` word: `fields` and the L3 concatenation agree. -/
theorem fields_address (imm : BitVec 64) (rd : Nat) :
    fields [(1, 0), (2, imm.toNat % 4), (5, 16), (19, (imm >>> 2).toNat % 2 ^ 19), (5, rd)] =
      arm8AddressWord imm (BitVec.ofNat 5 rd) := by
  rw [arm8AddressWord, holWordExtract_two imm, ← ofNat19_shift_eq imm]
  simp only [fields, List.foldl_cons, List.foldl_nil]
  rw [ofNat_mod_setWidth 1, ofNat_mod_setWidth 2, ofNat_mod_setWidth 5, ofNat_mod_setWidth 19]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    BitVec.getLsbD_append, BitVec.getLsbD_setWidth, Nat.testBit_mod_two_pow]
  interval_cases i <;> simp

/-- The computable address guard is exactly the L3 sign-extension guard. -/
theorem addressGuard_iff (imm : BitVec 64) :
    fitsSigned 21 imm = true ↔
      BitVec.signExtend 64 (BitVec.setWidth 21
        (holWordExtract 19 20 2 imm ++ holWordExtract 2 1 0 imm)) = imm := by
  rw [arm8AddressBits, BitVec.setWidth_setWidth_of_le _ (by norm_num)]
  exact (fitsSigned_iff_signExtend 21 (by decide) (by decide) imm).trans eq_comm

/-- When the L3 address guard fails, `arm8Encode` is four zero bytes. -/
theorem arm8EncodeBytes_address_bad (imm : BitVec 64) (rd : BitVec 5)
    (hl3 : ¬ (BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 imm ++ holWordExtract 2 1 0 imm)) = imm)) :
    arm8Encode (.Address (false, (imm, rd))) = [0, 0, 0, 0] := by
  have hc : (BitVec.signExtend 64 (BitVec.setWidth 21
      (holWordExtract 19 20 2 imm ++ holWordExtract 2 1 0 imm)) == imm) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    exact hl3 h
  simp only [arm8Encode, Encode, Bool.false_eq_true, if_false, hc]

/-- An `Address` encodes to the same four bytes on both sides, at every offset. -/
theorem encodeBytes_address (imm : BitVec 64) (rd : Nat) :
    encodeBytes (.address false imm rd) =
      arm8Encode (.Address (false, (imm, BitVec.ofNat 5 rd))) := by
  by_cases hf : fitsSigned 21 imm = true
  · have hw : encodeInsn32 (.address false imm rd) =
        some (fields [(1, 0), (2, imm.toNat % 4), (5, 16),
          (19, (imm >>> 2).toNat % 2 ^ 19), (5, rd)]) := by
      simp only [encodeInsn32, Bool.false_eq_true, if_false, hf, if_true]
    rw [encodeBytes_eq_of_encodeInsn32 _ _ hw, fields_address]
    exact (arm8EncodeBytes_address imm (BitVec.ofNat 5 rd)
      ((addressGuard_iff imm).mp hf)).symm
  · have hgf : fitsSigned 21 imm = false := by
      cases h : fitsSigned 21 imm
      · rfl
      · exact absurd h hf
    have hl3 : ¬ (BitVec.signExtend 64 (BitVec.setWidth 21
        (holWordExtract 19 20 2 imm ++ holWordExtract 2 1 0 imm)) = imm) :=
      fun h => hf ((addressGuard_iff imm).mpr h)
    have hw : encodeInsn32 (.address false imm rd) = none := by
      simp only [encodeInsn32]
      rw [hgf]
      simp
    rw [encodeBytes_eq_of_encodeInsn32_none _ hw]
    exact (arm8EncodeBytes_address_bad imm (BitVec.ofNat 5 rd) hl3).symm

end Flapjack.Compiler.Encoders.Arm8.L3
