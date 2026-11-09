module

public import Flapjack.Compiler.Encoders.Arm8.L3.Executable.Branch
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Loc

@[expose] public section

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

/-- The computable 20-bit `Loc` guard is exactly the L3 `arm8LocInRange`. -/
theorem fitsSigned20_iff_arm8LocInRange (a : BitVec 64) :
    fitsSigned 20 a = true ↔ arm8LocInRange a = true := by
  rw [arm8LocInRange_iff]
  constructor
  · intro h
    have htoInt : a.toInt = (BitVec.signExtend 64 (BitVec.setWidth 20 a)).toInt :=
      congrArg BitVec.toInt ((fitsSigned_iff_signExtend 20 (by decide) (by decide) a).mp h)
    rw [htoInt, BitVec.toInt_signExtend_eq_toNat_bmod, Nat.min_eq_right (by decide : 20 ≤ 64)]
    have hb : 0 < 2 ^ 20 := by norm_num
    have hle := Int.le_bmod (x := ((BitVec.setWidth 20 a).toNat : Int)) (m := 2 ^ 20) hb
    have hlt := Int.bmod_le (x := ((BitVec.setWidth 20 a).toNat : Int)) (m := 2 ^ 20) hb
    norm_num at hle hlt ⊢
    exact ⟨hle, hlt⟩
  · intro h
    rw [fitsSigned_iff_signExtend 20 (by decide) (by decide)]
    rw [← BitVec.toInt_inj]
    rw [BitVec.toInt_signExtend_eq_toNat_bmod, Nat.min_eq_right (by decide : 20 ≤ 64)]
    have hb : 0 < 2 ^ 20 := by norm_num
    rw [eq_comm, Int.bmod_eq_iff hb]
    refine ⟨?_, ?_, ?_⟩
    · norm_num
      exact h.1
    · norm_num
      omega
    · have h1 : (2 ^ 20 : Int) ∣ (a.toInt - (a.toNat : Int)) := by
        rw [BitVec.toInt_eq_toNat_bmod]
        exact Int.dvd_trans (by norm_num : (2 ^ 20 : Int) ∣ (2 ^ 64 : Int))
          Int.dvd_bmod_sub_self
      have h2 : (2 ^ 20 : Int) ∣ ((a.toNat : Int) - ↑((BitVec.setWidth 20 a).toNat)) := by
        rw [BitVec.toNat_setWidth]
        rw [← Int.natCast_sub (Nat.mod_le _ _)]
        exact Int.natCast_dvd_natCast.mpr (Nat.dvd_sub_mod (n := 2 ^ 20) a.toNat)
      have h3 := Int.dvd_add h1 h2
      have heq : a.toInt - (a.toNat : Int) + ((a.toNat : Int) -
          ↑((BitVec.setWidth 20 a).toNat)) =
          a.toInt - ↑((BitVec.setWidth 20 a).toNat) := by omega
      rw [heq] at h3
      exact h3

end Flapjack.Compiler.Encoders.Arm8.L3
