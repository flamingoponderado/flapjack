import Flapjack.Compiler.Encoders.Arm8.L3.Executable.Memory
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.AddSubImmediate
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Compare

/-!
# Arithmetic immediates: bytes for the L3 bridge

`Arm8.encodeInsn32` encodes `AddSubImmediate` in one of two forms -- the low
twelve-bit immediate, or the same twelve bits shifted left by twelve -- and
`none` when the immediate fits neither; `ConditionalCompareImmediate` is
encoded when the immediate fits the five-bit field and is `none` otherwise.
This module proves `Arm8.encodeBytes` equals `L3.arm8Encode` for each of those
cases, for either value of the `setFlags` field.

No new HOL claim is introduced: the bridge relates two Lean renderings of the
same instruction word.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem

/-- The twelve-bit field at bits 23:12 of a 64-bit word is the L3
`holWordExtract`. -/
theorem imm12Word_shift_eq (v : BitVec 64) :
    BitVec.ofNat 12 ((v >>> (12 : Nat)).toNat % 4096) = holWordExtract 12 23 12 v := by
  simp only [holWordExtract]
  rw [holWordExtract_eq_setWidth 12 (a := 64) 23 12 v (by omega) (by omega) (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
  omega

/-- `fields` builds the low add/sub immediate word (no flags). -/
theorem fields_addSubImmediate_low (sub : Bool) (imm rn rd : Nat) :
    fields [(1, 1), (1, bit sub), (1, 0), (7, 68), (12, imm % 4096), (5, rn), (5, rd)] =
      arm8AddSubImmediateWord sub false (BitVec.ofNat 12 (imm % 4096))
        (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  cases sub <;>
    · simp only [fields, List.foldl_cons, List.foldl_nil, arm8AddSubImmediateWord,
        bit_false, bit_true, holV2w_one_true, holV2w_one_false]
      rw [ofNat_mod_setWidth 1, ofNat_mod_setWidth 7, ofNat_mod_setWidth 12,
        ofNat_mod_setWidth 5, ofNat_mod_setWidth 5]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
        BitVec.getLsbD_append, BitVec.getLsbD_setWidth, Nat.testBit_mod_two_pow]
      interval_cases i <;> simp

/-- `fields` builds the low add/sub immediate word (with flags). -/
theorem fields_addSubImmediateS_low (sub : Bool) (imm rn rd : Nat) :
    fields [(1, 1), (1, bit sub), (1, 1), (7, 68), (12, imm % 4096), (5, rn), (5, rd)] =
      arm8AddSubImmediateWordS sub false (BitVec.ofNat 12 (imm % 4096))
        (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  cases sub <;>
    · simp only [fields, List.foldl_cons, List.foldl_nil, arm8AddSubImmediateWordS,
        bit_false, bit_true, holV2w_one_true, holV2w_one_false]
      rw [ofNat_mod_setWidth 1, ofNat_mod_setWidth 7, ofNat_mod_setWidth 12,
        ofNat_mod_setWidth 5, ofNat_mod_setWidth 5]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
        BitVec.getLsbD_append, BitVec.getLsbD_setWidth, Nat.testBit_mod_two_pow]
      interval_cases i <;> simp

/-- `fields` builds the shifted add/sub immediate word (no flags). -/
theorem fields_addSubImmediate_high (sub : Bool) (imm rn rd : Nat) :
    fields [(1, 1), (1, bit sub), (1, 0), (7, 69), (12, imm % 4096), (5, rn), (5, rd)] =
      arm8AddSubImmediateWord sub true (BitVec.ofNat 12 (imm % 4096))
        (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  cases sub <;>
    · simp only [fields, List.foldl_cons, List.foldl_nil, arm8AddSubImmediateWord,
        bit_false, bit_true, holV2w_one_true, holV2w_one_false]
      rw [ofNat_mod_setWidth 1, ofNat_mod_setWidth 7, ofNat_mod_setWidth 12,
        ofNat_mod_setWidth 5, ofNat_mod_setWidth 5]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
        BitVec.getLsbD_append, BitVec.getLsbD_setWidth, Nat.testBit_mod_two_pow]
      interval_cases i <;> simp

/-- `fields` builds the shifted add/sub immediate word (with flags). -/
theorem fields_addSubImmediateS_high (sub : Bool) (imm rn rd : Nat) :
    fields [(1, 1), (1, bit sub), (1, 1), (7, 69), (12, imm % 4096), (5, rn), (5, rd)] =
      arm8AddSubImmediateWordS sub true (BitVec.ofNat 12 (imm % 4096))
        (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  cases sub <;>
    · simp only [fields, List.foldl_cons, List.foldl_nil, arm8AddSubImmediateWordS,
        bit_false, bit_true, holV2w_one_true, holV2w_one_false]
      rw [ofNat_mod_setWidth 1, ofNat_mod_setWidth 7, ofNat_mod_setWidth 12,
        ofNat_mod_setWidth 5, ofNat_mod_setWidth 5]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
        BitVec.getLsbD_append, BitVec.getLsbD_setWidth, Nat.testBit_mod_two_pow]
      interval_cases i <;> simp

/-- The add/subtract immediate encodes to the same four bytes on both sides. -/
theorem encodeBytes_addSubImmediate (sub setFlags : Bool) (imm : BitVec 64) (rn rd : Nat) :
    encodeBytes (.addSubImmediate sub setFlags imm rn rd) =
      arm8Encode (.Data (.«AddSubImmediate@64»
        ((1 : BitVec 64), sub, setFlags, imm, BitVec.ofNat 5 rn, BitVec.ofNat 5 rd))) := by
  by_cases hlow : imm &&& (~~~(0xFFF : BitVec 64)) = 0
  · have hw : encodeInsn32 (.addSubImmediate sub setFlags imm rn rd) =
        some (fields [(1, 1), (1, bit sub), (1, bit setFlags), (7, 68),
          (12, imm.toNat % 4096), (5, rn), (5, rd)]) := by
      simp only [encodeInsn32]
      rw [if_pos hlow]
    cases setFlags
    · rw [encodeBytes_eq_of_encodeInsn32 _ _ hw]
      simp only [arm8Encode, arm8Encode_addSubImmediate_low sub imm (BitVec.ofNat 5 rn)
        (BitVec.ofNat 5 rd) hlow, fields_addSubImmediate_low, imm12Word_eq, bit_false]
    · rw [encodeBytes_eq_of_encodeInsn32 _ _ hw]
      simp only [arm8Encode, arm8Encode_addSubImmediateS_low sub imm (BitVec.ofNat 5 rn)
        (BitVec.ofNat 5 rd) hlow, fields_addSubImmediateS_low, imm12Word_eq, bit_true]
  · by_cases hhigh : imm &&& (~~~(0xFFF000 : BitVec 64)) = 0
    · have hw : encodeInsn32 (.addSubImmediate sub setFlags imm rn rd) =
          some (fields [(1, 1), (1, bit sub), (1, bit setFlags), (7, 69),
            (12, (imm >>> (12 : Nat)).toNat % 4096), (5, rn), (5, rd)]) := by
        simp only [encodeInsn32]
        rw [if_neg hlow, if_pos hhigh]
        simp
      cases setFlags
      · rw [encodeBytes_eq_of_encodeInsn32 _ _ hw]
        simp only [arm8Encode, arm8Encode_addSubImmediate_high sub imm (BitVec.ofNat 5 rn)
          (BitVec.ofNat 5 rd) (by simpa using hlow) hhigh, fields_addSubImmediate_high,
          imm12Word_shift_eq, bit_false]
      · rw [encodeBytes_eq_of_encodeInsn32 _ _ hw]
        simp only [arm8Encode, arm8Encode_addSubImmediateS_high sub imm (BitVec.ofNat 5 rn)
          (BitVec.ofNat 5 rd) (by simpa using hlow) hhigh, fields_addSubImmediateS_high,
          imm12Word_shift_eq, bit_true]
    · have hw : encodeInsn32 (.addSubImmediate sub setFlags imm rn rd) = none := by
        simp only [encodeInsn32]
        rw [if_neg hlow, if_neg hhigh]
      have hlow' : ¬ ((imm &&& ~~~(4095 : BitVec 64)) == (0 : BitVec 64)) = true := by
        intro h
        exact absurd (beq_iff_eq.mp h) hlow
      have hhigh' : ¬ ((imm &&& ~~~(16773120 : BitVec 64)) == (0 : BitVec 64)) = true := by
        intro h
        exact absurd (beq_iff_eq.mp h) hhigh
      rw [encodeBytes_eq_of_encodeInsn32_none _ hw]
      cases setFlags
      · simp only [arm8Encode, Encode, arm8EData_addSubImmediate, hlow', hhigh',
          Bool.false_eq_true, if_false]
      · simp only [arm8Encode, Encode, arm8EData_addSubImmediateS, hlow', hhigh',
          Bool.false_eq_true, if_false]

/-- A 64-bit immediate fits the five-bit `ConditionalCompareImmediate` field
exactly when it is the truncation of its own low five bits. -/
theorem fits5_iff (imm : BitVec 64) :
    imm.toNat < 32 ↔ imm = BitVec.setWidth 64 (BitVec.setWidth 5 imm) := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    omega
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth] at this
    omega

/-- `BitVec.setWidth` at a `Nat` argument is `BitVec.ofNat` of its `toNat`. -/
theorem setWidth_eq_ofNat (w : Nat) (v : BitVec 64) :
    BitVec.setWidth w v = BitVec.ofNat w v.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- `fields` builds the conditional-compare immediate word. -/
theorem fields_conditionalCompare (opc : Bool) (imm cd rn : Nat) (n z c v : Bool) :
    fields [(1, 1), (1, bit opc), (9, 466), (5, imm), (4, cd), (2, 2), (5, rn), (1, 0),
      (4, bit n * 8 + bit z * 4 + bit c * 2 + bit v)] =
      arm8ConditionalCompareWord opc (BitVec.ofNat 5 imm) (BitVec.ofNat 4 cd)
        n z c v (BitVec.ofNat 5 rn) := by
  cases opc <;> cases n <;> cases z <;> cases c <;> cases v <;>
    · simp only [fields, List.foldl_cons, List.foldl_nil, arm8ConditionalCompareWord,
        bit_false, bit_true, holV2w_one_true, holV2w_one_false]
      rw [ofNat_mod_setWidth 1, ofNat_mod_setWidth 9, ofNat_mod_setWidth 5,
        ofNat_mod_setWidth 4, ofNat_mod_setWidth 2, ofNat_mod_setWidth 5, ofNat_mod_setWidth 1]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
        BitVec.getLsbD_append, BitVec.getLsbD_setWidth, Nat.testBit_mod_two_pow]
      interval_cases i <;> simp <;> decide

/-- The conditional-compare immediate encodes to the same four bytes on both
sides. -/
theorem encodeBytes_conditionalCompareImmediate (opc : Bool) (imm : BitVec 64) (cd : Nat)
    (nzcv : Bool × Bool × Bool × Bool) (rn : Nat) :
    encodeBytes (.conditionalCompareImmediate opc imm cd nzcv rn) =
      arm8Encode (.Data (.«ConditionalCompareImmediate@64»
        ((1 : BitVec 64), (opc, (imm, (BitVec.ofNat 4 cd, (nzcv, BitVec.ofNat 5 rn))))))) := by
  obtain ⟨n, z, c, v⟩ := nzcv
  by_cases h : imm.toNat < 32
  · have hfit : (imm == BitVec.setWidth 64 (BitVec.setWidth 5 imm)) = true := by
      rw [beq_iff_eq]
      exact (fits5_iff imm).mp h
    have hw : encodeInsn32 (.conditionalCompareImmediate opc imm cd (n, z, c, v) rn) =
        some (fields [(1, 1), (1, bit opc), (9, 466), (5, imm.toNat), (4, cd), (2, 2),
          (5, rn), (1, 0), (4, bit n * 8 + bit z * 4 + bit c * 2 +
            bit v)]) := by
      simp only [encodeInsn32]
      rw [if_pos h]
    rw [encodeBytes_eq_of_encodeInsn32 _ _ hw]
    simp only [arm8Encode, arm8Encode_conditionalCompare, hfit, if_true,
      fields_conditionalCompare]
    rfl
  · have hfit : (imm == BitVec.setWidth 64 (BitVec.ofNat 5 imm.toNat)) = false := by
      rw [Bool.eq_false_iff]
      intro he
      rw [← setWidth_eq_ofNat 5 imm, beq_iff_eq] at he
      exact h ((fits5_iff imm).mpr he)
    have hw : encodeInsn32 (.conditionalCompareImmediate opc imm cd (n, z, c, v) rn) = none := by
      simp only [encodeInsn32]
      rw [if_neg h]
    rw [encodeBytes_eq_of_encodeInsn32_none _ hw]
    simp only [arm8Encode, arm8Encode_conditionalCompare, hfit, setWidth_eq_ofNat,
      Bool.false_eq_true, if_false]

end Flapjack.Compiler.Encoders.Arm8.L3
