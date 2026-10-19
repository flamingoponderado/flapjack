/-
Copyright (c) 2025 Flapjack contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.IntervalCases
import Flapjack.Compiler.Encoders.Arm8.Machine.DecodeProofSimple2
import Flapjack.Compiler.Encoders.Arm8.TargetProof

/-!
# ARMv8 decoder inverses: conditional encoders

Decoder inverses for the emitted instruction forms whose `encodeInsn32` guards
the word with a side condition on a field: `addSubImmediate` (two immediate
shapes), `logicalShiftedRegister` (an `encodeLogicalOp` match and a bound on the
shift amount), `logicalImmediate` (an `encodeBitMask` match) and `bitfieldMove`
(a `bitfieldOpBits` match).

Each inverse is stated with the bound hypotheses that make the encoder's guard
succeed, and the two successful `addSubImmediate` shapes are separated.  Bit
facts are proved by extensionality over `getLsbD` and `interval_cases`; the
`Nat` facts about `toNat`, `%`, `/` and `<<<` use `Nat.mod_eq_of_lt`,
`Nat.div_lt_of_lt_mul`, `Nat.div_mul_cancel` and `omega`, never a native
decision procedure.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm

/-! ## Clearing the low bits of a word

`encodeInsn32` tests immediates with `imm &&& ~~~(0xFFF : W) = 0` and
`imm &&& ~~~(0xFFF000 : W) = 0`.  A value that fits in the corresponding number
of bits is killed by such a mask. -/

/-- A `64`-bit word whose value fits in `k` bits is killed by `~~~(2^k - 1)`. -/
theorem and_not_low_eq_zero (k : Nat) (w : BitVec 64) (h : w.toNat < 2 ^ k) :
    w &&& ~~~(BitVec.ofNat 64 (2 ^ k - 1)) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hmask : (BitVec.ofNat 64 (2 ^ k - 1)).getLsbD i = decide (i < k) := by
    rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
    simp [hi]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hmask]
  by_cases hik : i < k
  · simp [hik]
  · have hlt : w.toNat < 2 ^ i := by
      have hle : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hb : w.getLsbD i = false := Nat.testBit_lt_two_pow hlt
    simp [hik, hb]

/-- The `12`-bit immediate shape of `encodeInsn32` is selected below `4096`. -/
theorem and_not_fff_eq_zero (w : BitVec 64) (h : w.toNat < 4096) :
    w &&& ~~~(0xFFF : W) = 0 :=
  and_not_low_eq_zero 12 w h

/-- A multiple of `4096` below `2^24` is killed by `~~~(0xFFF000)`: its low
twelve bits vanish by construction and its high bits by the bound. -/
theorem and_not_fff000_eq_zero_shifted (m : Nat) (hm : m < 4096) :
    BitVec.ofNat 64 (m <<< 12) &&& ~~~(BitVec.ofNat 64 ((2 ^ 12 - 1) <<< 12)) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ofNat,
    Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h12 : 12 ≤ i
  · by_cases h24 : i < 24
    · have hmid : i - 12 < 12 := by omega
      simp [h12, hmid]
    · have hfar : ¬ i - 12 < 12 := by omega
      have hz : m.testBit (i - 12) = false := by
        apply Nat.testBit_lt_two_pow
        have hle : 2 ^ 12 ≤ 2 ^ (i - 12) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      simp [h12, hfar, hz]
  · simp [h12]

/-- A shifted twelve-bit value keeps all of its bits under `~~~(0xFFF)`, since
its low twelve bits are zero already. -/
theorem and_not_fff_eq_self_shifted (m : Nat) :
    BitVec.ofNat 64 (m <<< 12) &&& ~~~(BitVec.ofNat 64 (2 ^ 12 - 1)) =
      BitVec.ofNat 64 (m <<< 12) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ofNat,
    Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h12 : 12 ≤ i
  · have hfar : ¬ i < 12 := by omega
    simp [h12, hfar]
    exact fun h _ => h
  · simp [h12]

/-! ## `addSubImmediate`, `imm12` shape (bit 22 zero) -/

/-- The 32-bit word of an `addSubImmediate` instruction with an unshifted
`imm12` field, over width-typed atoms. -/
def addSubImmediateWord (sub sf : BitVec 1) (imm12 : BitVec 12) (rn rd : BitVec 5) : BitVec 32 :=
  ((((((((0 : BitVec 32) <<< 1 ||| (1 : BitVec 32)) <<< 1 ||| sub.setWidth 32) <<< 1 |||
      sf.setWidth 32) <<< 7 ||| (68 : BitVec 32)) <<< 12 ||| imm12.setWidth 32) <<< 5 |||
      rn.setWidth 32) <<< 5 ||| rd.setWidth 32)

/-- The `fields` composition of an unshifted `addSubImmediate` is the
width-typed word. -/
theorem fields_addSubImmediate (sub setFlags : Bool) (imm rn rd : Nat) :
    fields [(1, 1), (1, bit sub), (1, bit setFlags), (7, 0b1000100), (12, imm),
      (5, rn), (5, rd)]
      = addSubImmediateWord (BitVec.ofNat 1 (bit sub)) (BitVec.ofNat 1 (bit setFlags))
          (BitVec.ofNat 12 imm) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

/-- Decode the width-typed unshifted `addSubImmediate` word. -/
theorem decode_addSubImmediate_word (sub sf : BitVec 1) (imm12 : BitVec 12)
    (rn rd : BitVec 5) :
    decodeInsn32 (addSubImmediateWord sub sf imm12 rn rd)
      = some (.addSubImmediate (sub.toNat = 1) (sf.toNat = 1)
          (BitVec.ofNat 64 imm12.toNat) rn.toNat rd.toNat) := by
  simp only [decodeInsn32]
  have h1 : bitMatches (addSubImmediateWord sub sf imm12 rn rd) 0xFFFFFFFF 0xD503201F
      = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [addSubImmediateWord] at hb
    simp at hb
  have h2 : bitMatches (addSubImmediateWord sub sf imm12 rn rd) 0x9F800000 0x92800000
      = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [addSubImmediateWord] at hb
    simp at hb
  have hK : bitMatches (addSubImmediateWord sub sf imm12 rn rd) 0x9F800000 0x91000000
      = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubImmediateWord]
    simp
    interval_cases i <;> simp
  simp only [h1, h2, hK, Bool.false_eq_true, if_true, if_false]
  have hsh : part (addSubImmediateWord sub sf imm12 rn rd) 22 1 = 0 := by
    have hz : ((addSubImmediateWord sub sf imm12 rn rd) >>> 22).setWidth 1 = 0 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [addSubImmediateWord]
      simp
      interval_cases i
      simp
    show (((addSubImmediateWord sub sf imm12 rn rd) >>> 22).setWidth 1).toNat = 0
    rw [hz]
    rfl
  have f1 : part (addSubImmediateWord sub sf imm12 rn rd) 30 1 = sub.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubImmediateWord]
    simp
    interval_cases i
    simp
  have f2 : part (addSubImmediateWord sub sf imm12 rn rd) 29 1 = sf.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubImmediateWord]
    simp
    interval_cases i
    simp
  have f3 : part (addSubImmediateWord sub sf imm12 rn rd) 10 12 = imm12.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubImmediateWord]
    simp
    interval_cases i <;> simp
  have f4 : part (addSubImmediateWord sub sf imm12 rn rd) 5 5 = rn.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubImmediateWord]
    simp
    interval_cases i <;> simp
  have f5 : part (addSubImmediateWord sub sf imm12 rn rd) 0 5 = rd.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubImmediateWord]
    simp
  simp [hsh, f1, f2, f3, f4, f5]

/-- The unshifted `imm12` immediate decodes back from the encoder's word. -/
theorem decode_encode_addSubImmediate32 (sub setFlags : Bool) (imm : W) (rn rd : Nat)
    (himm : imm.toNat < 4096) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn32 (fields [(1, 1), (1, bit sub), (1, bit setFlags), (7, 0b1000100),
      (12, imm.toNat % 4096), (5, rn), (5, rd)])
      = some (.addSubImmediate sub setFlags imm rn rd) := by
  rw [fields_addSubImmediate sub setFlags (imm.toNat % 4096) rn rd,
    decode_addSubImmediate_word]
  have h12 : (BitVec.ofNat 12 (imm.toNat % 4096)).toNat = imm.toNat % 4096 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]
  have hmod : imm.toNat % 4096 = imm.toNat := Nat.mod_eq_of_lt himm
  have hof : BitVec.ofNat 64 (imm.toNat % 4096) = imm := by
    rw [hmod, BitVec.ofNat_toNat]
    exact BitVec.setWidth_eq imm
  simp only [h12, hof]
  cases sub <;> cases setFlags <;>
    simp [bit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrn, Nat.mod_eq_of_lt hrd]

/-- The 64-bit carrier word emitted for an unshifted `addSubImmediate`. -/
theorem encodeInsn_addSubImmediate (sub setFlags : Bool) (imm : W) (rn rd : Nat)
    (himm : imm.toNat < 4096) :
    encodeInsn (.addSubImmediate sub setFlags imm rn rd) =
      some ((fields [(1, 1), (1, bit sub), (1, bit setFlags), (7, 0b1000100),
        (12, imm.toNat % 4096), (5, rn), (5, rd)]).setWidth 64) := by
  have hmask : imm &&& ~~~(0xFFF : W) = 0 := and_not_fff_eq_zero imm himm
  unfold encodeInsn
  simp only [encodeInsn32, if_pos hmask]
  rfl

/-- The 64-bit carrier form of the decoder inverts the encoder's carrier form. -/
theorem decode_encode_addSubImmediate (sub setFlags : Bool) (imm : W) (rn rd : Nat)
    (himm : imm.toNat < 4096) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((fields [(1, 1), (1, bit sub), (1, bit setFlags), (7, 0b1000100),
      (12, imm.toNat % 4096), (5, rn), (5, rd)]).setWidth 64)
      = some (.addSubImmediate sub setFlags imm rn rd) := by
  rw [show decodeInsn ((fields [(1, 1), (1, bit sub), (1, bit setFlags), (7, 0b1000100),
      (12, imm.toNat % 4096), (5, rn), (5, rd)]).setWidth 64)
      = decodeInsn32 (fields [(1, 1), (1, bit sub), (1, bit setFlags), (7, 0b1000100),
          (12, imm.toNat % 4096), (5, rn), (5, rd)]) by
    simp [decodeInsn]]
  exact decode_encode_addSubImmediate32 sub setFlags imm rn rd himm hrn hrd

/-- `decodeInsn` inverts `encodeInsn` on an unshifted `addSubImmediate`. -/
theorem decode_encode_addSubImmediateInsn (sub setFlags : Bool) (imm : W) (rn rd : Nat)
    (himm : imm.toNat < 4096) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((encodeInsn (.addSubImmediate sub setFlags imm rn rd)).getD 0)
      = some (.addSubImmediate sub setFlags imm rn rd) := by
  rw [encodeInsn_addSubImmediate sub setFlags imm rn rd himm, Option.getD_some]
  exact decode_encode_addSubImmediate sub setFlags imm rn rd himm hrn hrd

/-- One machine step executes an unshifted `addSubImmediate` whose bytes are at
the PC. -/
theorem arm8Next_addSubImmediate (s : Arm8State) (d : BitVec 64 → Prop)
    (sub setFlags : Bool) (imm : W) (rn rd : Nat)
    (himm : imm.toNat < 4096) (hrn : rn < 32) (hrd : rd < 32)
    (hbytes : bytesInMemoryHOL s.pc
      (encodeBytes (.addSubImmediate sub setFlags imm rn rd)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 }
      (.addSubImmediate sub setFlags imm rn rd) := by
  rw [arm8Next_encodeBytes s (.addSubImmediate sub setFlags imm rn rd)
    ((fields [(1, 1), (1, bit sub), (1, bit setFlags), (7, 0b1000100),
      (12, imm.toNat % 4096), (5, rn), (5, rd)]).setWidth 64) d
    (encodeInsn_addSubImmediate sub setFlags imm rn rd himm)
    (decode_encode_addSubImmediate sub setFlags imm rn rd himm hrn hrd) hbytes]

/-! ## `addSubImmediate`, shifted `imm12` shape (bit 22 set) -/

/-- The 32-bit word of an `addSubImmediate` instruction whose immediate is a
twelve-bit value shifted left by twelve, over width-typed atoms. -/
def addSubImmediateShiftedWord (sub sf : BitVec 1) (imm12 : BitVec 12) (rn rd : BitVec 5) :
    BitVec 32 :=
  ((((((((0 : BitVec 32) <<< 1 ||| (1 : BitVec 32)) <<< 1 ||| sub.setWidth 32) <<< 1 |||
      sf.setWidth 32) <<< 7 ||| (69 : BitVec 32)) <<< 12 ||| imm12.setWidth 32) <<< 5 |||
      rn.setWidth 32) <<< 5 ||| rd.setWidth 32)

/-- The `fields` composition of a shifted `addSubImmediate` is the width-typed
word. -/
theorem fields_addSubImmediateShifted (sub setFlags : Bool) (imm rn rd : Nat) :
    fields [(1, 1), (1, bit sub), (1, bit setFlags), (7, 0b1000101), (12, imm),
      (5, rn), (5, rd)]
      = addSubImmediateShiftedWord (BitVec.ofNat 1 (bit sub))
          (BitVec.ofNat 1 (bit setFlags)) (BitVec.ofNat 12 imm) (BitVec.ofNat 5 rn)
          (BitVec.ofNat 5 rd) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

/-- Decode the width-typed shifted `addSubImmediate` word. -/
theorem decode_addSubImmediateShifted_word (sub sf : BitVec 1) (imm12 : BitVec 12)
    (rn rd : BitVec 5) :
    decodeInsn32 (addSubImmediateShiftedWord sub sf imm12 rn rd)
      = some (.addSubImmediate (sub.toNat = 1) (sf.toNat = 1)
          (BitVec.ofNat 64 (imm12.toNat <<< 12)) rn.toNat rd.toNat) := by
  simp only [decodeInsn32]
  have h1 : bitMatches (addSubImmediateShiftedWord sub sf imm12 rn rd) 0xFFFFFFFF
      0xD503201F = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [addSubImmediateShiftedWord] at hb
    simp at hb
  have h2 : bitMatches (addSubImmediateShiftedWord sub sf imm12 rn rd) 0x9F800000
      0x92800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [addSubImmediateShiftedWord] at hb
    simp at hb
  have hK : bitMatches (addSubImmediateShiftedWord sub sf imm12 rn rd) 0x9F800000
      0x91000000 = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubImmediateShiftedWord]
    simp
    interval_cases i <;> simp
  simp only [h1, h2, hK, Bool.false_eq_true, if_true, if_false]
  have hsh : part (addSubImmediateShiftedWord sub sf imm12 rn rd) 22 1 = 1 := by
    have hz : ((addSubImmediateShiftedWord sub sf imm12 rn rd) >>> 22).setWidth 1 = 1 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [addSubImmediateShiftedWord]
      simp
      interval_cases i
      simp
    show (((addSubImmediateShiftedWord sub sf imm12 rn rd) >>> 22).setWidth 1).toNat = 1
    rw [hz]
    rfl
  have f1 : part (addSubImmediateShiftedWord sub sf imm12 rn rd) 30 1 = sub.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubImmediateShiftedWord]
    simp
    interval_cases i
    simp
  have f2 : part (addSubImmediateShiftedWord sub sf imm12 rn rd) 29 1 = sf.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubImmediateShiftedWord]
    simp
    interval_cases i
    simp
  have f3 : part (addSubImmediateShiftedWord sub sf imm12 rn rd) 10 12 = imm12.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubImmediateShiftedWord]
    simp
    interval_cases i <;> simp
  have f4 : part (addSubImmediateShiftedWord sub sf imm12 rn rd) 5 5 = rn.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubImmediateShiftedWord]
    simp
    interval_cases i <;> simp
  have f5 : part (addSubImmediateShiftedWord sub sf imm12 rn rd) 0 5 = rd.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubImmediateShiftedWord]
    simp
  simp [hsh, f1, f2, f3, f4, f5]

/-- The shifted immediate `imm12 <<< 12` decodes back from the encoder's word. -/
theorem decode_encode_addSubImmediateShifted32 (sub setFlags : Bool) (m rn rd : Nat)
    (hm : m < 4096) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn32 (fields [(1, 1), (1, bit sub), (1, bit setFlags), (7, 0b1000101),
      (12, m), (5, rn), (5, rd)])
      = some (.addSubImmediate sub setFlags (BitVec.ofNat 64 (m <<< 12)) rn rd) := by
  rw [fields_addSubImmediateShifted sub setFlags m rn rd,
    decode_addSubImmediateShifted_word]
  have h12 : (BitVec.ofNat 12 m).toNat = m := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
  simp only [h12]
  cases sub <;> cases setFlags <;>
    simp [bit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrn, Nat.mod_eq_of_lt hrd]

/-- The 64-bit carrier word emitted for a shifted `addSubImmediate`. -/
theorem encodeInsn_addSubImmediateShifted (sub setFlags : Bool) (m rn rd : Nat)
    (hm : m < 4096) (hm0 : m ≠ 0) :
    encodeInsn (.addSubImmediate sub setFlags (BitVec.ofNat 64 (m <<< 12)) rn rd) =
      some ((fields [(1, 1), (1, bit sub), (1, bit setFlags), (7, 0b1000101),
        (12, m), (5, rn), (5, rd)]).setWidth 64) := by
  have hlt : m <<< 12 < 2 ^ 64 := by
    have h24 : m <<< 12 < 2 ^ 24 := by
      rw [Nat.shiftLeft_eq]
      omega
    omega
  have htoNat : (BitVec.ofNat 64 (m <<< 12)).toNat = m <<< 12 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have himm0 : BitVec.ofNat 64 (m <<< 12) ≠ 0 := by
    intro h
    apply hm0
    have hz := congrArg BitVec.toNat h
    simpa [htoNat] using hz
  have hguard1 : (BitVec.ofNat 64 (m <<< 12)) &&& ~~~(0xFFF : W) ≠ 0 := by
    have hme : ~~~(0xFFF : W) = ~~~(BitVec.ofNat 64 (2 ^ 12 - 1)) := rfl
    rw [hme, and_not_fff_eq_self_shifted m]
    exact himm0
  have hguard2 : (BitVec.ofNat 64 (m <<< 12)) &&& ~~~(0xFFF000 : W) = 0 :=
    and_not_fff000_eq_zero_shifted m hm
  have hfield : ((BitVec.ofNat 64 (m <<< 12)) >>> 12).toNat % 4096 = m := by
    have hshift : ((BitVec.ofNat 64 (m <<< 12)) >>> 12).toNat
        = (BitVec.ofNat 64 (m <<< 12)).toNat >>> 12 :=
      BitVec.toNat_ushiftRight _ 12
    rw [hshift, htoNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    rw [Nat.mul_div_cancel _ (by norm_num : 0 < 2 ^ 12)]
    exact Nat.mod_eq_of_lt hm
  unfold encodeInsn
  simp only [encodeInsn32, if_neg hguard1, if_pos hguard2, hfield]
  rfl

/-- The 64-bit carrier form of the decoder inverts the encoder's carrier form
for a shifted `addSubImmediate`. -/
theorem decode_encode_addSubImmediateShifted (sub setFlags : Bool) (m rn rd : Nat)
    (hm : m < 4096) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((fields [(1, 1), (1, bit sub), (1, bit setFlags), (7, 0b1000101),
      (12, m), (5, rn), (5, rd)]).setWidth 64)
      = some (.addSubImmediate sub setFlags (BitVec.ofNat 64 (m <<< 12)) rn rd) := by
  rw [show decodeInsn ((fields [(1, 1), (1, bit sub), (1, bit setFlags), (7, 0b1000101),
      (12, m), (5, rn), (5, rd)]).setWidth 64)
      = decodeInsn32 (fields [(1, 1), (1, bit sub), (1, bit setFlags), (7, 0b1000101),
          (12, m), (5, rn), (5, rd)]) by
    simp [decodeInsn]]
  exact decode_encode_addSubImmediateShifted32 sub setFlags m rn rd hm hrn hrd

/-- `decodeInsn` inverts `encodeInsn` on a shifted `addSubImmediate`. -/
theorem decode_encode_addSubImmediateShiftedInsn (sub setFlags : Bool) (m rn rd : Nat)
    (hm : m < 4096) (hm0 : m ≠ 0) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((encodeInsn (.addSubImmediate sub setFlags (BitVec.ofNat 64 (m <<< 12))
      rn rd)).getD 0)
      = some (.addSubImmediate sub setFlags (BitVec.ofNat 64 (m <<< 12)) rn rd) := by
  rw [encodeInsn_addSubImmediateShifted sub setFlags m rn rd hm hm0, Option.getD_some]
  exact decode_encode_addSubImmediateShifted sub setFlags m rn rd hm hrn hrd

/-- One machine step executes a shifted `addSubImmediate` whose bytes are at the
PC. -/
theorem arm8Next_addSubImmediateShifted (s : Arm8State) (d : BitVec 64 → Prop)
    (sub setFlags : Bool) (m rn rd : Nat)
    (hm : m < 4096) (hm0 : m ≠ 0) (hrn : rn < 32) (hrd : rd < 32)
    (hbytes : bytesInMemoryHOL s.pc
      (encodeBytes (.addSubImmediate sub setFlags (BitVec.ofNat 64 (m <<< 12)) rn rd))
      s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 }
      (.addSubImmediate sub setFlags (BitVec.ofNat 64 (m <<< 12)) rn rd) := by
  rw [arm8Next_encodeBytes s
    (.addSubImmediate sub setFlags (BitVec.ofNat 64 (m <<< 12)) rn rd)
    ((fields [(1, 1), (1, bit sub), (1, bit setFlags), (7, 0b1000101),
      (12, m), (5, rn), (5, rd)]).setWidth 64) d
    (encodeInsn_addSubImmediateShifted sub setFlags m rn rd hm hm0)
    (decode_encode_addSubImmediateShifted sub setFlags m rn rd hm hrn hrd) hbytes]

/-- The documented `encodeInsn32` shape for a shifted immediate: an `imm` whose
low twelve bits vanish, which is nonzero and fits in twenty-four bits, encodes
the `bit22 = 1` word and is recovered by `decodeInsn`. -/
theorem decode_encode_addSubImmediateModInsn (sub setFlags : Bool) (imm : W) (rn rd : Nat)
    (hhi : imm.toNat < 0x1000000) (hlo : imm.toNat % 4096 = 0) (hne : imm.toNat ≠ 0)
    (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((encodeInsn (.addSubImmediate sub setFlags imm rn rd)).getD 0)
      = some (.addSubImmediate sub setFlags imm rn rd) := by
  have hdm : imm.toNat / 4096 * 4096 = imm.toNat :=
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hlo)
  have hshape : imm = BitVec.ofNat 64 ((imm.toNat / 4096) <<< 12) := by
    rw [Nat.shiftLeft_eq, hdm, BitVec.ofNat_toNat]
    exact (BitVec.setWidth_eq imm)
  have hm : imm.toNat / 4096 < 4096 := Nat.div_lt_of_lt_mul hhi
  have hm0 : imm.toNat / 4096 ≠ 0 := by
    intro h
    apply hne
    rw [← hdm, h, Nat.zero_mul]
  rw [hshape]
  exact decode_encode_addSubImmediateShiftedInsn sub setFlags (imm.toNat / 4096) rn rd
    hm hm0 hrn hrd

/-! ## `logicalShiftedRegister`

The encoder resolves the operation with `encodeLogicalOp` (which fails for the
flag-setting `orr`/`eor` forms) and requires a six-bit shift amount below `64`.
The decoder reads the opcode back through `decodeLogicalOp`, so the inverse is
stated for a word whose opcode field is `encodeLogicalOp op setFlags`. -/

/-- `decodeLogicalOp` inverts `encodeLogicalOp`. -/
theorem decodeLogicalOp_encodeLogicalOp (op : LogicalOp) (setFlags : Bool) (opc : Nat)
    (h : encodeLogicalOp op setFlags = some opc) :
    decodeLogicalOp opc = some (op, setFlags) := by
  cases op <;> cases setFlags <;> simp only [encodeLogicalOp] at h <;> (cases h <;> rfl)

/-- The opcode emitted by `encodeLogicalOp` fits in the two-bit field. -/
theorem encodeLogicalOp_lt (op : LogicalOp) (setFlags : Bool) (opc : Nat)
    (h : encodeLogicalOp op setFlags = some opc) : opc < 4 := by
  cases op <;> cases setFlags <;> simp only [encodeLogicalOp] at h <;> (cases h <;> simp)

/-- `decodeShift` inverts `shiftTypeBits`. -/
theorem decodeShift_shiftTypeBits (shift : ShiftType) :
    decodeShift (shiftTypeBits shift) = shift := by
  cases shift <;> rfl

/-- A one-bit field encoding a boolean decodes back to that boolean. -/
theorem decide_bit_eq_one (b : Bool) : decide (bit b = 1) = b := by
  cases b <;> rfl

/-- The 32-bit word of a `logicalShiftedRegister` instruction, over width-typed
atoms. -/
def logicalShiftedRegisterWord (opc : BitVec 2) (sh : BitVec 2) (inv : BitVec 1)
    (rm : BitVec 5) (imm : BitVec 6) (rn rd : BitVec 5) : BitVec 32 :=
  ((((((((((0 : BitVec 32) <<< 1 ||| (1 : BitVec 32)) <<< 2 ||| opc.setWidth 32) <<< 5 |||
      (10 : BitVec 32)) <<< 2 ||| sh.setWidth 32) <<< 1 ||| inv.setWidth 32) <<< 5 |||
      rm.setWidth 32) <<< 6 ||| imm.setWidth 32) <<< 5 ||| rn.setWidth 32) <<< 5 |||
      rd.setWidth 32)

/-- The `fields` composition of a `logicalShiftedRegister` is the width-typed
word. -/
theorem fields_logicalShiftedRegister (opc sh inv rm imm rn rd : Nat) :
    fields [(1, 1), (2, opc), (5, 0b01010), (2, sh), (1, inv), (5, rm), (6, imm),
      (5, rn), (5, rd)]
      = logicalShiftedRegisterWord (BitVec.ofNat 2 opc) (BitVec.ofNat 2 sh)
          (BitVec.ofNat 1 inv) (BitVec.ofNat 5 rm) (BitVec.ofNat 6 imm)
          (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

/-- Decode the width-typed `logicalShiftedRegister` word. -/
theorem decode_logicalShiftedRegister_word (op : LogicalOp) (sf : Bool) (opc : BitVec 2)
    (sh : BitVec 2) (inv : BitVec 1) (rm : BitVec 5) (imm : BitVec 6) (rn rd : BitVec 5)
    (hopc : decodeLogicalOp opc.toNat = some (op, sf)) :
    decodeInsn32 (logicalShiftedRegisterWord opc sh inv rm imm rn rd)
      = some (.logicalShiftedRegister op (inv.toNat = 1) sf (decodeShift sh.toNat)
          imm.toNat rm.toNat rn.toNat rd.toNat) := by
  simp only [decodeInsn32]
  have h1 : bitMatches (logicalShiftedRegisterWord opc sh inv rm imm rn rd) 0xFFFFFFFF
      0xD503201F = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 28) h
    simp only [logicalShiftedRegisterWord] at hb
    simp at hb
  have h2 : bitMatches (logicalShiftedRegisterWord opc sh inv rm imm rn rd) 0x9F800000
      0x92800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 28) h
    simp only [logicalShiftedRegisterWord] at hb
    simp at hb
  have h3 : bitMatches (logicalShiftedRegisterWord opc sh inv rm imm rn rd) 0x9F800000
      0x91000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 28) h
    simp only [logicalShiftedRegisterWord] at hb
    simp at hb
  have h4 : bitMatches (logicalShiftedRegisterWord opc sh inv rm imm rn rd) 0x9F800000
      0x92000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 28) h
    simp only [logicalShiftedRegisterWord] at hb
    simp at hb
  have hK : bitMatches (logicalShiftedRegisterWord opc sh inv rm imm rn rd) 0x9F000000
      0x8A000000 = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [logicalShiftedRegisterWord]
    simp
    interval_cases i <;> simp
  simp only [h1, h2, h3, h4, hK, Bool.false_eq_true, if_true, if_false]
  have f29 : part (logicalShiftedRegisterWord opc sh inv rm imm rn rd) 29 2
      = opc.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [logicalShiftedRegisterWord]
    simp
    interval_cases i <;> simp
  have f22 : part (logicalShiftedRegisterWord opc sh inv rm imm rn rd) 22 2
      = sh.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [logicalShiftedRegisterWord]
    simp
    interval_cases i <;> simp
  have f21 : part (logicalShiftedRegisterWord opc sh inv rm imm rn rd) 21 1
      = inv.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [logicalShiftedRegisterWord]
    simp
    interval_cases i
    simp
  have f16 : part (logicalShiftedRegisterWord opc sh inv rm imm rn rd) 16 5
      = rm.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [logicalShiftedRegisterWord]
    simp
    interval_cases i <;> simp
  have f10 : part (logicalShiftedRegisterWord opc sh inv rm imm rn rd) 10 6
      = imm.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [logicalShiftedRegisterWord]
    simp
    interval_cases i <;> simp
  have f5 : part (logicalShiftedRegisterWord opc sh inv rm imm rn rd) 5 5
      = rn.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [logicalShiftedRegisterWord]
    simp
    interval_cases i <;> simp
  have f0 : part (logicalShiftedRegisterWord opc sh inv rm imm rn rd) 0 5
      = rd.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [logicalShiftedRegisterWord]
    simp
  simp only [f29, hopc, f22, f21, f16, f10, f5, f0]

/-- The `logicalShiftedRegister` word decodes back to the encoded instruction. -/
theorem decode_encode_logicalShiftedRegister32 (op : LogicalOp) (invert setFlags : Bool)
    (shift : ShiftType) (imm rm rn rd : Nat) (opc : Nat)
    (hopc : encodeLogicalOp op setFlags = some opc) (himm : imm < 64)
    (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn32 (fields [(1, 1), (2, opc), (5, 0b01010), (2, shiftTypeBits shift),
      (1, bit invert), (5, rm), (6, imm), (5, rn), (5, rd)])
      = some (.logicalShiftedRegister op invert setFlags shift imm rm rn rd) := by
  have hopc2 : (BitVec.ofNat 2 opc).toNat = opc := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := encodeLogicalOp_lt op setFlags opc hopc
    omega
  rw [fields_logicalShiftedRegister opc (shiftTypeBits shift) (bit invert) rm imm rn rd,
    decode_logicalShiftedRegister_word op setFlags (BitVec.ofNat 2 opc)
      (BitVec.ofNat 2 (shiftTypeBits shift)) (BitVec.ofNat 1 (bit invert))
      (BitVec.ofNat 5 rm) (BitVec.ofNat 6 imm) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd)
      (by rw [hopc2]; exact decodeLogicalOp_encodeLogicalOp op setFlags opc hopc)]
  have hsh : (BitVec.ofNat 2 (shiftTypeBits shift)).toNat = shiftTypeBits shift := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    cases shift <;> simp [shiftTypeBits]
  have hinv : (BitVec.ofNat 1 (bit invert)).toNat = bit invert := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    cases invert <;> simp [bit]
  simp only [hsh, hinv, decodeShift_shiftTypeBits, decide_bit_eq_one,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt himm, Nat.mod_eq_of_lt hrm,
    Nat.mod_eq_of_lt hrn, Nat.mod_eq_of_lt hrd]

/-- The 64-bit carrier word emitted for a `logicalShiftedRegister`. -/
theorem encodeInsn_logicalShiftedRegister (op : LogicalOp) (invert setFlags : Bool)
    (shift : ShiftType) (imm rm rn rd : Nat) (opc : Nat)
    (hopc : encodeLogicalOp op setFlags = some opc) (himm : imm < 64) :
    encodeInsn (.logicalShiftedRegister op invert setFlags shift imm rm rn rd) =
      some ((fields [(1, 1), (2, opc), (5, 0b01010), (2, shiftTypeBits shift),
        (1, bit invert), (5, rm), (6, imm), (5, rn), (5, rd)]).setWidth 64) := by
  unfold encodeInsn
  simp only [encodeInsn32, hopc, if_pos himm]
  rfl

/-- The 64-bit carrier form of the decoder inverts the encoder's carrier form for
a `logicalShiftedRegister`. -/
theorem decode_encode_logicalShiftedRegister (op : LogicalOp) (invert setFlags : Bool)
    (shift : ShiftType) (imm rm rn rd : Nat) (opc : Nat)
    (hopc : encodeLogicalOp op setFlags = some opc) (himm : imm < 64)
    (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((fields [(1, 1), (2, opc), (5, 0b01010), (2, shiftTypeBits shift),
      (1, bit invert), (5, rm), (6, imm), (5, rn), (5, rd)]).setWidth 64)
      = some (.logicalShiftedRegister op invert setFlags shift imm rm rn rd) := by
  rw [show decodeInsn ((fields [(1, 1), (2, opc), (5, 0b01010),
      (2, shiftTypeBits shift), (1, bit invert), (5, rm), (6, imm), (5, rn),
      (5, rd)]).setWidth 64)
      = decodeInsn32 (fields [(1, 1), (2, opc), (5, 0b01010), (2, shiftTypeBits shift),
          (1, bit invert), (5, rm), (6, imm), (5, rn), (5, rd)]) by
    simp [decodeInsn]]
  exact decode_encode_logicalShiftedRegister32 op invert setFlags shift imm rm rn rd opc
    hopc himm hrm hrn hrd

/-- `decodeInsn` inverts `encodeInsn` on a `logicalShiftedRegister`. -/
theorem decode_encode_logicalShiftedRegisterInsn (op : LogicalOp) (invert setFlags : Bool)
    (shift : ShiftType) (imm rm rn rd : Nat) (opc : Nat)
    (hopc : encodeLogicalOp op setFlags = some opc) (himm : imm < 64)
    (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((encodeInsn (.logicalShiftedRegister op invert setFlags shift imm rm rn
      rd)).getD 0)
      = some (.logicalShiftedRegister op invert setFlags shift imm rm rn rd) := by
  rw [encodeInsn_logicalShiftedRegister op invert setFlags shift imm rm rn rd opc hopc
    himm, Option.getD_some]
  exact decode_encode_logicalShiftedRegister op invert setFlags shift imm rm rn rd opc
    hopc himm hrm hrn hrd

/-- One machine step executes a `logicalShiftedRegister` whose bytes are at the
PC. -/
theorem arm8Next_logicalShiftedRegister (s : Arm8State) (d : BitVec 64 → Prop)
    (op : LogicalOp) (invert setFlags : Bool) (shift : ShiftType) (imm rm rn rd : Nat)
    (opc : Nat) (hopc : encodeLogicalOp op setFlags = some opc) (himm : imm < 64)
    (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32)
    (hbytes : bytesInMemoryHOL s.pc
      (encodeBytes (.logicalShiftedRegister op invert setFlags shift imm rm rn rd))
      s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 }
      (.logicalShiftedRegister op invert setFlags shift imm rm rn rd) := by
  rw [arm8Next_encodeBytes s
    (.logicalShiftedRegister op invert setFlags shift imm rm rn rd)
    ((fields [(1, 1), (2, opc), (5, 0b01010), (2, shiftTypeBits shift),
      (1, bit invert), (5, rm), (6, imm), (5, rn), (5, rd)]).setWidth 64) d
    (encodeInsn_logicalShiftedRegister op invert setFlags shift imm rm rn rd opc hopc himm)
    (decode_encode_logicalShiftedRegister op invert setFlags shift imm rm rn rd opc hopc
      himm hrm hrn hrd) hbytes]

/-! ## `logicalImmediate`

The encoder resolves both the operation (`encodeLogicalOp`, `none` for the
flag-setting `orr`/`eor` forms) and the immediate (`encodeBitMask`, a search over
the bitmask encodings).  The decoder runs the search backwards with
`decodeBitMasks`, and `decodeEncodeBitMask` supplies the inverse. -/

/-- `decodeBitMasks` only inspects its `immN` argument modulo `2` and its `imms`
and `immr` arguments modulo `64`, so reducing those arguments changes nothing. -/
theorem decodeBitMasks_mod (N s r : Nat) (b : Bool) :
    decodeBitMasks (N % 2) (s % 64) (r % 64) b = decodeBitMasks N s r b := by
  simp only [decodeBitMasks, Nat.mod_mod]

/-- The 32-bit word of a `logicalImmediate` instruction, over width-typed
atoms. -/
def logicalImmediateWord (opc : BitVec 2) (nB : BitVec 1) (immrB immsB : BitVec 6)
    (rn rd : BitVec 5) : BitVec 32 :=
  (((((((((0 : BitVec 32) <<< 1 ||| (1 : BitVec 32)) <<< 2 ||| opc.setWidth 32)
      <<< 6 ||| (36 : BitVec 32)) <<< 1 ||| nB.setWidth 32) <<< 6 ||| immrB.setWidth 32)
      <<< 6 ||| immsB.setWidth 32) <<< 5 ||| rn.setWidth 32) <<< 5 ||| rd.setWidth 32)

/-- The `fields` composition of a `logicalImmediate` is the width-typed word. -/
theorem fields_logicalImmediate (opc n immr imms rn rd : Nat) :
    fields [(1, 1), (2, opc), (6, 0b100100), (1, n), (6, immr), (6, imms),
      (5, rn), (5, rd)]
      = logicalImmediateWord (BitVec.ofNat 2 opc) (BitVec.ofNat 1 n)
          (BitVec.ofNat 6 immr) (BitVec.ofNat 6 imms) (BitVec.ofNat 5 rn)
          (BitVec.ofNat 5 rd) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

/-- Decode the width-typed `logicalImmediate` word. -/
theorem decode_logicalImmediate_word (op : LogicalOp) (sf : Bool) (opc : BitVec 2)
    (nB : BitVec 1) (immrB immsB : BitVec 6) (rn rd : BitVec 5) (x v : Nat)
    (hopc : decodeLogicalOp opc.toNat = some (op, sf))
    (hbm : decodeBitMasks nB.toNat immsB.toNat immrB.toNat true = some (x, v)) :
    decodeInsn32 (logicalImmediateWord opc nB immrB immsB rn rd)
      = some (.logicalImmediate op sf (BitVec.ofNat 64 x) rn.toNat rd.toNat) := by
  simp only [decodeInsn32]
  have h1 : bitMatches (logicalImmediateWord opc nB immrB immsB rn rd) 0xFFFFFFFF
      0xD503201F = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [logicalImmediateWord] at hb
    simp at hb
  have h2 : bitMatches (logicalImmediateWord opc nB immrB immsB rn rd) 0x9F800000
      0x92800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [logicalImmediateWord] at hb
    simp at hb
  have h3 : bitMatches (logicalImmediateWord opc nB immrB immsB rn rd) 0x9F800000
      0x91000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [logicalImmediateWord] at hb
    simp at hb
  have hK : bitMatches (logicalImmediateWord opc nB immrB immsB rn rd) 0x9F800000
      0x92000000 = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [logicalImmediateWord]
    simp
    interval_cases i <;> simp
  simp only [h1, h2, h3, hK, Bool.false_eq_true, if_true, if_false]
  have f29 : part (logicalImmediateWord opc nB immrB immsB rn rd) 29 2 = opc.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [logicalImmediateWord]
    simp
    interval_cases i <;> simp
  have f22 : part (logicalImmediateWord opc nB immrB immsB rn rd) 22 1 = nB.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [logicalImmediateWord]
    simp
    interval_cases i
    simp
  have f16 : part (logicalImmediateWord opc nB immrB immsB rn rd) 16 6 = immrB.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [logicalImmediateWord]
    simp
    interval_cases i <;> simp
  have f10 : part (logicalImmediateWord opc nB immrB immsB rn rd) 10 6 = immsB.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [logicalImmediateWord]
    simp
    interval_cases i <;> simp
  have f5 : part (logicalImmediateWord opc nB immrB immsB rn rd) 5 5 = rn.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [logicalImmediateWord]
    simp
    interval_cases i <;> simp
  have f0 : part (logicalImmediateWord opc nB immrB immsB rn rd) 0 5 = rd.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [logicalImmediateWord]
    simp
  simp only [f29, hopc, f22, f16, f10, f5, f0, hbm]

/-- The `logicalImmediate` word decodes back to the encoded instruction. -/
theorem decode_encode_logicalImmediate32 (op : LogicalOp) (setFlags : Bool) (imm : W)
    (rn rd : Nat) (opc n imms immr : Nat)
    (hopc : encodeLogicalOp op setFlags = some opc)
    (hbm : encodeBitMask imm = some (n, imms, immr))
    (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn32 (fields [(1, 1), (2, opc), (6, 0b100100), (1, n), (6, immr),
      (6, imms), (5, rn), (5, rd)])
      = some (.logicalImmediate op setFlags imm rn rd) := by
  obtain ⟨v, hv⟩ := decodeEncodeBitMask imm n imms immr hbm
  have hopc2 : (BitVec.ofNat 2 opc).toNat = opc := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := encodeLogicalOp_lt op setFlags opc hopc
    omega
  have hn : (BitVec.ofNat 1 n).toNat = n % 2 := by rw [BitVec.toNat_ofNat]
  have himms : (BitVec.ofNat 6 imms).toNat = imms % 64 := by rw [BitVec.toNat_ofNat]
  have himmr : (BitVec.ofNat 6 immr).toNat = immr % 64 := by rw [BitVec.toNat_ofNat]
  have hbm' : decodeBitMasks (BitVec.ofNat 1 n).toNat (BitVec.ofNat 6 imms).toNat
      (BitVec.ofNat 6 immr).toNat true = some (imm.toNat, v) := by
    rw [hn, himms, himmr, decodeBitMasks_mod n imms immr true]
    exact hv
  rw [fields_logicalImmediate opc n immr imms rn rd,
    decode_logicalImmediate_word op setFlags (BitVec.ofNat 2 opc) (BitVec.ofNat 1 n)
      (BitVec.ofNat 6 immr) (BitVec.ofNat 6 imms) (BitVec.ofNat 5 rn)
      (BitVec.ofNat 5 rd) imm.toNat v
      (by rw [hopc2]; exact decodeLogicalOp_encodeLogicalOp op setFlags opc hopc) hbm']
  have hword : BitVec.ofNat 64 imm.toNat = imm := by
    rw [BitVec.ofNat_toNat]
    exact BitVec.setWidth_eq imm
  simp only [hword, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrn, Nat.mod_eq_of_lt hrd]

/-- The 64-bit carrier word emitted for a `logicalImmediate`. -/
theorem encodeInsn_logicalImmediate (op : LogicalOp) (setFlags : Bool) (imm : W)
    (rn rd : Nat) (opc n imms immr : Nat)
    (hopc : encodeLogicalOp op setFlags = some opc)
    (hbm : encodeBitMask imm = some (n, imms, immr)) :
    encodeInsn (.logicalImmediate op setFlags imm rn rd) =
      some ((fields [(1, 1), (2, opc), (6, 0b100100), (1, n), (6, immr), (6, imms),
        (5, rn), (5, rd)]).setWidth 64) := by
  unfold encodeInsn
  simp only [encodeInsn32, hbm, hopc]
  rfl

/-- The 64-bit carrier form of the decoder inverts the encoder's carrier form for
a `logicalImmediate`. -/
theorem decode_encode_logicalImmediate (op : LogicalOp) (setFlags : Bool) (imm : W)
    (rn rd : Nat) (opc n imms immr : Nat)
    (hopc : encodeLogicalOp op setFlags = some opc)
    (hbm : encodeBitMask imm = some (n, imms, immr))
    (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((fields [(1, 1), (2, opc), (6, 0b100100), (1, n), (6, immr), (6, imms),
      (5, rn), (5, rd)]).setWidth 64)
      = some (.logicalImmediate op setFlags imm rn rd) := by
  rw [show decodeInsn ((fields [(1, 1), (2, opc), (6, 0b100100), (1, n), (6, immr),
      (6, imms), (5, rn), (5, rd)]).setWidth 64)
      = decodeInsn32 (fields [(1, 1), (2, opc), (6, 0b100100), (1, n), (6, immr),
          (6, imms), (5, rn), (5, rd)]) by
    simp [decodeInsn]]
  exact decode_encode_logicalImmediate32 op setFlags imm rn rd opc n imms immr hopc hbm
    hrn hrd

/-- `decodeInsn` inverts `encodeInsn` on a `logicalImmediate`. -/
theorem decode_encode_logicalImmediateInsn (op : LogicalOp) (setFlags : Bool) (imm : W)
    (rn rd : Nat) (opc n imms immr : Nat)
    (hopc : encodeLogicalOp op setFlags = some opc)
    (hbm : encodeBitMask imm = some (n, imms, immr))
    (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((encodeInsn (.logicalImmediate op setFlags imm rn rd)).getD 0)
      = some (.logicalImmediate op setFlags imm rn rd) := by
  rw [encodeInsn_logicalImmediate op setFlags imm rn rd opc n imms immr hopc hbm,
    Option.getD_some]
  exact decode_encode_logicalImmediate op setFlags imm rn rd opc n imms immr hopc hbm
    hrn hrd

/-- One machine step executes a `logicalImmediate` whose bytes are at the PC. -/
theorem arm8Next_logicalImmediate (s : Arm8State) (d : BitVec 64 → Prop)
    (op : LogicalOp) (setFlags : Bool) (imm : W) (rn rd : Nat) (opc n imms immr : Nat)
    (hopc : encodeLogicalOp op setFlags = some opc)
    (hbm : encodeBitMask imm = some (n, imms, immr)) (hrn : rn < 32) (hrd : rd < 32)
    (hbytes : bytesInMemoryHOL s.pc
      (encodeBytes (.logicalImmediate op setFlags imm rn rd)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 }
      (.logicalImmediate op setFlags imm rn rd) := by
  rw [arm8Next_encodeBytes s (.logicalImmediate op setFlags imm rn rd)
    ((fields [(1, 1), (2, opc), (6, 0b100100), (1, n), (6, immr), (6, imms),
      (5, rn), (5, rd)]).setWidth 64) d
    (encodeInsn_logicalImmediate op setFlags imm rn rd opc n imms immr hopc hbm)
    (decode_encode_logicalImmediate op setFlags imm rn rd opc n imms immr hopc hbm
      hrn hrd) hbytes]

/-! ## `bitfieldMove`

The encoder resolves `(inzero, extend)` with `bitfieldOpBits`, which fails for the
`(false, true)` pair, and always emits a word with bit 22 set and a fixed opcode.
The decoder's mask covers the top bit of the `immr` field, so the inverse needs
`immr < 32`: the emitted encoding only roundtrips for widths below the register
size. -/

/-- The bitfield opcode emitted by `bitfieldOpBits` fits in its two-bit field. -/
theorem bitfieldOpBits_lt (inzero extend : Bool) (opc : Nat)
    (h : bitfieldOpBits inzero extend = some opc) : opc < 4 := by
  cases inzero <;> cases extend <;> simp only [bitfieldOpBits] at h <;> (cases h <;> simp)

/-- `decodeBitfieldOp` inverts `bitfieldOpBits`. -/
theorem decodeBitfieldOp_bitfieldOpBits (inzero extend : Bool) (opc : Nat)
    (h : bitfieldOpBits inzero extend = some opc) :
    decodeBitfieldOp opc = some (inzero, extend) := by
  cases inzero <;> cases extend <;> simp only [bitfieldOpBits] at h <;> (cases h <;> rfl)

/-- The 32-bit word of a `bitfieldMove` instruction, over width-typed atoms. -/
def bitfieldMoveWord (opc : BitVec 2) (immr6 imms : BitVec 6) (rn rd : BitVec 5) :
    BitVec 32 :=
(((((((((0 : BitVec 32) <<< 1 ||| (1 : BitVec 32)) <<< 2 ||| opc.setWidth 32)
      <<< 6 ||| (38 : BitVec 32)) <<< 1 ||| (1 : BitVec 32)) <<< 6 ||| immr6.setWidth 32)
      <<< 6 ||| imms.setWidth 32) <<< 5 ||| rn.setWidth 32) <<< 5 ||| rd.setWidth 32)

/-- The `fields` composition of a `bitfieldMove` is the width-typed word. -/
theorem fields_bitfieldMove (opc immr imms rn rd : Nat) :
    fields [(1, 1), (2, opc), (6, 0b100110), (1, 1), (6, immr), (6, imms),
      (5, rn), (5, rd)]
      = bitfieldMoveWord (BitVec.ofNat 2 opc) (BitVec.ofNat 6 immr)
          (BitVec.ofNat 6 imms) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

/-- Decode the width-typed `bitfieldMove` word.  The mask pins the top bit of the
`immr` field to zero, hence the bound on the rotated width. -/
theorem decode_bitfieldMove_word (inzero extend : Bool) (opc : BitVec 2)
    (immr6 imms : BitVec 6) (rn rd : BitVec 5)
    (hopc : decodeBitfieldOp opc.toNat = some (inzero, extend)) :
    decodeInsn32 (bitfieldMoveWord opc immr6 imms rn rd)
      = some (.bitfieldMove inzero extend immr6.toNat imms.toNat rn.toNat rd.toNat) := by
  simp only [decodeInsn32]
  have h1 : bitMatches (bitfieldMoveWord opc immr6 imms rn rd) 0xFFFFFFFF 0xD503201F
      = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [bitfieldMoveWord] at hb
    simp at hb
  have h2 : bitMatches (bitfieldMoveWord opc immr6 imms rn rd) 0x9F800000 0x92800000
      = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [bitfieldMoveWord] at hb
    simp at hb
  have h3 : bitMatches (bitfieldMoveWord opc immr6 imms rn rd) 0x9F800000 0x91000000
      = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [bitfieldMoveWord] at hb
    simp at hb
  have h4 : bitMatches (bitfieldMoveWord opc immr6 imms rn rd) 0x9F800000 0x92000000
      = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [bitfieldMoveWord] at hb
    simp at hb
  have h5 : bitMatches (bitfieldMoveWord opc immr6 imms rn rd) 0x9F000000 0x8A000000
      = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 28) h
    simp only [bitfieldMoveWord] at hb
    simp at hb
  have h6 : bitMatches (bitfieldMoveWord opc immr6 imms rn rd) 0x9F200000 0x8B000000
      = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 28) h
    simp only [bitfieldMoveWord] at hb
    simp at hb
  have hK : bitMatches (bitfieldMoveWord opc immr6 imms rn rd) 0x9FC00000
      0x93400000 = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [bitfieldMoveWord]
    simp
    interval_cases i <;> simp
  simp only [h1, h2, h3, h4, h5, h6, hK, Bool.false_eq_true, if_true, if_false]
  have f29 : part (bitfieldMoveWord opc immr6 imms rn rd) 29 2 = opc.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [bitfieldMoveWord]
    simp
    interval_cases i <;> simp
  have f16 : part (bitfieldMoveWord opc immr6 imms rn rd) 16 6 = immr6.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [bitfieldMoveWord]
    simp
    interval_cases i <;> simp
  have f10 : part (bitfieldMoveWord opc immr6 imms rn rd) 10 6 = imms.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [bitfieldMoveWord]
    simp
    interval_cases i <;> simp
  have f5 : part (bitfieldMoveWord opc immr6 imms rn rd) 5 5 = rn.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [bitfieldMoveWord]
    simp
    interval_cases i <;> simp
  have f0 : part (bitfieldMoveWord opc immr6 imms rn rd) 0 5 = rd.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [bitfieldMoveWord]
    simp
  simp only [f29, hopc, f16, f10, f5, f0]

/-- The `bitfieldMove` word decodes back to the encoded instruction, provided the
rotated width fits in five bits. -/
theorem decode_encode_bitfieldMove32 (inzero extend : Bool) (immr imms rn rd : Nat)
    (opc : Nat) (hbits : bitfieldOpBits inzero extend = some opc)
    (himmr : immr < 64) (himms : imms < 64) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn32 (fields [(1, 1), (2, opc), (6, 0b100110), (1, 1), (6, immr),
      (6, imms), (5, rn), (5, rd)])
      = some (.bitfieldMove inzero extend immr imms rn rd) := by
  have hopc2 : (BitVec.ofNat 2 opc).toNat = opc := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := bitfieldOpBits_lt inzero extend opc hbits
    omega
  have himmr6 : (BitVec.ofNat 6 immr).toNat = immr := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : immr < 2 ^ 6)]
  have himms6 : (BitVec.ofNat 6 imms).toNat = imms := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : imms < 2 ^ 6)]
  rw [fields_bitfieldMove opc immr imms rn rd,
    decode_bitfieldMove_word inzero extend (BitVec.ofNat 2 opc) (BitVec.ofNat 6 immr)
      (BitVec.ofNat 6 imms) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd)
      (by rw [hopc2]; exact decodeBitfieldOp_bitfieldOpBits inzero extend opc hbits)]
  simp only [himmr6, himms6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrn,
    Nat.mod_eq_of_lt hrd]

/-- The 64-bit carrier word emitted for a `bitfieldMove`. -/
theorem encodeInsn_bitfieldMove (inzero extend : Bool) (immr imms rn rd : Nat)
    (opc : Nat) (hbits : bitfieldOpBits inzero extend = some opc)
    (himmr : immr < 64) (himms : imms < 64) :
    encodeInsn (.bitfieldMove inzero extend immr imms rn rd) =
      some ((fields [(1, 1), (2, opc), (6, 0b100110), (1, 1), (6, immr), (6, imms),
        (5, rn), (5, rd)]).setWidth 64) := by
  unfold encodeInsn
  simp only [encodeInsn32, hbits, himmr, himms]
  rfl

/-- The 64-bit carrier form of the decoder inverts the encoder's carrier form for
a `bitfieldMove`. -/
theorem decode_encode_bitfieldMove (inzero extend : Bool) (immr imms rn rd : Nat)
    (opc : Nat) (hbits : bitfieldOpBits inzero extend = some opc)
    (himmr : immr < 64) (himms : imms < 64) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((fields [(1, 1), (2, opc), (6, 0b100110), (1, 1), (6, immr),
      (6, imms), (5, rn), (5, rd)]).setWidth 64)
      = some (.bitfieldMove inzero extend immr imms rn rd) := by
  rw [show decodeInsn ((fields [(1, 1), (2, opc), (6, 0b100110), (1, 1), (6, immr),
      (6, imms), (5, rn), (5, rd)]).setWidth 64)
      = decodeInsn32 (fields [(1, 1), (2, opc), (6, 0b100110), (1, 1), (6, immr),
          (6, imms), (5, rn), (5, rd)]) by
    simp [decodeInsn]]
  exact decode_encode_bitfieldMove32 inzero extend immr imms rn rd opc hbits himmr himms
    hrn hrd

/-- `decodeInsn` inverts `encodeInsn` on a `bitfieldMove` whose rotated width fits
in five bits. -/
theorem decode_encode_bitfieldMoveInsn (inzero extend : Bool) (immr imms rn rd : Nat)
    (opc : Nat) (hbits : bitfieldOpBits inzero extend = some opc)
    (himmr : immr < 64) (himms : imms < 64) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((encodeInsn (.bitfieldMove inzero extend immr imms rn rd)).getD 0)
      = some (.bitfieldMove inzero extend immr imms rn rd) := by
  rw [encodeInsn_bitfieldMove inzero extend immr imms rn rd opc hbits himmr himms,
    Option.getD_some]
  exact decode_encode_bitfieldMove inzero extend immr imms rn rd opc hbits himmr himms
    hrn hrd

/-- One machine step executes a `bitfieldMove` whose bytes are at the PC. -/
theorem arm8Next_bitfieldMove (s : Arm8State) (d : BitVec 64 → Prop)
    (inzero extend : Bool) (immr imms rn rd : Nat) (opc : Nat)
    (hbits : bitfieldOpBits inzero extend = some opc)
    (himmr : immr < 64) (himms : imms < 64) (hrn : rn < 32) (hrd : rd < 32)
    (hbytes : bytesInMemoryHOL s.pc
      (encodeBytes (.bitfieldMove inzero extend immr imms rn rd)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 }
      (.bitfieldMove inzero extend immr imms rn rd) := by
  rw [arm8Next_encodeBytes s (.bitfieldMove inzero extend immr imms rn rd)
    ((fields [(1, 1), (2, opc), (6, 0b100110), (1, 1), (6, immr), (6, imms),
      (5, rn), (5, rd)]).setWidth 64) d
    (encodeInsn_bitfieldMove inzero extend immr imms rn rd opc hbits himmr himms)
    (decode_encode_bitfieldMove inzero extend immr imms rn rd opc hbits himmr himms
      hrn hrd) hbytes]

end Flapjack.Compiler.Encoders.Arm8
