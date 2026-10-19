import Mathlib.Data.BitVec
import Mathlib.Tactic

/-!
# Converse mask facts for the ARM8 immediate encodings

Converses of the mask lemmas in `DecodeProofConditional`: a word killed by the
high-bit mask `~~~0xFFF` is below `4096`, and a word killed by `~~~0xFFF000` is a
multiple of `4096` below `2^24`.  The proofs are bitwise, since arithmetic on
`&&&` with these constant masks is not available.
-/

namespace Flapjack.Compiler.Encoders.Arm8

theorem and_not_fff_eq_zero_toNat_lt {w : BitVec 64}
    (h : w &&& ~~~(BitVec.ofNat 64 4095) = 0) : w.toNat < 4096 := by
  have hbit : ∀ i, 12 ≤ i → i < 64 → w.getLsbD i = false := by
    intro i hi hi64
    have hmask : (~~~(BitVec.ofNat 64 4095)).getLsbD i = true := by
      rw [BitVec.getLsbD_not, BitVec.getLsbD_ofNat]
      have htest : (4095 : Nat).testBit i = false := by
        rw [show 4095 = 2 ^ 12 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
        simp [hi]
      simp [hi64, htest]
    have hb := congrArg (fun x : BitVec 64 => x.getLsbD i) h
    have hz : (0 : BitVec 64).getLsbD i = false := by simp
    simp only [BitVec.getLsbD_and, hmask, Bool.and_true, hz] at hb
    exact hb
  have heq : w = w &&& (BitVec.ofNat 64 4095) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and, BitVec.getLsbD_ofNat]
    by_cases h12 : i < 12
    · have htest : (4095 : Nat).testBit i = true := by
        rw [show 4095 = 2 ^ 12 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
        simp [h12]
      simp [hi, htest]
    · have hb := hbit i (by omega) hi
      simp [hb]
  have hto : w.toNat = w.toNat &&& 4095 := by
    have := congrArg BitVec.toNat heq
    simpa [BitVec.toNat_and] using this
  rw [hto]
  exact Nat.and_lt_two_pow (x := w.toNat) (y := 4095) (n := 12) (by norm_num)

theorem mask_fff000_low {i : Nat} (hi : i < 12) :
    (~~~(BitVec.ofNat 64 0xFFF000)).getLsbD i = true := by
  rw [BitVec.getLsbD_not, BitVec.getLsbD_ofNat]
  have htest : (0xFFF000 : Nat).testBit i = false := by
    rw [show 0xFFF000 = (2 ^ 12 - 1) <<< 12 by decide, Nat.testBit_shiftLeft]
    have hlt : ¬ 12 ≤ i := by omega
    simp [hlt]
  have hlt : i < 64 := by omega
  simp [hlt, htest]

theorem mask_fff000_high {i : Nat} (hi : 24 ≤ i) (hi64 : i < 64) :
    (~~~(BitVec.ofNat 64 0xFFF000)).getLsbD i = true := by
  rw [BitVec.getLsbD_not, BitVec.getLsbD_ofNat]
  have htest : (0xFFF000 : Nat).testBit i = false := by
    rw [show 0xFFF000 = (2 ^ 12 - 1) <<< 12 by decide, Nat.testBit_shiftLeft,
      Nat.testBit_two_pow_sub_one]
    have hge : 12 ≤ i := by omega
    have hfar : ¬ i - 12 < 12 := by omega
    simp [hge, hfar]
  simp [hi64, htest]

theorem and_not_fff000_eq_zero_low {w : BitVec 64}
    (h : w &&& ~~~(BitVec.ofNat 64 0xFFF000) = 0) :
    w &&& (BitVec.ofNat 64 4095) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_ofNat]
  have hz : (0 : BitVec 64).getLsbD i = false := by simp
  by_cases h12 : i < 12
  · have hmask := mask_fff000_low h12
    have hb := congrArg (fun x : BitVec 64 => x.getLsbD i) h
    simp only [BitVec.getLsbD_and, hmask, Bool.and_true, hz] at hb
    have htest : (4095 : Nat).testBit i = true := by
      rw [show 4095 = 2 ^ 12 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
      simp [h12]
    simp [hb, htest]
  · have htest : (4095 : Nat).testBit i = false := by
      rw [show 4095 = 2 ^ 12 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
      simp [h12]
    simp [htest]

theorem and_not_fff000_eq_zero_toNat_mod {w : BitVec 64}
    (h : w &&& ~~~(BitVec.ofNat 64 0xFFF000) = 0) : w.toNat % 4096 = 0 := by
  have hlow := and_not_fff000_eq_zero_low h
  have hto : w.toNat &&& 4095 = 0 := by
    have := congrArg BitVec.toNat hlow
    simpa [BitVec.toNat_and] using this
  rw [show 4096 = 2 ^ 12 by norm_num, ← Nat.and_two_pow_sub_one_eq_mod, hto]

theorem and_not_fff000_eq_zero_toNat_lt {w : BitVec 64}
    (h : w &&& ~~~(BitVec.ofNat 64 0xFFF000) = 0) : w.toNat < 2 ^ 24 := by
  have hbit : ∀ i, 24 ≤ i → i < 64 → w.toNat.testBit i = false := by
    intro i hi hi64
    have hmask := mask_fff000_high hi hi64
    have hb := congrArg (fun x : BitVec 64 => x.getLsbD i) h
    have hz : (0 : BitVec 64).getLsbD i = false := by simp
    simp only [BitVec.getLsbD_and, hmask, Bool.and_true, hz] at hb
    change w.getLsbD i = false at hb
    exact hb
  have hto : w.toNat = w.toNat &&& 16777215 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    by_cases h24 : i < 24
    · have htest : Nat.testBit 16777215 i = true := by
        rw [show 16777215 = 2 ^ 24 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
        simp [h24]
      rw [htest]
      cases hw : w.toNat.testBit i <;> rfl
    · by_cases hi64 : i < 64
      · have hb := hbit i (by omega) hi64
        have htest : Nat.testBit 16777215 i = false := by
          rw [show 16777215 = 2 ^ 24 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
          simp [h24]
        rw [hb, htest]
        rfl
      · have hpow : 2 ^ 64 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hw : w.toNat.testBit i = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le w.isLt hpow)
        have htest : Nat.testBit 16777215 i = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num : 16777215 < 2 ^ 64) hpow)
        rw [hw, htest]
        rfl
  have hbnd : w.toNat &&& 16777215 < 2 ^ 24 := Nat.and_lt_two_pow _ (by decide)
  exact hto ▸ hbnd

end Flapjack.Compiler.Encoders.Arm8
