import Flapjack.Compiler.Encoders.Arm8.L3.Defs
import Mathlib.Data.Nat.Bitwise

/-!
# Bitmask encoding: counting and rotation

First part of the `Arm8.encodeBitMask` / `L3.EncodeBitMask` correspondence:
the computable `countTrailing` agrees with the L3 `CountTrailing` at width 64,
and the computable 64-bit `rotateRightWidth` agrees with `BitVec.rotateRight`.
The decoder, aux and encoder correspondences follow in later commits; only
then does the module establish the full `encodeBitMask` bridge.

No new HOL claim is introduced: these relate two Lean renderings of the same
bitmask search.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem

private lemma getLsbD_zero_ofNat (v : Nat) :
    (BitVec.ofNat 64 v).getLsbD 0 = (v % 2 == 1) := by
  rw [BitVec.getLsbD_ofNat, Nat.testBit_zero]
  by_cases h : v % 2 = 1 <;> simp [h]

private lemma ofNat_ushiftRight_one (v : Nat) (h : v < 2^64) :
    (BitVec.ofNat 64 v) >>> (1 : Nat) = BitVec.ofNat 64 (v >>> 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hv' : v >>> 1 < 2 ^ 64 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) h
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt hv']

private lemma guard_iff (b : Bool) (v : Nat) (h : v < 2^64) :
    ((BitVec.ofNat 64 v).getLsbD 0 = b ∨
       (if b then BitVec.ofNat 64 v = 0 else BitVec.ofNat 64 v = -1)) ↔
    (((v % 2 == 1) = b) ∨ (if b then v = 0 else v = 2^64 - 1)) := by
  rw [getLsbD_zero_ofNat]
  cases b
  · simp only [Bool.false_eq_true, if_false, BitVec.toNat_eq, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt h]
    have hneg : (-1 : BitVec 64).toNat = 2^64 - 1 := by decide
    rw [hneg]
  · simp only [if_true, BitVec.toNat_eq, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt h]
    simp

private lemma guardBool_iff (b : Bool) (v : Nat) (h : v < 2^64) :
    ((((BitVec.ofNat 64 v).getLsbD 0 == b) ||
       (if b then BitVec.ofNat 64 v == 0 else BitVec.ofNat 64 v == -1)) = true) ↔
    (((v % 2 == 1) = b) ∨ (if b then v = 0 else v = 2^64 - 1)) := by
  rw [Bool.or_eq_true]
  cases b
  · simp only [Bool.false_eq_true, if_false, beq_iff_eq]
    exact guard_iff false v h
  · simp only [if_true, beq_iff_eq]
    simpa using guard_iff true v h

private lemma CountTrailing_eq_of_guard (b : Bool) (w : BitVec 64)
    (h : (((w.getLsbD 0 == b) || (if b then w == 0 else w == -1)) = true)) :
    CountTrailing (TN := 64) (b, w) = 0 := by
  rw [CountTrailing.eq_def]
  dsimp only
  cases b
  · simp only [Bool.false_eq_true, if_false]
    split
    · rfl
    · rename_i hneg
      exact absurd h hneg
  · simp only [if_true]
    split
    · rfl
    · rename_i hneg
      exact absurd h hneg

private lemma CountTrailing_eq_of_not_guard (b : Bool) (w : BitVec 64)
    (h : ¬ (((w.getLsbD 0 == b) || (if b then w == 0 else w == -1)) = true)) :
    CountTrailing (TN := 64) (b, w) =
      1 + CountTrailing (TN := 64) (b, w >>> (1 : Nat)) := by
  rw [CountTrailing.eq_def]
  dsimp only
  cases b
  · simp only [Bool.false_eq_true, if_false]
    split
    · rename_i hpos
      exact absurd hpos h
    · rfl
  · simp only [if_true]
    split
    · rename_i hpos
      exact absurd hpos h
    · rfl

private lemma go_eq_CountTrailing (b : Bool) :
    ∀ (fuel : Nat), fuel ≤ 64 → ∀ (v : Nat), v < 2 ^ fuel →
      countTrailing.go b fuel v = CountTrailing (TN := 64) (b, BitVec.ofNat 64 v) := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ v hv
    have hv0 : v = 0 := by
      rw [Nat.pow_zero] at hv
      omega
    subst hv0
    rw [countTrailing.go.eq_1, CountTrailing.eq_def]
    simp
  | succ f ih =>
    intro hf v hv
    have hv64 : v < 2^64 := by
      have hle : 2 ^ (f + 1) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hf
      omega
    rw [countTrailing.go.eq_2, Nat.mod_eq_of_lt hv64]
    by_cases hP : ((v % 2 == 1) = b) ∨ (if b then v = 0 else v = 2^64 - 1)
    · have hG : ((((BitVec.ofNat 64 v).getLsbD 0 == b) ||
          (if b then BitVec.ofNat 64 v == 0 else BitVec.ofNat 64 v == -1)) = true) :=
        (guardBool_iff b v hv64).mpr hP
      rw [if_pos hP, CountTrailing_eq_of_guard b (BitVec.ofNat 64 v) hG]
    · have hG : ¬ ((((BitVec.ofNat 64 v).getLsbD 0 == b) ||
          (if b then BitVec.ofNat 64 v == 0 else BitVec.ofNat 64 v == -1)) = true) :=
        fun hh => hP ((guardBool_iff b v hv64).mp hh)
      rw [if_neg hP, CountTrailing_eq_of_not_guard b (BitVec.ofNat 64 v) hG]
      have hb : v >>> 1 < 2 ^ f := by
        rw [Nat.shiftRight_eq_div_pow]
        have hp : v < 2 * 2 ^ f := by
          rw [Nat.mul_comm, ← Nat.pow_succ]
          exact hv
        simpa using Nat.div_lt_of_lt_mul hp
      rw [ofNat_ushiftRight_one v hv64, ih (by omega) (v >>> 1) hb]

theorem countTrailing_eq (b : Bool) (w : BitVec 64) :
    countTrailing b w.toNat = CountTrailing (TN := 64) (b, w) := by
  rw [show countTrailing b w.toNat = countTrailing.go b 64 w.toNat from rfl]
  rw [go_eq_CountTrailing b 64 (by omega) w.toNat w.isLt]
  simp [BitVec.ofNat_toNat]

/-- Masking an OR whose first operand already fits `n` bits. -/
private lemma lor_mod_two_pow_of_lt (a b n : Nat) (ha : a < 2 ^ n) :
    (a ||| b) % 2 ^ n = a ||| (b % 2 ^ n) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_lor, Nat.testBit_lor, Nat.testBit_mod_two_pow]
  by_cases h : i < n
  · simp [h]
  · have hle : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt h)
    have hai : a.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hle)
    simp [h, hai]

/-- The computable rotation is the `BitVec` rotation. -/
theorem rotateRightWidth_eq (w : BitVec 64) (n : Nat) :
    rotateRightWidth 64 w.toNat n = (BitVec.rotateRight w n).toNat := by
  rw [BitVec.toNat_rotateRight]
  unfold rotateRightWidth
  rw [Nat.mod_eq_of_lt w.isLt]
  dsimp only
  rw [lor_mod_two_pow_of_lt _ _ 64 (by
    rw [Nat.shiftRight_eq_div_pow]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) w.isLt)]

/-- The computable `highestSetBit` is the L3 `HighestSetBit` at width 7. -/
theorem highestSetBit_eq (w : BitVec 7) :
    highestSetBit w.toNat = HighestSetBit (TN := 7) w := by
  unfold highestSetBit HighestSetBit holWordLog2
  by_cases h : w.toNat = 0
  · have hw : (w == (BitVec.ofNat 7 0)) = true := by
      rw [beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      simp [h]
    simp [h, hw]
  · have hw : (w == (BitVec.ofNat 7 0)) = false := by
      rw [beq_eq_false_iff_ne]
      intro hh
      apply h
      rw [hh]; rfl
    have hlt : Nat.log2 w.toNat < 7 := (Nat.log2_lt h).mpr w.isLt
    simp only [h, hw, Bool.false_eq_true, if_false]
    have htoNat : (BitVec.ofNat 7 (Nat.log2 w.toNat)).toNat = Nat.log2 w.toNat := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toInt_eq_toNat_bmod, htoNat]
    symm
    apply Int.bmod_eq_of_le <;> omega

/-- The computable `ones` is the L3 `Ones` at width 6. -/
theorem ones_eq (n : Nat) (hn : n ≤ 6) :
    ones n = (holV2w 6 (Ones n)).toNat := by
  have hbit : holV2w 6 (Ones n) = BitVec.ofNat 6 (2 ^ n - 1) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    unfold holV2w Flapjack.RiscV.L3.holV2w
    rw [getLsbD_holFcpWord]
    unfold Ones holPadLeft
    simp only [List.length_replicate, List.append_nil, BitVec.getLsbD_ofNat]
    by_cases h : i < n
    · have hidx : n - 1 - i < n := by omega
      simp [hi, h, hidx, Nat.testBit_two_pow_sub_one]
    · simp [hi, h, Nat.testBit_two_pow_sub_one]
  have htoNat : (BitVec.ofNat 6 (2 ^ n - 1)).toNat = 2 ^ n - 1 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by
      have h2 : 2 ^ n ≤ 64 := Nat.pow_le_pow_right (by decide) hn
      omega)
  unfold ones
  rw [hbit, htoNat]

/-- The decoder's `len` argument: the computable Nat is the L3 7-bit word
`immN ++ ~~~imms`. -/
theorem len_eq (immN : BitVec 1) (imms : BitVec 6) :
    ((immN.toNat % 2) <<< 6) ||| (63 - imms.toNat % 64) = (immN ++ ~~~imms).toNat := by
  rw [BitVec.toNat_append]
  simp only [BitVec.toNat_not, Nat.reducePow]
  have h1 : immN.toNat < 2 := immN.isLt
  have h2 : imms.toNat < 64 := imms.isLt
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]

/-- `ones k` is the L3 `holV2w m (holPadLeft false m (Ones k))` at any width
`m ≥ k`, used for the rotated element of the decoder. -/
theorem ones_pad_eq (m k : Nat) (hk : k ≤ m) (hm : m ≤ 64) :
    (holV2w m (holPadLeft false m (Ones k))).toNat = ones k := by
  have hbit : holV2w m (holPadLeft false m (Ones k)) = BitVec.ofNat m (2 ^ k - 1) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    unfold holV2w Flapjack.RiscV.L3.holV2w
    rw [getLsbD_holFcpWord]
    simp only [holPadLeft, Ones, List.length_replicate, List.length_append,
      List.length_nil, Nat.sub_zero, List.append_nil, Nat.sub_add_cancel hk,
      BitVec.getLsbD_ofNat]
    rw [List.getD_eq_getElem?_getD]
    by_cases h : i < k
    · have hge : ¬ m - 1 - i < (List.replicate (m - k) false).length := by
        simp only [List.length_replicate]; omega
      rw [List.getElem?_append, if_neg hge]
      simp only [List.length_replicate]
      rw [List.getElem?_eq_getElem (by
        rw [List.length_replicate]; omega)]
      simp [hi, h, Nat.testBit_two_pow_sub_one]
    · have hlt : m - 1 - i < (List.replicate (m - k) false).length := by
        simp only [List.length_replicate]; omega
      rw [List.getElem?_append, if_pos hlt]
      rw [List.getElem?_eq_getElem (by
        rw [List.length_replicate]; omega)]
      simp [hi, h, Nat.testBit_two_pow_sub_one]
  have htoNat : (BitVec.ofNat m (2 ^ k - 1)).toNat = 2 ^ k - 1 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by
      have h2 : 2 ^ k ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hk
      have h3 : 2 ^ m ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hm
      have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
      omega)
  unfold ones
  rw [hbit, htoNat]

end Flapjack.Compiler.Encoders.Arm8.L3
