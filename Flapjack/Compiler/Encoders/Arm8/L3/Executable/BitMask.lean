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

end Flapjack.Compiler.Encoders.Arm8.L3
