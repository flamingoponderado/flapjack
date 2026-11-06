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
lemma lor_mod_two_pow_of_lt (a b n : Nat) (ha : a < 2 ^ n) :
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

/-- The computable rotation is the `BitVec` rotation at any width. -/
theorem rotateRightWidth_eq_gen (m : Nat) (w : BitVec m) (n : Nat) :
    rotateRightWidth m w.toNat n = (BitVec.rotateRight w n).toNat := by
  rw [BitVec.toNat_rotateRight]
  unfold rotateRightWidth
  rw [Nat.mod_eq_of_lt w.isLt]
  dsimp only
  rw [lor_mod_two_pow_of_lt _ _ m (by
    rw [Nat.shiftRight_eq_div_pow]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) w.isLt)]

/-- `holRotate` moves the low `r % length` bits to the front, which is a right
rotation of the word value. -/
theorem holRotate_eq_drop_take (v : List Bool) (r : Nat) (hlen : 1 ≤ v.length) :
    holRotate v r = v.drop (v.length - r % v.length) ++ v.take (v.length - r % v.length) := by
  unfold holRotate holField holShiftr holFixwidth
  dsimp only
  set x := r % v.length with hx
  have hxlt : x < v.length := Nat.mod_lt _ (by omega)
  by_cases h0 : x = 0
  · simp only [h0, Nat.sub_zero, List.drop_length, List.take_length]
    split
    · rfl
    · rename_i h
      exact absurd h0 (by tauto)
  · have hv0 : ¬ v.length = 0 := by omega
    have hx1 : x - 1 + 1 = x := Nat.sub_one_add_one h0
    have hy1 : v.length - 1 + 1 - x = v.length - x := by omega
    have hle : ¬ v.length < x := by omega
    have hmin : min (v.length - x) v.length = v.length - x := Nat.min_eq_left (by omega)
    simp only [hv0, false_or, h0, Nat.sub_zero, if_false, hx1, hy1, hle,
      List.take_length, List.length_take, hmin, Nat.lt_irrefl, Nat.sub_self, List.drop_zero]

/-- The fold step of `holV2n`. -/
private def v2nStep (acc : Nat) (b : Bool) : Nat := 2 * acc + (if b then 1 else 0)

/-- The fold of `holV2n` from an arbitrary accumulator is that accumulator
times `2 ^ length` plus the value of the list. -/
private theorem holV2n_shift (acc : Nat) (b : List Bool) :
    List.foldl v2nStep acc b = acc * 2 ^ b.length + holV2n b := by
  induction b generalizing acc with
  | nil => simp [holV2n]
  | cons x t ih =>
    have hcons : holV2n (x :: t) = v2nStep 0 x * 2 ^ t.length + holV2n t := by
      show List.foldl v2nStep (v2nStep 0 x) t = _
      exact ih (v2nStep 0 x)
    simp only [List.foldl_cons, List.length_cons, hcons]
    rw [ih (v2nStep acc x)]
    simp only [v2nStep]
    rw [Nat.pow_succ]
    simp only [Nat.add_mul, Nat.mul_assoc]
    simp only [Nat.zero_mul]
    ac_rfl

/-- The value of a concatenation: the first part is the high bits. -/
theorem holV2n_append (a b : List Bool) :
    holV2n (a ++ b) = holV2n a * 2 ^ b.length + holV2n b := by
  show List.foldl v2nStep 0 (a ++ b) =
      List.foldl v2nStep 0 a * 2 ^ b.length + List.foldl v2nStep 0 b
  rw [List.foldl_append]
  exact holV2n_shift (List.foldl v2nStep 0 a) b

/-- The value of a non-empty list starts with its head. -/
theorem holV2n_cons (x : Bool) (t : List Bool) :
    holV2n (x :: t) = (if x then 1 else 0) * 2 ^ t.length + holV2n t := by
  show List.foldl v2nStep (v2nStep 0 x) t = _
  rw [holV2n_shift (v2nStep 0 x) t]
  simp [v2nStep]

/-- A list's value fits in its own width. -/
theorem holV2n_lt (v : List Bool) : holV2n v < 2 ^ v.length := by
  induction v with
  | nil => simp [holV2n]
  | cons x t ih =>
    rw [holV2n_cons, List.length_cons, Nat.pow_succ]
    have hb : (if x then 1 else 0) ≤ 1 := by cases x <;> simp
    have hle : (if x then 1 else 0) * 2 ^ t.length ≤ 2 ^ t.length := by
      calc (if x then 1 else 0) * 2 ^ t.length ≤ 1 * 2 ^ t.length :=
            Nat.mul_le_mul_right _ hb
        _ = 2 ^ t.length := Nat.one_mul _
    omega

/-- Bit `i` of a list's value is the `i`-th bit from the end, matching the
`FCP` rendering in `holV2w`. -/
theorem holV2n_testBit (v : List Bool) (i : Nat) :
    (holV2n v).testBit i =
      (decide (i < v.length) && v.getD (v.length - 1 - i) false) := by
  induction v with
  | nil => simp [holV2n]
  | cons x t ih =>
    rw [holV2n_cons]
    rw [show (if x then 1 else 0) * 2 ^ t.length + holV2n t
        = 2 ^ t.length * (if x then 1 else 0) + holV2n t by rw [Nat.mul_comm]]
    rw [Nat.testBit_two_pow_mul_add _ (holV2n_lt t) i]
    by_cases hi : i < t.length
    · rw [if_pos hi, ih]
      have h1 : i < t.length + 1 := by omega
      simp only [List.length_cons, hi, h1, decide_true]
      rw [show t.length + 1 - 1 - i = t.length - i by omega]
      simp only [Bool.true_and]
      rw [← List.getD_cons_succ]
      congr 1
      omega
    · rw [if_neg hi]
      by_cases heq : i = t.length
      · subst heq
        have h1 : t.length < t.length + 1 := by omega
        simp only [h1, List.length_cons, Nat.add_sub_cancel, Nat.sub_self,
          List.getD_cons_zero, decide_true, Bool.true_and]
        cases x <;> simp [Nat.testBit_zero]
      · have hlt : ¬ i < t.length + 1 := by omega
        simp only [hlt, List.length_cons, decide_false, Bool.false_and]
        have hk : 1 ≤ i - t.length := by omega
        have h2 : 1 < 2 ^ (i - t.length) := by
          have hp : 2 ^ 1 ≤ 2 ^ (i - t.length) :=
            Nat.pow_le_pow_right (by decide : 0 < 2) hk
          have h21 : 2 ^ 1 = 2 := by decide
          omega
        cases x <;> simp [Nat.testBit_lt_two_pow h2]

/-- `bitstring$v2w` at an explicit width agrees with the numeric rendering of
`holV2n` when the list fits. -/
theorem holV2w_eq_ofNat (m : Nat) (v : List Bool) (_h : v.length ≤ m) :
    holV2w m v = BitVec.ofNat m (holV2n v) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  show (holFcpWord (width := m)
      (fun j => decide (j < v.length) && v.getD (v.length - 1 - j) false)).getLsbD i
      = (BitVec.ofNat m (holV2n v)).getLsbD i
  rw [getLsbD_holFcpWord, BitVec.getLsbD_ofNat, holV2n_testBit]

end Flapjack.Compiler.Encoders.Arm8.L3
