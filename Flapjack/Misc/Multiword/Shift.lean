module

public import Flapjack.Misc.Multiword.Digits
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Halving a multiword number by a one-bit right shift. -/
namespace Flapjack.Misc.Multiword
open Flapjack

/-- Shift a little-endian digit list right by one bit. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_shift_def"
  (words_as_type_indexed_bitvec)]
def mwShift {width : Nat} [NeZero width] : List (BitVec width) → List (BitVec width)
  | [] => []
  | [w] => [w >>> 1]
  | w :: x :: xs => (w >>> 1 ||| x <<< (width - 1)) :: mwShift (x :: xs)

private theorem shift_or_toNat {width : Nat} [NeZero width] (w x : BitVec width) :
    (w >>> 1 ||| x <<< (width - 1)).toNat = w.toNat / 2 + x.toNat % 2 * 2 ^ (width - 1) := by
  have pos := Nat.pos_of_ne_zero (NeZero.ne width)
  have disjoint : w >>> 1 &&& x <<< (width - 1) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
      ]
    by_cases small : i < width - 1
    · simp [small]
    · have : i = width - 1 := by omega
      subst this
      simp [show 1 + (width - 1) = width by omega, BitVec.getLsbD_of_ge]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ disjoint, BitVec.toNat_add,
    BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, Nat.pow_one]
  have hw : 2 ^ width = 2 * 2 ^ (width - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hx := x.isLt
  have hwx := w.isLt
  have low : x.toNat * 2 ^ (width - 1) % 2 ^ width = x.toNat % 2 * 2 ^ (width - 1) := by
    rw [hw, Nat.mul_mod_mul_right]
  rw [low]
  apply Nat.mod_eq_of_lt
  have : x.toNat % 2 ≤ 1 := by omega
  have : w.toNat / 2 < 2 ^ (width - 1) := by omega
  have : x.toNat % 2 * 2 ^ (width - 1) ≤ 2 ^ (width - 1) := by
    calc x.toNat % 2 * 2 ^ (width - 1) ≤ 1 * 2 ^ (width - 1) := Nat.mul_le_mul_right _ ‹_›
      _ = 2 ^ (width - 1) := Nat.one_mul _
  omega

/-- The shifted digits denote half the value, rounded down. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_shift_thm"
  (words_as_type_indexed_bitvec)]
theorem mwShift_thm {width : Nat} [NeZero width] :
    ∀ xs : List (BitVec width), mw2n (mwShift xs) = mw2n xs / 2 := by
  have pos := Nat.pos_of_ne_zero (NeZero.ne width)
  have hw : 2 ^ width = 2 * 2 ^ (width - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  intro xs
  induction xs with
  | nil => simp [mwShift, mw2n]
  | cons w xs ih =>
    cases xs with
    | nil =>
      simp only [mwShift, mw2n, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
        Nat.pow_one, Nat.mul_zero, Nat.add_zero]
    | cons x xs =>
      simp only [mwShift, mw2n] at ih ⊢
      rw [ih, shift_or_toNat]
      generalize mw2n xs = rest
      rw [hw]
      generalize 2 ^ (width - 1) = H
      have hx : x.toNat = x.toNat % 2 + 2 * (x.toNat / 2) := (Nat.mod_add_div _ _).symm
      have rb : x.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
      generalize x.toNat % 2 = r at hx rb ⊢
      generalize x.toNat / 2 = q at hx ⊢
      rw [hx]
      have e1 : (r + 2 * q + 2 * H * rest) / 2 = q + H * rest + r / 2 := by
        rw [show r + 2 * q + 2 * H * rest = r + 2 * (q + H * rest) by ring,
          Nat.add_mul_div_left _ _ (by decide)]
        omega
      have e2 : (w.toNat + 2 * H * (r + 2 * q + 2 * H * rest)) / 2 =
          w.toNat / 2 + (H * r + 2 * H * (q + H * rest)) := by
        rw [show w.toNat + 2 * H * (r + 2 * q + 2 * H * rest) =
            w.toNat + 2 * (H * r + 2 * H * (q + H * rest)) by ring,
          Nat.add_mul_div_left _ _ (by decide)]
      rw [e1, e2, show r / 2 = 0 by omega]
      ring

/-- Shifting keeps the number of digits. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "LENGTH_mw_shift"
  (words_as_type_indexed_bitvec)]
theorem length_mwShift {width : Nat} [NeZero width] :
    ∀ xs : List (BitVec width), (mwShift xs).length = xs.length := by
  intro xs
  induction xs with
  | nil => rfl
  | cons w xs ih =>
    cases xs with
    | nil => rfl
    | cons x xs => simp only [mwShift, List.length_cons] at ih ⊢; rw [ih]

end Flapjack.Misc.Multiword
