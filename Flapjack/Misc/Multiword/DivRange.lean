module

public import Flapjack.Misc.Multiword.DivTest

@[expose] public section

/-! Knuth's bounds on the trial quotient digit. -/
namespace Flapjack.Misc.Multiword
open Flapjack

private theorem rev_cons_value {width : Nat} [NeZero width] (x : BitVec width)
    (xs : List (BitVec width)) :
    mw2n (x :: xs).reverse = mw2n xs.reverse + dimwords width xs.length * x.toNat := by
  rw [List.reverse_cons, mw2n_msf, List.length_reverse]

private theorem rev_value_lt {width : Nat} [NeZero width] (xs : List (BitVec width)) :
    mw2n xs.reverse < dimwords width xs.length := by
  have := mw2n_lt xs.reverse
  rwa [List.length_reverse] at this

/-- With a normalised divisor the trial digit exceeds the true digit by at most two. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_div_range2"
  (words_as_type_indexed_bitvec)]
theorem mw_div_range2 {width : Nat} [NeZero width] :
    ∀ (u1 u2 : BitVec width) (us : List (BitVec width)) (v1 : BitVec width)
      (vs : List (BitVec width)),
      us.length = vs.length ∧
        mw2n (u1 :: u2 :: us).reverse / mw2n (v1 :: vs).reverse < 2 ^ width ∧
        2 ^ width / 2 ≤ v1.toNat →
      min ((u1.toNat * 2 ^ width + u2.toNat) / v1.toNat) (2 ^ width - 1) ≤
        mw2n (u1 :: u2 :: us).reverse / mw2n (v1 :: vs).reverse + 2 := by
  rintro u1 u2 us v1 vs ⟨len, _, half⟩
  rw [rev_cons_value, rev_cons_value, List.length_cons, dimwords_succ, rev_cons_value, ← len]
  have hR := rev_value_lt us
  have hS := rev_value_lt vs
  rw [← len] at hS
  have hl : 0 < dimwords width us.length := dimwords_pos _
  generalize dimwords width us.length = l at hR hS hl
  generalize mw2n us.reverse = R at hR
  generalize mw2n vs.reverse = S at hS
  generalize ha : u1.toNat * 2 ^ width + u2.toNat = A
  have hU : R + l * u2.toNat + 2 ^ width * l * u1.toNat = A * l + R := by rw [← ha]; ring
  rw [hU]
  generalize hq : (A * l + R) / (S + l * v1.toNat) = q
  have hb : 2 ≤ 2 ^ width := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) (Nat.pos_of_ne_zero (NeZero.ne width))
  apply Nat.le_of_not_lt
  intro big
  rcases Nat.eq_zero_or_pos v1.toNat with z | vpos
  · simp [z] at big
  have q1 : min (A / v1.toNat) (2 ^ width - 1) ≤ A / v1.toNat := Nat.min_le_left _ _
  have q2 : min (A / v1.toNat) (2 ^ width - 1) ≤ 2 ^ width - 1 := Nat.min_le_right _ _
  generalize min (A / v1.toNat) (2 ^ width - 1) = q' at q1 q2 big
  have hqv : q' * v1.toNat ≤ A := by
    calc q' * v1.toNat ≤ A / v1.toNat * v1.toNat := Nat.mul_le_mul_right _ q1
      _ ≤ A := Nat.div_mul_le_self _ _
  have Vpos : 0 < S + l * v1.toNat := by have := Nat.mul_pos hl vpos; omega
  have hU : A * l + R < (q + 1) * (S + l * v1.toNat) := by
    have := Nat.lt_mul_div_succ (A * l + R) Vpos
    rw [hq] at this
    linarith
  -- q' * v1 * l ≤ A * l ≤ U < (q + 1) * V < (q + 1) * (v1 + 1) * l
  have chain : q' * v1.toNat * l < (q + 1) * (v1.toNat + 1) * l := by
    calc q' * v1.toNat * l ≤ A * l := Nat.mul_le_mul_right _ hqv
      _ ≤ A * l + R := Nat.le_add_right _ _
      _ < (q + 1) * (S + l * v1.toNat) := hU
      _ ≤ (q + 1) * (v1.toNat + 1) * l := by
          rw [Nat.mul_assoc]; apply Nat.mul_le_mul_left
          nlinarith
  have cancel : q' * v1.toNat < (q + 1) * (v1.toNat + 1) := Nat.lt_of_mul_lt_mul_right chain
  have two : 2 * v1.toNat ≤ q := by nlinarith
  have hb2 : 2 ^ width = 2 * (2 ^ width / 2) := by
    have : 2 ^ width % 2 = 0 := by
      rw [show width = width - 1 + 1 by have := NeZero.ne width; omega, Nat.pow_succ]
      simp
    omega
  omega

private theorem q_of_test_choice {width : Nat} [NeZero width] (u1 u2 v1 : BitVec width)
    (vpos : 0 < v1.toNat) :
    (if u1.toNat < v1.toNat then (singleDiv u1 u2 v1).1
      else BitVec.ofNat width (2 ^ width - 1)).toNat =
      min ((u1.toNat * 2 ^ width + u2.toNat) / v1.toNat) (2 ^ width - 1) := by
  have hb : 0 < 2 ^ width := Nat.two_pow_pos _
  split
  · rename_i lt
    have small := single_div_lemma1 (x2 := u2) lt
    rw [Nat.add_comm, Nat.mul_comm] at small
    simp only [singleDiv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
    exact (Nat.min_eq_left (by omega)).symm
  · rename_i ge
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine (Nat.min_eq_right ?_).symm
    apply Nat.le_trans (Nat.sub_le _ 1)
    rw [Nat.le_div_iff_mul_le vpos]
    have := Nat.mul_le_mul_left (2 ^ width) (Nat.le_of_not_lt ge)
    rw [Nat.mul_comm (2 ^ width) u1.toNat] at this
    omega

private theorem cmp_true_bound {width : Nat} [NeZero width] (q u1 u2 u3 v1 v2 : BitVec width) :
    mwCmp [u3, u2, u1] (mwMulBySingle q [v2, v1]) = some true ↔
      u1.toNat * 2 ^ width * 2 ^ width + u2.toNat * 2 ^ width + u3.toNat <
        q.toNat * (v1.toNat * 2 ^ width + v2.toNat) := by
  have ⟨val, len⟩ := mwMulBySingle_lemma q [v2, v1]
  rw [mwCmpThm _ _ (by rw [len]; rfl), val]
  have key : ∀ A B : Nat, ((if A = B then none else some (decide (A < B))) = some true ↔ A < B) := by
    intro A B
    by_cases e : A = B
    · simp [e]
    · simp [e]
  rw [key]
  simp only [mw2n, Nat.mul_zero, Nat.add_zero]
  constructor <;> intro h <;> nlinarith [h]

/-- The test keeps the trial digit at or above any lower bound on the true digit. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_div_test_lemma2"
  (words_as_type_indexed_bitvec)]
theorem mwDivTest_lemma2 {width : Nat} [NeZero width] :
    ∀ (us vs : List (BitVec width)) (q u1 u2 u3 v1 v2 : BitVec width),
      0 < v1.toNat ∧ us.length = vs.length ∧
        mw2n (u1 :: u2 :: u3 :: us).reverse / mw2n (v1 :: v2 :: vs).reverse < 2 ^ width ∧
        mw2n (u1 :: u2 :: u3 :: us).reverse / mw2n (v1 :: v2 :: vs).reverse ≤ q.toNat →
      mw2n (u1 :: u2 :: u3 :: us).reverse / mw2n (v1 :: v2 :: vs).reverse ≤
        (mwDivTest q u1 u2 u3 v1 v2).toNat := by
  intro us vs q u1 u2 u3 v1 v2 ⟨vpos, len, _, le⟩
  generalize hQ : mw2n (u1 :: u2 :: u3 :: us).reverse / mw2n (v1 :: v2 :: vs).reverse = Q at le ⊢
  induction h : q.toNat using Nat.strong_induction_on generalizing q with
  | _ n ih =>
    rw [mwDivTest]
    split
    · rename_i hc
      have bound := (cmp_true_bound q u1 u2 u3 v1 v2).mp hc
      have p : (BitVec.ofNat width (q.toNat - 1)).toNat = q.toNat - 1 := by
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) q.isLt)
      -- the true digit is below q
      have lt : Q < q.toNat := by
        rw [← hQ]
        simp only [rev_cons_value, List.length_cons, dimwords_succ]
        rw [← len]
        have hR := rev_value_lt us
        have hS := rev_value_lt vs
        rw [← len] at hS
        have hl : 0 < dimwords width us.length := dimwords_pos _
        generalize dimwords width us.length = l at hR hS hl
        generalize mw2n us.reverse = R at hR
        generalize mw2n vs.reverse = S at hS
        have Vpos : 0 < S + l * v2.toNat + 2 ^ width * l * v1.toNat := by
          have : 0 < 2 ^ width * l * v1.toNat :=
            Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hl) vpos
          omega
        rw [Nat.div_lt_iff_lt_mul Vpos]
        have step : (u1.toNat * 2 ^ width * 2 ^ width + u2.toNat * 2 ^ width + u3.toNat + 1) * l ≤
            q.toNat * (v1.toNat * 2 ^ width + v2.toNat) * l := Nat.mul_le_mul_right _ bound
        nlinarith [step]
      simp only
      split
      · exact ih _ (by omega) _ (by omega) p
      · rw [p]; omega
    · omega

/-- The tested trial digit is the true quotient digit or one more. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_div_test_thm"
  (words_as_type_indexed_bitvec)]
theorem mwDivTest_thm {width : Nat} [NeZero width] :
    ∀ (u1 u2 u3 : BitVec width) (us : List (BitVec width)) (v1 v2 : BitVec width)
      (vs : List (BitVec width)),
      us.length = vs.length ∧ 2 ^ width / 2 ≤ v1.toNat ∧
        mw2n (u1 :: u2 :: u3 :: us).reverse / mw2n (v1 :: v2 :: vs).reverse < 2 ^ width →
      let q := if u1.toNat < v1.toNat then (singleDiv u1 u2 v1).1
        else BitVec.ofNat width (2 ^ width - 1)
      (mwDivTest q u1 u2 u3 v1 v2).toNat < 2 ^ width ∧
        ((mwDivTest q u1 u2 u3 v1 v2).toNat =
            mw2n (u1 :: u2 :: u3 :: us).reverse / mw2n (v1 :: v2 :: vs).reverse ∨
          (mwDivTest q u1 u2 u3 v1 v2).toNat =
            mw2n (u1 :: u2 :: u3 :: us).reverse / mw2n (v1 :: v2 :: vs).reverse + 1) := by
  rintro u1 u2 u3 us v1 v2 vs ⟨len, half, small⟩
  intro q
  refine ⟨BitVec.isLt _, ?_⟩
  have hb : 2 ≤ 2 ^ width := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) (Nat.pos_of_ne_zero (NeZero.ne width))
  have vpos : 0 < v1.toNat := by omega
  have len' : (u3 :: us).length = (v2 :: vs).length := by simp [len]
  have hq : q.toNat = min ((u1.toNat * 2 ^ width + u2.toNat) / v1.toNat) (2 ^ width - 1) :=
    q_of_test_choice u1 u2 v1 vpos
  have r1 := mw_div_range1 u1 u2 (u3 :: us) v1 (v2 :: vs) ⟨len', vpos, small⟩
  have r2 := mw_div_range2 u1 u2 (u3 :: us) v1 (v2 :: vs) ⟨len', small, half⟩
  rw [← hq] at r1 r2
  generalize hQ : mw2n (u1 :: u2 :: u3 :: us).reverse / mw2n (v1 :: v2 :: vs).reverse = Q at r1 r2 small
  have lo := mwDivTest_lemma2 us vs q u1 u2 u3 v1 v2 ⟨vpos, len, by rw [hQ]; exact small,
    by rw [hQ]; exact r1⟩
  rw [hQ] at lo
  have hi := mwDivTest_lemma1 q u1 u2 u3 v1 v2
  by_cases two : q.toNat = Q + 2
  · -- the first test fires, so the result is at most q - 1
    have fires : mwCmp [u3, u2, u1] (mwMulBySingle q [v2, v1]) = some true := by
      rw [cmp_true_bound]
      apply Nat.lt_of_not_le
      intro le
      have Vpos0 : 0 < mw2n (v1 :: v2 :: vs).reverse := by
        simp only [rev_cons_value]
        have : 0 < dimwords width (v2 :: vs).length * v1.toNat :=
          Nat.mul_pos (dimwords_pos _) vpos
        omega
      have hdiv0 := Nat.lt_mul_div_succ (mw2n (u1 :: u2 :: u3 :: us).reverse) Vpos0
      rw [hQ, show Q + 1 = q.toNat - 1 by omega] at hdiv0
      simp only [rev_cons_value, List.length_cons, dimwords_succ] at hdiv0
      rw [← len] at hdiv0
      have hR := rev_value_lt us
      have hS := rev_value_lt vs
      rw [← len] at hS
      have hl : 0 < dimwords width us.length := dimwords_pos _
      generalize dimwords width us.length = l at hR hS hl hdiv0
      generalize mw2n us.reverse = R at hR hdiv0
      generalize mw2n vs.reverse = S at hS hdiv0
      have qb : q.toNat ≤ 2 ^ width - 1 := by have := q.isLt; omega
      have qpos : 1 ≤ q.toNat := by omega
      generalize hT : u1.toNat * 2 ^ width * 2 ^ width + u2.toNat * 2 ^ width + u3.toNat = T at le
      generalize hW : v1.toNat * 2 ^ width + v2.toNat = W at le
      have hU : R + l * u3.toNat + 2 ^ width * l * u2.toNat + 2 ^ width * (2 ^ width * l) * u1.toNat =
          T * l + R := by rw [← hT]; ring
      have hV : S + l * v2.toNat + 2 ^ width * l * v1.toNat = W * l + S := by rw [← hW]; ring
      rw [hU, hV] at hdiv0
      -- q * V ≤ q * l + T * l ≤ q * l + U, and U < (q - 1) * V, so V < q * l
      have a1 : q.toNat * W * l ≤ T * l := Nat.mul_le_mul_right l le
      have a2 : q.toNat * S ≤ q.toNat * l := Nat.mul_le_mul_left _ (Nat.le_of_lt hS)
      have a3 : (W * l + S) * (q.toNat - 1) + (W * l + S) = (W * l + S) * q.toNat := by
        rw [← Nat.mul_succ]; congr 1; omega
      have vlt : W * l + S < q.toNat * l := by nlinarith
      have wb : 2 ^ width ≤ W := by
        rw [← hW]
        have : 2 ^ width ≤ v1.toNat * 2 ^ width := Nat.le_mul_of_pos_left _ vpos
        omega
      have : q.toNat * l < 2 ^ width * l := Nat.mul_lt_mul_of_pos_right (by omega) hl
      have : 2 ^ width * l ≤ W * l := Nat.mul_le_mul_right _ wb
      omega
    have once : (mwDivTest q u1 u2 u3 v1 v2).toNat ≤ q.toNat - 1 := by
      rw [mwDivTest, if_pos fires]
      have p : (BitVec.ofNat width (q.toNat - 1)).toNat = q.toNat - 1 := by
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) q.isLt)
      simp only
      split
      · calc _ ≤ (BitVec.ofNat width (q.toNat - 1)).toNat := mwDivTest_lemma1 _ _ _ _ _ _
          _ = _ := p
      · rw [p]
    omega
  · omega

end Flapjack.Misc.Multiword
