module

public import Flapjack.Misc.Multiword.DivSingle
public import Flapjack.Misc.Multiword.CompareSigned
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Knuth's quotient-digit test and its range lemmas. -/
namespace Flapjack.Misc.Multiword
open Flapjack

private theorem pred_toNat {width : Nat} [NeZero width] (q : BitVec width) :
    (BitVec.ofNat width (q.toNat - 1)).toNat = q.toNat - 1 := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) q.isLt)

private theorem mwCmp_mulBySingle_zero {width : Nat} [NeZero width] (u1 u2 u3 v1 v2 : BitVec width) :
    mwCmp [u3, u2, u1] (mwMulBySingle 0 [v2, v1]) ≠ some true := by
  have ⟨val, len⟩ := mwMulBySingle_lemma (0 : BitVec width) [v2, v1]
  rw [mwCmpThm _ _ (by rw [len]; rfl), val]
  simp

/-- Knuth's step D3: decrease the trial quotient digit while it is too large. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_div_test_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwDivTest {width : Nat} [NeZero width] (q u1 u2 u3 v1 v2 : BitVec width) :
    BitVec width :=
  if mwCmp [u3, u2, u1] (mwMulBySingle q [v2, v1]) = some true then
    let q2 := BitVec.ofNat width (q.toNat - 1)
    let s := singleMul q2 v1 0
    if mwCmp [u2, u1] (mwAdd [s.1, s.2] [0, 1] false).1 = some true then
      mwDivTest q2 u1 u2 u3 v1 v2
    else q2
  else q
termination_by q.toNat
decreasing_by
  rename_i h _
  rw [pred_toNat]
  have : q.toNat ≠ 0 := by
    intro z
    have : q = 0 := BitVec.eq_of_toNat_eq (by simpa using z)
    subst this
    exact mwCmp_mulBySingle_zero u1 u2 u3 v1 v2 h
  omega

/-- The test never increases the trial digit. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_div_test_lemma1"
  (words_as_type_indexed_bitvec)]
theorem mwDivTest_lemma1 {width : Nat} [NeZero width] :
    ∀ (q u1 u2 u3 v1 v2 : BitVec width), (mwDivTest q u1 u2 u3 v1 v2).toNat ≤ q.toNat := by
  intro q u1 u2 u3 v1 v2
  induction h : q.toNat using Nat.strong_induction_on generalizing q with
  | _ n ih =>
    rw [mwDivTest]
    split
    · rename_i hc
      have nz : q.toNat ≠ 0 := by
        intro z
        have : q = 0 := BitVec.eq_of_toNat_eq (by simpa using z)
        subst this
        exact mwCmp_mulBySingle_zero u1 u2 u3 v1 v2 hc
      have p := pred_toNat q
      simp only
      split
      · exact Nat.le_trans (ih _ (by omega) _ p) (by omega)
      · omega
    · omega

/-- Trial quotient digit from the two leading digits. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_div_guess_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwDivGuess {width : Nat} [NeZero width] (us ys : List (BitVec width)) :
    BitVec width :=
  let q := if (holHd us).toNat < (holHd ys).toNat then
      (singleDiv (holHd us) (holHd us.tail) (holHd ys)).1
    else BitVec.ofNat width (2 ^ width - 1)
  let q2 := mwDivTest q (holHd us) (holHd us.tail) (holHd us.tail.tail) (holHd ys)
    (holHd ys.tail)
  q2

/-- Decrease the digit when its multiple exceeds the partial remainder. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_div_adjust_def"
  (words_as_type_indexed_bitvec)]
noncomputable def mwDivAdjust {width : Nat} [NeZero width] (q : BitVec width)
    (zs ys : List (BitVec width)) : BitVec width :=
  if mwCmp zs (mwMulBySingle q ys) = some true then BitVec.ofNat width (q.toNat - 1) else q

/-- Subtraction keeps the length of its first operand. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "LENGTH_mw_sub"
  (words_as_type_indexed_bitvec)]
theorem length_mwSub {width : Nat} [NeZero width] :
    ∀ (xs1 ys : List (BitVec width)) (c : Bool) (qs1 : List (BitVec width)) (c1 : Bool),
      mwSub xs1 ys c = (qs1, c1) → xs1.length = qs1.length := by
  intro xs1
  induction xs1 with
  | nil =>
    intro ys c qs1 c1 h
    simp only [mwSub, Prod.mk.injEq] at h
    rw [← h.1]
  | cons x xs ih =>
    intro ys c qs1 c1 h
    cases ys with
    | nil =>
      simp only [mwSub] at h
      rcases hz : singleSub x 0 c with ⟨z, d⟩
      rcases hr : mwSub xs [] d with ⟨zs, e⟩
      simp only [hz, hr, Prod.mk.injEq] at h
      rw [← h.1, List.length_cons, List.length_cons, ih [] d zs e hr]
    | cons y ys =>
      simp only [mwSub] at h
      rcases hz : singleSub x y c with ⟨z, d⟩
      rcases hr : mwSub xs ys d with ⟨zs, e⟩
      simp only [hz, hr, Prod.mk.injEq] at h
      rw [← h.1, List.length_cons, List.length_cons, ih ys d zs e hr]

/-- Simple division keeps the number of digits. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "LENGTH_mw_simple_div"
  (words_as_type_indexed_bitvec)]
theorem length_mwSimpleDiv {width : Nat} [NeZero width] :
    ∀ (xs : List (BitVec width)) (x ys : BitVec width) (qs : List (BitVec width))
      (r : BitVec width) (c : Bool), mwSimpleDiv x xs ys = (qs, r, c) → xs.length = qs.length := by
  intro xs
  induction xs with
  | nil =>
    intro x ys qs r c h
    simp only [mwSimpleDiv, Prod.mk.injEq] at h
    rw [← h.1]
  | cons x1 xs ih =>
    intro x ys qs r c h
    simp only [mwSimpleDiv] at h
    rcases hqr : singleDiv x x1 ys with ⟨q, r1⟩
    rcases hrest : mwSimpleDiv r1 xs ys with ⟨qs1, r2, c2⟩
    simp only [hqr, hrest, Prod.mk.injEq] at h
    rw [← h.1, List.length_cons, List.length_cons, ih r1 ys qs1 r2 c2 hrest]

private theorem mw2n_reverse_cons' {width : Nat} [NeZero width] (x : BitVec width)
    (xs : List (BitVec width)) :
    mw2n (x :: xs).reverse = mw2n xs.reverse + dimwords width xs.length * x.toNat := by
  rw [List.reverse_cons, mw2n_msf, List.length_reverse]

/-- A quotient digit in range bounds the two leading dividend digits. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "q_thm"
  (words_as_type_indexed_bitvec)]
theorem q_thm {width : Nat} [NeZero width] :
    ∀ (u1 u2 : BitVec width) (us : List (BitVec width)) (v1 : BitVec width)
      (vs : List (BitVec width)),
      us.length = vs.length ∧ 0 < v1.toNat ∧
        mw2n (u1 :: u2 :: us).reverse / mw2n (v1 :: vs).reverse < 2 ^ width →
      u1.toNat * 2 ^ width + u2.toNat < 2 ^ width * (1 + v1.toNat) := by
  rintro u1 u2 us v1 vs ⟨len, pos, small⟩
  have hD : 0 < dimwords width us.length := dimwords_pos _
  rw [mw2n_reverse_cons', mw2n_reverse_cons', List.length_cons, dimwords_succ] at small
  rw [mw2n_reverse_cons', ← len] at small
  have rv := mw2n_lt vs.reverse
  rw [List.length_reverse, ← len] at rv
  have ru := mw2n_lt us.reverse
  rw [List.length_reverse] at ru
  generalize dimwords width us.length = D at hD small rv ru
  have Vpos : 0 < mw2n vs.reverse + D * v1.toNat := by
    have : 0 < D * v1.toNat := Nat.mul_pos hD pos
    omega
  have lt := (Nat.div_lt_iff_lt_mul Vpos).mp small
  have key : D * (u1.toNat * 2 ^ width + u2.toNat) < D * (2 ^ width * (1 + v1.toNat)) := by
    have e : D * (2 ^ width * (1 + v1.toNat)) = 2 ^ width * (D + D * v1.toNat) := by ring
    rw [e]
    calc D * (u1.toNat * 2 ^ width + u2.toNat)
        ≤ mw2n us.reverse + D * u2.toNat + 2 ^ width * D * u1.toNat := by
          have : D * (u1.toNat * 2 ^ width + u2.toNat) = D * u2.toNat + 2 ^ width * D * u1.toNat := by
            ring
          omega
      _ < 2 ^ width * (mw2n vs.reverse + D * v1.toNat) := by
          linarith [lt]
      _ ≤ 2 ^ width * (D + D * v1.toNat) := Nat.mul_le_mul_left _ (by omega)
  exact Nat.lt_of_mul_lt_mul_left key

/-- The trial digit is never below the true quotient digit. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_div_range1"
  (words_as_type_indexed_bitvec)]
theorem mw_div_range1 {width : Nat} [NeZero width] :
    ∀ (u1 u2 : BitVec width) (us : List (BitVec width)) (v1 : BitVec width)
      (vs : List (BitVec width)),
      us.length = vs.length ∧ 0 < v1.toNat ∧
        mw2n (u1 :: u2 :: us).reverse / mw2n (v1 :: vs).reverse < 2 ^ width →
      min ((u1.toNat * 2 ^ width + u2.toNat) / v1.toNat) (2 ^ width - 1) ≥
        mw2n (u1 :: u2 :: us).reverse / mw2n (v1 :: vs).reverse := by
  rintro u1 u2 us v1 vs ⟨len, pos, small⟩
  rcases Nat.lt_or_ge ((u1.toNat * 2 ^ width + u2.toNat) / v1.toNat) (2 ^ width - 1) with lt | ge
  · rw [Nat.min_eq_left (Nat.le_of_lt lt)]
    have hD : 0 < dimwords width us.length := dimwords_pos _
    rw [mw2n_reverse_cons', mw2n_reverse_cons', List.length_cons, dimwords_succ,
      mw2n_reverse_cons', ← len]
    have ru := mw2n_lt us.reverse
    rw [List.length_reverse] at ru
    generalize dimwords width us.length = D at hD ru
    generalize ha : u1.toNat * 2 ^ width + u2.toNat = a
    have qa := Nat.lt_div_mul_add (a := a) pos
    generalize a / v1.toNat = Q at qa ⊢
    have Vpos : 0 < mw2n vs.reverse + D * v1.toNat := by
      have : 0 < D * v1.toNat := Nat.mul_pos hD pos
      omega
    apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul Vpos]
    have hU : mw2n us.reverse + D * u2.toNat + 2 ^ width * D * u1.toNat = mw2n us.reverse + D * a := by
      rw [← ha]; ring
    rw [hU]
    have step : D * (a + 1) ≤ D * (Q * v1.toNat + v1.toNat) := Nat.mul_le_mul_left _ qa
    have e : (Q + 1) * (mw2n vs.reverse + D * v1.toNat) =
        (Q + 1) * mw2n vs.reverse + D * (Q * v1.toNat + v1.toNat) := by ring
    show _ < (Q + 1) * _
    rw [e, Nat.mul_add D a 1, Nat.mul_one] at *
    omega
  · rw [Nat.min_eq_right ge]
    exact Nat.le_sub_one_of_lt small

end Flapjack.Misc.Multiword
