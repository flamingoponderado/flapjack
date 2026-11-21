module

public import Flapjack.Misc.Multiword.CalcD
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Division of a multiword number by a single word. -/
namespace Flapjack.Misc.Multiword
open Flapjack

private theorem zero_toNat {width : Nat} [NeZero width] : (0 : BitVec width).toNat = 0 := by simp

/-- Termination measure of `mwDivBySingle` (Flapjack infrastructure): two per digit, plus one
while the leading digit is not below the divisor. -/
def divBySingleMeasure {width : Nat} [NeZero width] :
    List (BitVec width) × BitVec width → Nat
  | ([], _) => 0
  | (x :: rest, y) => 2 * (rest.length + 1) + (if x.toNat < y.toNat then 0 else 1)

private theorem singleDiv_snd_toNat {width : Nat} [NeZero width] (x1 x2 y : BitVec width)
    (hy : 0 < y.toNat) :
    (singleDiv x1 x2 y).2.toNat = (x1.toNat * 2 ^ width + x2.toNat) % y.toNat := by
  simp only [singleDiv, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hy) y.isLt)

/-- Schoolbook division of most-significant-first digits by one word. The
source's `let (q,r) = single_div ...` bindings are written as the pair projections. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_div_by_single_def"
  (words_as_type_indexed_bitvec)]
def mwDivBySingle {width : Nat} [NeZero width] :
    List (BitVec width) → BitVec width → List (BitVec width)
  | [], _ => [0]
  | [x], y =>
    (fun p : BitVec width × BitVec width =>
      if x.toNat < y.toNat then [p.2] else [p.1, p.2]) (singleDiv 0 x y)
  | x1 :: x2 :: xs, y =>
    if x1.toNat < y.toNat ∨ y.toNat = 0 then
      (singleDiv x1 x2 y).1 :: mwDivBySingle ((singleDiv x1 x2 y).2 :: xs) y
    else
      (singleDiv 0 x1 y).1 :: mwDivBySingle ((singleDiv 0 x1 y).2 :: x2 :: xs) y
termination_by xs y => divBySingleMeasure (xs, y)
decreasing_by
  all_goals simp_wf
  · simp only [divBySingleMeasure, List.length_cons]
    split <;> omega
  · rename_i h
    simp only [not_or] at h
    have hy : 0 < y.toNat := Nat.pos_of_ne_zero h.2
    have := singleDiv_snd_toNat 0 x1 y hy
    rw [zero_toNat, Nat.zero_mul, Nat.zero_add] at this
    simp only [divBySingleMeasure, List.length_cons]
    rw [if_pos (by show (singleDiv 0 x1 y).2.toNat < y.toNat; rw [this]; exact Nat.mod_lt _ hy),
      if_neg h.1]
    omega

/-- Single division over a leading digit below the divisor does not overflow. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "single_div_lemma1"
  (words_as_type_indexed_bitvec)]
theorem single_div_lemma1 {width : Nat} [NeZero width] {x1 y x2 : BitVec width} :
    x1.toNat < y.toNat → (x2.toNat + 2 ^ width * x1.toNat) / y.toNat < 2 ^ width := by
  intro h
  apply DIV_thm2 ⟨by omega, ?_⟩
  have := x2.isLt
  calc x2.toNat + 2 ^ width * x1.toNat < 2 ^ width * (x1.toNat + 1) := by
        rw [Nat.mul_add, Nat.mul_one]; omega
    _ ≤ 2 ^ width * y.toNat := Nat.mul_le_mul_left _ h

/-- The remainder of a single division is below a nonzero divisor. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "single_div_lemma2"
  (words_as_type_indexed_bitvec)]
theorem single_div_lemma2 {width : Nat} [NeZero width] {y x1 x2 : BitVec width} :
    y ≠ 0 → (singleDiv x1 x2 y).2.toNat < y.toNat := by
  intro h
  have hy := NOT_0w_bis h
  rw [singleDiv_snd_toNat _ _ _ hy]
  exact Nat.mod_lt _ hy

/-- Without overflow, single division computes quotient and remainder. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "single_div_thm"
  (words_as_type_indexed_bitvec)]
theorem single_div_thm {width : Nat} [NeZero width] :
    ∀ (x1 x2 y q r : BitVec width), singleDiv x1 x2 y = (q, r) →
      (x1.toNat * 2 ^ width + x2.toNat) / y.toNat < 2 ^ width ∧ y ≠ 0 →
      q.toNat = (x1.toNat * 2 ^ width + x2.toNat) / y.toNat ∧
        r.toNat = (x1.toNat * 2 ^ width + x2.toNat) % y.toNat := by
  intro x1 x2 y q r h ⟨small, ne⟩
  have hy := NOT_0w_bis ne
  have hr := singleDiv_snd_toNat x1 x2 y hy
  simp only [singleDiv, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, by simpa [singleDiv] using hr⟩
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt small

/-- Single division with a leading digit below the divisor satisfies the division equation. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "single_div_thm_bis"
  (words_as_type_indexed_bitvec)]
theorem single_div_thm_bis {width : Nat} [NeZero width] :
    ∀ (x1 x2 y q r : BitVec width), singleDiv x1 x2 y = (q, r) ∧ x1.toNat < y.toNat →
      q.toNat * y.toNat + r.toNat = x1.toNat * 2 ^ width + x2.toNat := by
  rintro x1 x2 y q r ⟨h, lt⟩
  have ne : y ≠ 0 := fun e => by subst e; simp at lt
  have small := single_div_lemma1 (x2 := x2) lt
  rw [Nat.add_comm, Nat.mul_comm] at small
  obtain ⟨hq, hr⟩ := single_div_thm x1 x2 y q r h ⟨small, ne⟩
  rw [hq, hr, Nat.mul_comm]
  exact Nat.div_add_mod _ _

/-- With a leading digit below the divisor, the quotient has one digit per remaining input digit. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_div_by_single_LENGTH"
  (words_as_type_indexed_bitvec)]
theorem mwDivBySingle_LENGTH {width : Nat} [NeZero width] :
    ∀ (x : BitVec width) (xs : List (BitVec width)) (y : BitVec width),
      x.toNat < y.toNat → (mwDivBySingle (x :: xs) y).length = xs.length + 1 := by
  intro x xs y lt
  have hy : 0 < y.toNat := by omega
  induction xs generalizing x with
  | nil => rw [mwDivBySingle]; simp [lt]
  | cons x2 xs ih =>
    rw [mwDivBySingle, if_pos (Or.inl lt)]
    simp only [List.length_cons]
    rw [ih _ (by rw [singleDiv_snd_toNat _ _ _ hy]; exact Nat.mod_lt _ hy)]

private theorem mw2n_reverse_cons {width : Nat} [NeZero width] (x : BitVec width)
    (xs : List (BitVec width)) :
    mw2n (x :: xs).reverse = mw2n xs.reverse + dimwords width xs.length * x.toNat := by
  rw [List.reverse_cons, mw2n_msf, List.length_reverse]

private theorem divBySingle_value {width : Nat} [NeZero width] (y : BitVec width)
    (hy : 0 < y.toNat) :
    ∀ xs : List (BitVec width),
      mwDivBySingle xs y ≠ [] ∧
      (holLast (mwDivBySingle xs y)).toNat < y.toNat ∧
      mw2n xs.reverse = y.toNat * mw2n (mwDivBySingle xs y).dropLast.reverse +
        (holLast (mwDivBySingle xs y)).toNat := by
  have hW : 0 < 2 ^ width := Nat.two_pow_pos _
  intro xs
  induction xs, y using mwDivBySingle.induct with
  | case1 y => simp [mwDivBySingle, holLast, mw2n]; omega
  | case2 x y =>
    rw [mwDivBySingle]
    have hr := singleDiv_snd_toNat 0 x y hy
    rw [zero_toNat, Nat.zero_mul, Nat.zero_add] at hr
    by_cases lt : x.toNat < y.toNat
    · simp only [lt, if_true]
      refine ⟨by simp, ?_, ?_⟩
      · simp only [holLast, hr]; exact Nat.mod_lt _ hy
      · simp only [holLast, hr, List.dropLast_singleton, List.reverse_nil, mw2n,
          List.reverse_singleton, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
        exact (Nat.mod_eq_of_lt lt).symm
    · simp only [lt, if_false]
      refine ⟨by simp, ?_, ?_⟩
      · simp only [holLast, hr]; exact Nat.mod_lt _ hy
      · simp only [holLast, List.dropLast, List.reverse_singleton, mw2n, singleDiv,
          BitVec.toNat_ofNat, Nat.mul_zero, Nat.add_zero]
        rw [zero_toNat, Nat.zero_mul, Nat.zero_add,
          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt),
          Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hy) y.isLt)]
        exact (Nat.div_add_mod _ _).symm
  | case3 x1 x2 xs y h ih =>
    rw [mwDivBySingle, if_pos h]
    have lt : x1.toNat < y.toNat := h.resolve_right (by omega)
    have hqr : singleDiv x1 x2 y = ((singleDiv x1 x2 y).1, (singleDiv x1 x2 y).2) := rfl
    generalize (singleDiv x1 x2 y).1 = q at hqr ⊢
    have ih := ih hy
    generalize (singleDiv x1 x2 y).2 = r at hqr ih ⊢
    have ne := ih.1
    have last := ih.2.1
    have val := ih.2.2
    have rlt : r.toNat < y.toNat := by
      have := single_div_lemma2 (x1 := x1) (x2 := x2) (y := y) (fun e => by subst e; simp at hy)
      rwa [hqr] at this
    have len := mwDivBySingle_LENGTH r xs y rlt
    have eqn := single_div_thm_bis x1 x2 y q r ⟨hqr, lt⟩
    refine ⟨List.cons_ne_nil _ _, ?_, ?_⟩
    · rwa [holLast_cons, if_neg ne]
    · rw [holLast_cons, if_neg ne, List.dropLast_cons_of_ne_nil ne, mw2n_reverse_cons,
        mw2n_reverse_cons, mw2n_reverse_cons]
      rw [mw2n_reverse_cons] at val
      have flen : (mwDivBySingle (r :: xs) y).dropLast.length = xs.length := by
        rw [List.length_dropLast, len]; rfl
      rw [flen]
      have d1 : dimwords width (xs.length + 1) = 2 ^ width * dimwords width xs.length :=
        dimwords_succ _
      simp only [List.length_cons, d1]
      have : dimwords width xs.length * (x1.toNat * 2 ^ width + x2.toNat) =
          dimwords width xs.length * (q.toNat * y.toNat + r.toNat) := by rw [eqn]
      nlinarith [this, val]
  | case4 x1 x2 xs y h ih =>
    rw [mwDivBySingle, if_neg h]
    simp only [not_or] at h
    have hqr : singleDiv 0 x1 y = ((singleDiv 0 x1 y).1, (singleDiv 0 x1 y).2) := rfl
    generalize (singleDiv 0 x1 y).1 = q at hqr ⊢
    have ih := ih hy
    generalize (singleDiv 0 x1 y).2 = r at hqr ih ⊢
    have ne := ih.1
    have last := ih.2.1
    have val := ih.2.2
    have hr := singleDiv_snd_toNat 0 x1 y hy
    rw [hqr, zero_toNat, Nat.zero_mul, Nat.zero_add] at hr
    have rlt : r.toNat < y.toNat := by rw [hr]; exact Nat.mod_lt _ hy
    have hq : q.toNat = x1.toNat / y.toNat := by
      have := congrArg Prod.fst hqr
      simp only [singleDiv, zero_toNat, Nat.zero_mul, Nat.zero_add] at this
      rw [← this, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x1.isLt)
    have len := mwDivBySingle_LENGTH r (x2 :: xs) y rlt
    refine ⟨List.cons_ne_nil _ _, ?_, ?_⟩
    · rwa [holLast_cons, if_neg ne]
    · rw [holLast_cons, if_neg ne, List.dropLast_cons_of_ne_nil ne]
      have flen : (mwDivBySingle (r :: x2 :: xs) y).dropLast.length = (x2 :: xs).length := by
        rw [List.length_dropLast, len]; rfl
      rw [mw2n_reverse_cons x1 (x2 :: xs), mw2n_reverse_cons q, flen]
      rw [mw2n_reverse_cons r (x2 :: xs)] at val
      have eqn : q.toNat * y.toNat + r.toNat = x1.toNat := by
        rw [hq, hr, Nat.mul_comm]; exact Nat.div_add_mod _ _
      have : dimwords width (x2 :: xs).length * x1.toNat =
          dimwords width (x2 :: xs).length * (q.toNat * y.toNat + r.toNat) := by rw [eqn]
      nlinarith [this, val]

/-- Division by a single word: the quotient digits times the divisor plus the last digit. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_div_by_single_thm"
  (words_as_type_indexed_bitvec)]
theorem mwDivBySingle_thm {width : Nat} [NeZero width] :
    ∀ (xs : List (BitVec width)) (y : BitVec width), 0 < y.toNat →
      mw2n xs.reverse = mw2n (mwMulBySingle y (mwDivBySingle xs y).dropLast.reverse) +
        (holLast (mwDivBySingle xs y)).toNat := by
  intro xs y hy
  rw [(mwMulBySingle_lemma _ _).1]
  exact (divBySingle_value y hy xs).2.2

/-- Division by a single word computes the quotient and the remainder. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_div_by_single_thm_bis"
  (words_as_type_indexed_bitvec)]
theorem mwDivBySingle_thm_bis {width : Nat} [NeZero width] :
    ∀ (xs : List (BitVec width)) (y : BitVec width), 0 < y.toNat →
      mw2n (mwDivBySingle xs y).dropLast.reverse = mw2n xs.reverse / y.toNat ∧
        (holLast (mwDivBySingle xs y)).toNat = mw2n xs.reverse % y.toNat := by
  intro xs y hy
  obtain ⟨_, last, val⟩ := divBySingle_value y hy xs
  rw [val]
  constructor
  · rw [Nat.mul_add_div hy, Nat.div_eq_of_lt last, Nat.add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt last]

/-- Division by a single word, least-significant result digit carried as the remainder. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_simple_div_def"
  (words_as_type_indexed_bitvec)]
def mwSimpleDiv {width : Nat} [NeZero width] (x : BitVec width) :
    List (BitVec width) → BitVec width → List (BitVec width) × BitVec width × Bool
  | [], _ => ([], x, true)
  | x1 :: xs, y =>
    let c1 := decide (x < y)
    let (q, r) := singleDiv x x1 y
    let (qs, r, c) := mwSimpleDiv r xs y
    (q :: qs, r, c && c1)

private theorem mwSimpleDiv_lemma {width : Nat} [NeZero width] :
    ∀ (xs : List (BitVec width)) (x y : BitVec width) (qs : List (BitVec width))
      (r : BitVec width) (c : Bool),
      mwSimpleDiv x xs y = (qs, r, c) → 0 < y.toNat → x.toNat < y.toNat →
      mwDivBySingle (x :: xs) y = qs ++ [r] ∧ c = true := by
  intro xs
  induction xs with
  | nil =>
    intro x y qs r c h hy lt
    simp only [mwSimpleDiv, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rw [mwDivBySingle]
    have hr := singleDiv_snd_toNat 0 x y hy
    rw [zero_toNat, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt lt] at hr
    dsimp only
    rw [if_pos lt]
    exact ⟨by rw [BitVec.eq_of_toNat_eq hr]; rfl, rfl⟩
  | cons x1 xs ih =>
    intro x y qs r c h hy lt
    rw [mwDivBySingle, if_pos (Or.inl lt)]
    simp only [mwSimpleDiv] at h
    rcases hqr : singleDiv x x1 y with ⟨q, r1⟩
    rcases hrest : mwSimpleDiv r1 xs y with ⟨qs1, r2, c2⟩
    simp only [hqr, hrest, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have r1lt : r1.toNat < y.toNat := by
      have := singleDiv_snd_toNat x x1 y hy
      rw [hqr] at this; rw [this]; exact Nat.mod_lt _ hy
    obtain ⟨eq, c2t⟩ := ih r1 y qs1 r2 c2 hrest hy r1lt
    simp only
    refine ⟨by rw [eq]; rfl, ?_⟩
    simp [c2t, BitVec.lt_def, lt]

private theorem mw2n_reverse_append_zero {width : Nat} [NeZero width] (xs : List (BitVec width)) :
    mw2n ((0 : BitVec width) :: xs).reverse = mw2n xs.reverse := by
  rw [mw2n_reverse_cons]; simp

/-- Simple division by a nonzero word computes the quotient and the remainder. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "mw_simple_div_thm"
  (words_as_type_indexed_bitvec)]
theorem mwSimpleDiv_thm {width : Nat} [NeZero width] :
    ∀ (xs : List (BitVec width)) (y : BitVec width) (qs : List (BitVec width))
      (r : BitVec width) (c : Bool),
      mwSimpleDiv 0 xs y = (qs, r, c) ∧ 0 < y →
      mw2n qs.reverse = mw2n xs.reverse / y.toNat ∧
        r.toNat = mw2n xs.reverse % y.toNat ∧ c = true := by
  rintro xs y qs r c ⟨h, pos⟩
  have hy : 0 < y.toNat := by simpa [BitVec.lt_def] using pos
  obtain ⟨eq, ct⟩ := mwSimpleDiv_lemma xs 0 y qs r c h hy (by simpa using hy)
  obtain ⟨q, rm⟩ := mwDivBySingle_thm_bis (0 :: xs) y hy
  rw [eq, List.dropLast_concat, mw2n_reverse_append_zero] at q
  rw [eq, mw2n_reverse_append_zero] at rm
  refine ⟨q, ?_, ct⟩
  rw [← rm]
  simp [holLast_append_singleton]

end Flapjack.Misc.Multiword
