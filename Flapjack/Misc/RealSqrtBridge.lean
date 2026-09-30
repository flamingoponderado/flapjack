import Mathlib.Analysis.Real.Sqrt

/-!
# Real square-root facts for binary64 rounding

This is Flapjack-side infrastructure, not a port of a HOL declaration. It
records in Lean's real-number model the comparison facts that
`Flapjack.Misc.BinaryIeeeSqrt` currently defines directly over `Rat` and leaves
as external soundness assumptions. The later exact `float_sqrt` port must
still compare its full statement and use of these facts against HOL.
-/

namespace Flapjack

/-- Embed a rational radicand in the real carrier and take its real square
root. `Real.sqrt` is total; the hypotheses on the comparison lemmas identify
the nonnegative-radicand case used by HOL `float_sqrt`. -/
noncomputable def realSqrtOfRat (r : Rat) : ℝ := Real.sqrt (r : ℝ)

theorem realSqrtOfRat_nonneg (r : Rat) : 0 ≤ realSqrtOfRat r :=
  Real.sqrt_nonneg _

theorem realSqrtOfRat_le_iff {r q : Rat} :
    realSqrtOfRat r ≤ q ↔ 0 ≤ q ∧ r ≤ q * q := by
  unfold realSqrtOfRat
  rw [Real.sqrt_le_iff]
  constructor
  · rintro ⟨hq, hrq⟩
    refine ⟨by exact_mod_cast hq, ?_⟩
    simpa [pow_two] using (show r ≤ q ^ 2 by exact_mod_cast hrq)
  · rintro ⟨hq, hrq⟩
    refine ⟨by exact_mod_cast hq, ?_⟩
    have hrq' : r ≤ q ^ 2 := by simpa [pow_two] using hrq
    exact_mod_cast hrq'

theorem realSqrtOfRat_lt_iff {r q : Rat} (hr : 0 ≤ r) (hq : 0 ≤ q) :
    realSqrtOfRat r < q ↔ r < q * q := by
  unfold realSqrtOfRat
  rw [Real.sqrt_lt (by exact_mod_cast hr) (by exact_mod_cast hq)]
  constructor
  · intro h
    have h' : r < q ^ 2 := by exact_mod_cast h
    simpa [pow_two] using h'
  · intro h
    have h' : r < q ^ 2 := by simpa [pow_two] using h
    exact_mod_cast h'

theorem realSqrtOfRat_ge_iff {r q : Rat} (hr : 0 ≤ r) :
    q ≤ realSqrtOfRat r ↔ q ≤ 0 ∨ q * q ≤ r := by
  constructor
  · intro h
    by_cases hq : q ≤ 0
    · exact Or.inl hq
    · right
      have hq' : 0 ≤ q := le_of_not_ge hq
      have hreal : (q : ℝ) ≤ Real.sqrt (r : ℝ) := by
        exact_mod_cast h
      have hsquare := (Real.le_sqrt (by exact_mod_cast hq') (by exact_mod_cast hr)).mp hreal
      have hsquare' : q ^ 2 ≤ r := by exact_mod_cast hsquare
      simpa [pow_two] using hsquare'
  · rintro (hq | hsquare)
    · exact le_trans (show (q : ℝ) ≤ 0 by exact_mod_cast hq) (Real.sqrt_nonneg _)
    · by_cases hq : q ≤ 0
      · exact le_trans (show (q : ℝ) ≤ 0 by exact_mod_cast hq) (Real.sqrt_nonneg _)
      · have hq' : 0 ≤ q := le_of_not_ge hq
        have hsquare'' : q ^ 2 ≤ r := by simpa [pow_two] using hsquare
        have hsquare' : (q : ℝ) ^ 2 ≤ (r : ℝ) := by exact_mod_cast hsquare''
        have hreal := (Real.le_sqrt (by exact_mod_cast hq') (by exact_mod_cast hr)).mpr hsquare'
        exact_mod_cast hreal

theorem realSqrtOfRat_gt_iff {r q : Rat} :
    q < realSqrtOfRat r ↔ q < 0 ∨ q * q < r := by
  by_cases hq : 0 ≤ q
  · constructor
    · intro h
      right
      unfold realSqrtOfRat at h
      have hreal : (q : ℝ) < Real.sqrt (r : ℝ) ↔
          Real.sqrt ((q : ℝ) ^ 2) < Real.sqrt (r : ℝ) := by
        rw [Real.sqrt_sq (by exact_mod_cast hq)]
      have hsquare := (Real.sqrt_lt_sqrt_iff (sq_nonneg (q : ℝ))).mp (hreal.mp h)
      have hsquare' : q ^ 2 < r := by exact_mod_cast hsquare
      simpa [pow_two] using hsquare'
    · intro h
      rcases h with hneg | hsquare
      · exact (False.elim ((not_lt_of_ge hq) hneg))
      · unfold realSqrtOfRat
        have hsquare' : q ^ 2 < r := by simpa [pow_two] using hsquare
        have hsquare'' : (q : ℝ) ^ 2 < (r : ℝ) := by exact_mod_cast hsquare'
        have hreal := (Real.sqrt_lt_sqrt_iff (sq_nonneg (q : ℝ))).mpr hsquare''
        rw [Real.sqrt_sq (by exact_mod_cast hq)] at hreal
        exact hreal
  · constructor
    · intro h
      left
      exact lt_of_not_ge hq
    · intro _
      have hqneg : q < 0 := lt_of_not_ge hq
      have hqR : (q : ℝ) < 0 := by exact_mod_cast hqneg
      unfold realSqrtOfRat
      exact hqR.trans_le (Real.sqrt_nonneg _)

theorem realSqrtOfRat_eq_iff {r q : Rat} (hr : 0 ≤ r) :
    q = realSqrtOfRat r ↔ 0 ≤ q ∧ q * q = r := by
  unfold realSqrtOfRat
  constructor
  · intro h
    have h' : Real.sqrt (r : ℝ) = (q : ℝ) := by exact_mod_cast h.symm
    have hqR : 0 ≤ (q : ℝ) := by rw [← h']; exact Real.sqrt_nonneg _
    have hq : 0 ≤ q := by exact_mod_cast hqR
    have hsquare := (Real.sqrt_eq_iff_mul_self_eq (by exact_mod_cast hr)
      (by exact_mod_cast hq)).mp h'
    exact ⟨hq, by exact_mod_cast hsquare.symm⟩
  · rintro ⟨hq, hsquare⟩
    have hsquare' : (r : ℝ) = (q : ℝ) * (q : ℝ) := by exact_mod_cast hsquare.symm
    have h' := (Real.sqrt_eq_iff_mul_self_eq (by exact_mod_cast hr)
      (by exact_mod_cast hq)).mpr hsquare'
    exact_mod_cast h'.symm

theorem real_abs_distance_le_iff (a b x : ℝ) :
    |a - x| ≤ |b - x| ↔
      a = b ∨ (a < b ∧ x ≤ (a + b) / 2) ∨ (b < a ∧ (a + b) / 2 ≤ x) := by
  rw [← sq_le_sq]
  constructor
  · intro hsquare
    rcases lt_trichotomy a b with hab | hab | hba
    · exact Or.inr (Or.inl ⟨hab, by nlinarith [hsquare]⟩)
    · exact Or.inl hab
    · exact Or.inr (Or.inr ⟨hba, by nlinarith [hsquare]⟩)
  · rintro (rfl | (⟨hab, hx⟩ | ⟨hba, hx⟩))
    · simp
    · nlinarith
    · nlinarith

theorem realSqrtOfRat_distance_le_iff {r a b : Rat} :
    |(a : ℝ) - realSqrtOfRat r| ≤ |(b : ℝ) - realSqrtOfRat r| ↔
      a = b ∨ (a < b ∧ realSqrtOfRat r ≤ (a + b) / 2) ∨
        (b < a ∧ (a + b) / 2 ≤ realSqrtOfRat r) := by
  rw [real_abs_distance_le_iff]
  norm_cast

end Flapjack
