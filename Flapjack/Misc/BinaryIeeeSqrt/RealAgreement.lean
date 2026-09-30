import Flapjack.Misc.BinaryIeeeSqrt
import Flapjack.Misc.RealSqrtBridge

/-!
# Agreement between the current rational cuts and real square-root comparisons

This module is Flapjack-specific infrastructure. HOL's `float_sqrt` uses the
real square root directly; `BinaryIeeeSqrt.lean` keeps executable rational
comparisons. The theorems below establish their mathematical relation inside
Lean's real model. They do not by themselves port or tag HOL `float_sqrt`.
-/

namespace Flapjack

theorem holSqrtLe_real_iff {r q : Rat} :
    holSqrtLe r q ↔ realSqrtOfRat r ≤ q := by
  unfold holSqrtLe
  exact (realSqrtOfRat_le_iff (r := r) (q := q)).symm

theorem holSqrtLt_real_iff {r q : Rat} (hr : 0 ≤ r) :
    holSqrtLt r q ↔ realSqrtOfRat r < q := by
  unfold holSqrtLt
  constructor
  · rintro ⟨hq, hrq⟩
    exact (realSqrtOfRat_lt_iff hr (le_of_lt hq)).2 hrq
  · intro h
    have hqReal : 0 < (q : ℝ) := lt_of_le_of_lt (realSqrtOfRat_nonneg r) h
    have hq : 0 < q := by exact_mod_cast hqReal
    exact ⟨hq, (realSqrtOfRat_lt_iff hr hq.le).1 h⟩

theorem holSqrtGe_real_iff {r q : Rat} (hr : 0 ≤ r) :
    holSqrtGe r q ↔ q ≤ realSqrtOfRat r := by
  unfold holSqrtGe
  exact (realSqrtOfRat_ge_iff hr).symm

theorem holSqrtGt_real_iff {r q : Rat} :
    holSqrtGt r q ↔ q < realSqrtOfRat r := by
  unfold holSqrtGt
  exact (realSqrtOfRat_gt_iff).symm

theorem holSqrtEq_real_iff {r q : Rat} (hr : 0 ≤ r) :
    holSqrtEq r q ↔ q = realSqrtOfRat r := by
  unfold holSqrtEq
  exact (realSqrtOfRat_eq_iff hr).symm

theorem holSqrtDistLe_real_iff {r a b : Rat} (hr : 0 ≤ r) :
    holSqrtDistLe r a b ↔
      |(a : ℝ) - realSqrtOfRat r| ≤ |(b : ℝ) - realSqrtOfRat r| := by
  unfold holSqrtDistLe
  rw [holSqrtLe_real_iff, holSqrtGe_real_iff hr]
  exact_mod_cast (realSqrtOfRat_distance_le_iff (r := r) (a := a) (b := b)).symm

end Flapjack
