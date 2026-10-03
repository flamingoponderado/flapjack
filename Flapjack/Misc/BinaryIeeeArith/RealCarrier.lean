import Flapjack.Misc.BinaryIeeeArith
import Flapjack.Misc.BinaryIeeeSqrt.RealCarrier

/-!
# `binary_ieee` arithmetic and comparison over Mathlib reals

Literal transcriptions over Mathlib `ℝ` of HOL `float_add`, `float_sub`,
`float_mul`, `float_div`, `float_mul_add` and `float_compare`
(`HOL/src/floating-point/binary_ieeeScript.sml:587-777`), each built from the
arbitrary-real `float_value`/`float_to_real`/`float_round_with_flags` ports of
`Flapjack.Misc.BinaryIeeeSqrt.RealCarrier`, with every HOL clause, zero test
and comparison kept over `ℝ` (decided classically). The tagged executed
renderings in `Flapjack.Misc.BinaryIeeeArith`/`BinaryIeee` compute the same
operations through `Rat`; the theorems below prove, for every rounding mode and
input and with no premise, that each executed rendering equals its real
transcription. These transcriptions are Flapjack infrastructure: they carry no
`@[hol]` tag (the executed renderings already carry the reviewed tags, and have
HOL's exact float-valued signatures), and no HOL-to-Lean equivalence is
claimed beyond the standard reading of Mathlib `ℝ` as HOL `real`.
-/

namespace Flapjack

open Classical

/-- HOL `float_add_def` transcribed over `ℝ`. -/
noncomputable def holFloatAddR {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding)
    (x y : HolFloat t w) : HolFloatFlags × HolFloat t w :=
  match holFloatValueR x, holFloatValueR y with
  | .nan, _ => (holCheckForSignalling [x, y], holFloatSomeQnan (.fpAdd mode x y))
  | _, .nan => (holCheckForSignalling [y], holFloatSomeQnan (.fpAdd mode x y))
  | .infinity, .infinity =>
      if x.sign = y.sign then (holClearFlags, x)
      else (holInvalidopFlags, holFloatSomeQnan (.fpAdd mode x y))
  | .infinity, _ => (holClearFlags, x)
  | _, .infinity => (holClearFlags, y)
  | .float r1, .float r2 =>
      holFloatRoundWithFlagsR mode
        (if r1 = 0 ∧ r2 = 0 ∧ x.sign = y.sign then x.sign = 1 else mode = .roundTowardNegative)
        (r1 + r2)

theorem holFloatAdd_eq_real {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding)
    (x y : HolFloat t w) : holFloatAdd mode x y = holFloatAddR mode x y := by
  unfold holFloatAdd holFloatAddR
  rw [holFloatValueR_eq, holFloatValueR_eq]
  cases holFloatValue x <;> cases holFloatValue y <;> simp only []
  rename_i q1 q2
  rw [← Rat.cast_add, holFloatRoundWithFlagsR_ratCast]
  simp [Rat.cast_eq_zero]

/-- HOL `float_sub_def` transcribed over `ℝ`. -/
noncomputable def holFloatSubR {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding)
    (x y : HolFloat t w) : HolFloatFlags × HolFloat t w :=
  match holFloatValueR x, holFloatValueR y with
  | .nan, _ => (holCheckForSignalling [x, y], holFloatSomeQnan (.fpSub mode x y))
  | _, .nan => (holCheckForSignalling [y], holFloatSomeQnan (.fpSub mode x y))
  | .infinity, .infinity =>
      if x.sign = y.sign then (holInvalidopFlags, holFloatSomeQnan (.fpSub mode x y))
      else (holClearFlags, x)
  | .infinity, _ => (holClearFlags, x)
  | _, .infinity => (holClearFlags, holFloatNegate y)
  | .float r1, .float r2 =>
      holFloatRoundWithFlagsR mode
        (if r1 = 0 ∧ r2 = 0 ∧ x.sign ≠ y.sign then x.sign = 1 else mode = .roundTowardNegative)
        (r1 - r2)

theorem holFloatSub_eq_real {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding)
    (x y : HolFloat t w) : holFloatSub mode x y = holFloatSubR mode x y := by
  unfold holFloatSub holFloatSubR
  rw [holFloatValueR_eq, holFloatValueR_eq]
  cases holFloatValue x <;> cases holFloatValue y <;> simp only []
  rename_i q1 q2
  rw [← Rat.cast_sub, holFloatRoundWithFlagsR_ratCast]
  simp [Rat.cast_eq_zero]

/-- HOL `float_mul_def` transcribed over `ℝ`. -/
noncomputable def holFloatMulR {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding)
    (x y : HolFloat t w) : HolFloatFlags × HolFloat t w :=
  let signedInf : HolFloat t w :=
    if x.sign = y.sign then holFloatPlusInfinity t w else holFloatMinusInfinity t w
  match holFloatValueR x, holFloatValueR y with
  | .nan, _ => (holCheckForSignalling [x, y], holFloatSomeQnan (.fpMul mode x y))
  | _, .nan => (holCheckForSignalling [y], holFloatSomeQnan (.fpMul mode x y))
  | .infinity, .float r =>
      if r = 0 then (holInvalidopFlags, holFloatSomeQnan (.fpMul mode x y))
      else (holClearFlags, signedInf)
  | .float r, .infinity =>
      if r = 0 then (holInvalidopFlags, holFloatSomeQnan (.fpMul mode x y))
      else (holClearFlags, signedInf)
  | .infinity, .infinity => (holClearFlags, signedInf)
  | .float r1, .float r2 => holFloatRoundWithFlagsR mode (x.sign ≠ y.sign) (r1 * r2)

theorem holFloatMul_eq_real {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding)
    (x y : HolFloat t w) : holFloatMul mode x y = holFloatMulR mode x y := by
  unfold holFloatMul holFloatMulR
  rw [holFloatValueR_eq, holFloatValueR_eq]
  cases holFloatValue x <;> cases holFloatValue y <;> simp [Rat.cast_eq_zero]
  rw [← Rat.cast_mul, holFloatRoundWithFlagsR_ratCast]

/-- HOL `float_div_def` transcribed over `ℝ`. -/
noncomputable def holFloatDivR {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding)
    (x y : HolFloat t w) : HolFloatFlags × HolFloat t w :=
  let signedInf : HolFloat t w :=
    if x.sign = y.sign then holFloatPlusInfinity t w else holFloatMinusInfinity t w
  match holFloatValueR x, holFloatValueR y with
  | .nan, _ => (holCheckForSignalling [x, y], holFloatSomeQnan (.fpDiv mode x y))
  | _, .nan => (holCheckForSignalling [y], holFloatSomeQnan (.fpDiv mode x y))
  | .infinity, .infinity => (holInvalidopFlags, holFloatSomeQnan (.fpDiv mode x y))
  | .infinity, _ => (holClearFlags, signedInf)
  | _, .infinity =>
      (holClearFlags,
        if x.sign = y.sign then holFloatPlusZero t w else holFloatMinusZero t w)
  | .float r1, .float r2 =>
      if r2 = 0 then
        if r1 = 0 then (holInvalidopFlags, holFloatSomeQnan (.fpDiv mode x y))
        else (holDividezeroFlags, signedInf)
      else holFloatRoundWithFlagsR mode (x.sign ≠ y.sign) (r1 / r2)

theorem holFloatDiv_eq_real {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding)
    (x y : HolFloat t w) : holFloatDiv mode x y = holFloatDivR mode x y := by
  unfold holFloatDiv holFloatDivR
  rw [holFloatValueR_eq, holFloatValueR_eq]
  cases holFloatValue x <;> cases holFloatValue y <;> simp only []
  rename_i q1 q2
  simp only [Rat.cast_eq_zero]
  split <;> try rfl
  rw [← Rat.cast_div, holFloatRoundWithFlagsR_ratCast]

/-- HOL `float_mul_add_def` transcribed over `ℝ`. -/
noncomputable def holFloatMulAddR {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding)
    (x y z : HolFloat t w) : HolFloatFlags × HolFloat t w :=
  let signP := x.sign ^^^ y.sign
  let infP := holFloatIsInfinite x || holFloatIsInfinite y
  if holFloatIsNan x || holFloatIsNan y || holFloatIsNan z then
    (holCheckForSignalling [x, y, z], holFloatSomeQnan (.fpMulAdd mode x y z))
  else if (holFloatIsInfinite x && holFloatIsZero y) || (holFloatIsZero x && holFloatIsInfinite y) ||
      (holFloatIsInfinite z && infP && decide (signP ≠ z.sign)) then
    (holInvalidopFlags, holFloatSomeQnan (.fpMulAdd mode x y z))
  else if (holFloatIsInfinite z && decide (z.sign = 0)) || (infP && decide (signP = 0)) then
    (holClearFlags, holFloatPlusInfinity t w)
  else if (holFloatIsInfinite z && decide (z.sign = 1)) || (infP && decide (signP = 1)) then
    (holClearFlags, holFloatMinusInfinity t w)
  else
    let r1 := holFloatToRealR x * holFloatToRealR y
    let r2 := holFloatToRealR z
    let r := r1 + r2
    holFloatRoundWithFlagsR mode
      (decide (r = 0 ∧
          (if r1 = 0 ∧ r2 = 0 ∧ signP = z.sign then signP = 1 else mode = .roundTowardNegative)) ||
        decide (r < 0))
      r

theorem holFloatMulAdd_eq_real {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding)
    (x y z : HolFloat t w) : holFloatMulAdd mode x y z = holFloatMulAddR mode x y z := by
  unfold holFloatMulAdd holFloatMulAddR
  simp only [holFloatToRealR_eq_cast, ← Rat.cast_mul, ← Rat.cast_add, Rat.cast_eq_zero,
    Rat.cast_lt_zero, holFloatRoundWithFlagsR_ratCast]

/-- HOL `float_compare_def` transcribed over `ℝ`. -/
noncomputable def holFloatCompareR {t : Nat} {w : Nat} [NeZero t] [NeZero w]
    (x y : HolFloat t w) : HolFloatCompare :=
  match holFloatValueR x, holFloatValueR y with
  | .nan, _ => .un
  | _, .nan => .un
  | .infinity, .infinity =>
      if x.sign = y.sign then .eq else if x.sign = 1 then .lt else .gt
  | .infinity, _ => if x.sign = 1 then .lt else .gt
  | _, .infinity => if y.sign = 1 then .gt else .lt
  | .float r1, .float r2 => if r1 < r2 then .lt else if r1 = r2 then .eq else .gt

theorem holFloatCompare_eq_real {t : Nat} {w : Nat} [NeZero t] [NeZero w]
    (x y : HolFloat t w) : holFloatCompare x y = holFloatCompareR x y := by
  unfold holFloatCompare holFloatCompareR
  rw [holFloatValueR_eq, holFloatValueR_eq]
  cases holFloatValue x <;> cases holFloatValue y <;> simp [Rat.cast_lt, Rat.cast_inj]

end Flapjack
