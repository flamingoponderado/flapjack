import Flapjack.Misc.BinaryIeeeArith
import Flapjack.Misc.BinaryIeeeSqrt.RealCarrier

/-!
# HOL `binary_ieee` definitions not reached by `wordSem`

The thirteen `HOL/src/floating-point/binary_ieeeScript.sml` definitions that the
`machine_ieee` `fp64_*` operations used by `wordSem` `inst`/`fpSem` do not reach
(bead `flapjack-h29l.6.2.11`): `is_integral` (137), `float_is_integral` (140-145),
`ULP` (371-374), `ulp` (378), `integral_round` (445-475),
`float_round_to_integral` (548-552), `real_to_float_with_flags` (tagged in
`Flapjack.Misc.BinaryIeeeSqrt.RealCarrier`), `float_mul_sub` (724-749),
`float_unordered` (810-813), `exponent_boundary` (815-819), `float_ulp`
(4359-4361), `next_hi` (4437-4445) and `next_lo` (4447-4455).

HOL `real` is Mathlib `ℝ` where a definition takes an arbitrary real
(`is_integral`, `ULP`, `integral_round`), as in `RealCarrier`; `float_mul_sub`
rounds a product difference of float values, which is rational, and so follows the
tagged `float_mul_add` port over the `Rat` rendering. HOL's choice operator is
`Classical.epsilon` and propositions are decided classically. HOL `precision` is a
local overload of `dimindex`, so `precision (:'t)` is `t`; HOL `UINT_MAXw` on the
significand is `BitVec.allOnes t` and `<₊` is unsigned `<`.
-/

namespace Flapjack

open Classical

/-- HOL `is_integral_def` (`binary_ieeeScript.sml:137`):
`is_integral r = ?n. abs r = &(n:num)`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "is_integral_def"
  (reals_as_rational_cuts)]
def holIsIntegralR (r : ℝ) : Prop := ∃ n : Nat, |r| = n

/-- HOL `float_is_integral_def` (`binary_ieeeScript.sml:140-145`). -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_is_integral_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
def holFloatIsIntegralR {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : Prop :=
  match holFloatValueR x with
  | .float r => holIsIntegralR r
  | _ => False

/-- HOL `ULP_def` (`binary_ieeeScript.sml:371-374`):
`ULP (e, (:'t)) = 2 pow (if e = 0w then 1 else w2n e) / 2 pow (bias (:'w) + precision (:'t))`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "ULP_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
noncomputable def holULP {t : Nat} {w : Nat} [NeZero t] [NeZero w] (e : BitVec w) : ℝ :=
  2 ^ (if e = 0 then 1 else e.toNat) / 2 ^ (holFloatBias w + t)

/-- HOL `ulp_def` (`binary_ieeeScript.sml:378`): `ulp (:'t # 'w) = ULP (0w, (:'t))`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "ulp_def"
  (word_dimensions_as_widths := [t, w]) (reals_as_rational_cuts)]
noncomputable def holUlp (t : Nat) (w : Nat) [NeZero t] [NeZero w] : ℝ :=
  holULP (t := t) (0 : BitVec w)

/-- HOL `integral_round_def` (`binary_ieeeScript.sml:445-475`) over `ℝ`, all four
modes. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "integral_round_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
noncomputable def holIntegralRound {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding)
    (x : ℝ) : HolFloat t w :=
  match mode with
  | .roundTiesToEven =>
      let th := holFloatThresholdR t w
      if x ≤ -th then holFloatMinusInfinity t w
      else if x ≥ th then holFloatPlusInfinity t w
      else holClosestSuchR (fun a => ∃ n : Nat, Even n ∧ |holFloatToRealR a| = n)
        holFloatIsIntegralR x
  | .roundTowardZero =>
      let th := holFloatLargestR t w
      if x < -th then holFloatBottom t w
      else if x > th then holFloatTop t w
      else holClosestR (fun a => holFloatIsIntegralR a ∧ |holFloatToRealR a| ≤ |x|) x
  | .roundTowardPositive =>
      let th := holFloatLargestR t w
      if x < -th then holFloatBottom t w
      else if x > th then holFloatPlusInfinity t w
      else holClosestR (fun a => holFloatIsIntegralR a ∧ holFloatToRealR a ≥ x) x
  | .roundTowardNegative =>
      let th := holFloatLargestR t w
      if x < -th then holFloatMinusInfinity t w
      else if x > th then holFloatTop t w
      else holClosestR (fun a => holFloatIsIntegralR a ∧ holFloatToRealR a ≤ x) x

/-- HOL `float_round_to_integral_def` (`binary_ieeeScript.sml:548-552`). -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_round_to_integral_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
noncomputable def holFloatRoundToIntegral {t : Nat} {w : Nat} [NeZero t] [NeZero w]
    (mode : HolRounding) (x : HolFloat t w) : HolFloat t w :=
  match holFloatValueR x with
  | .float r => holIntegralRound mode r
  | _ => x

/-- HOL `float_mul_sub_def` (`binary_ieeeScript.sml:724-749`), clause for clause.
As in HOL, the invalid-operation case names `FP_MulAdd`, the infinity cases test
`z.Sign = 1w` (positive) and `z.Sign = 0w` (negative), and the zero sign is chosen
from `signP <> z.Sign` without a sign-of-result disjunct. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_mul_sub_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
noncomputable def holFloatMulSub {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding)
    (x y z : HolFloat t w) : HolFloatFlags × HolFloat t w :=
  let signP := x.sign ^^^ y.sign
  let infP := holFloatIsInfinite x || holFloatIsInfinite y
  if holFloatIsNan x || holFloatIsNan y || holFloatIsNan z then
    (holCheckForSignalling [x, y, z], holFloatSomeQnan (.fpMulSub mode x y z))
  else if (holFloatIsInfinite x && holFloatIsZero y) || (holFloatIsZero x && holFloatIsInfinite y) ||
      (holFloatIsInfinite z && infP && decide (signP = z.sign)) then
    (holInvalidopFlags, holFloatSomeQnan (.fpMulAdd mode x y z))
  else if (holFloatIsInfinite z && decide (z.sign = 1)) || (infP && decide (signP = 0)) then
    (holClearFlags, holFloatPlusInfinity t w)
  else if (holFloatIsInfinite z && decide (z.sign = 0)) || (infP && decide (signP = 1)) then
    (holClearFlags, holFloatMinusInfinity t w)
  else
    let r1 := holFloatToReal x * holFloatToReal y
    let r2 := holFloatToReal z
    holFloatRoundWithFlags mode
      (decide (if r1 = 0 ∧ r2 = 0 ∧ signP ≠ z.sign then signP = 1 else mode = .roundTowardNegative))
      (r1 - r2)

/-- HOL `float_unordered_def` (`binary_ieeeScript.sml:810-813`):
`float_compare x y = UN`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_unordered_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
def holFloatUnordered {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x y : HolFloat t w) : Bool :=
  decide (holFloatCompare x y = .un)

/-- HOL `exponent_boundary_def` (`binary_ieeeScript.sml:815-819`). -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "exponent_boundary_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
def holExponentBoundary {t : Nat} {w : Nat} [NeZero t] [NeZero w] (y x : HolFloat t w) : Prop :=
  x.sign = y.sign ∧ x.exponent.toNat = y.exponent.toNat + 1 ∧ x.exponent ≠ 1 ∧
    y.significand = -1 ∧ x.significand = 0

/-- HOL `float_ulp_def` (`binary_ieeeScript.sml:4359-4361`):
`float_ulp f = ULP (f.Exponent, (:'t))`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_ulp_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
noncomputable def holFloatUlp {t : Nat} {w : Nat} [NeZero t] [NeZero w] (f : HolFloat t w) : ℝ :=
  holULP (t := t) f.exponent

/-- HOL `next_hi_def` (`binary_ieeeScript.sml:4437-4445`). -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "next_hi_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
def holNextHi {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : HolFloat t w :=
  if x.significand < BitVec.allOnes t then { x with significand := x.significand + 1 }
  else { sign := x.sign, exponent := x.exponent + 1, significand := 0 }

/-- HOL `next_lo_def` (`binary_ieeeScript.sml:4447-4455`). -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "next_lo_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
def holNextLo {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : HolFloat t w :=
  if 0 < x.significand then { x with significand := x.significand - 1 }
  else { sign := x.sign, exponent := x.exponent - 1, significand := BitVec.allOnes t }

end Flapjack
