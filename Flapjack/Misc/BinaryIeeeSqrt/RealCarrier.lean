import Flapjack.HolRef
import Flapjack.Misc.BinaryIeeeSqrt.RoundAgreement

/-!
# HOL `binary_ieee` rounding and `float_sqrt` over Mathlib reals

Literal renderings, over Mathlib's `ℝ` as the carrier of HOL `real`, of the HOL
`binary_ieeeScript.sml` definitions that `fp64_sqrt` passes through:
`float_value`/`float_to_real` (41-63), `is_closest`/`closest_such`/`closest`
(253-353), `largest`/`threshold` (355-365), `round` (411-443), `float_round`
(505-515), `float_round_with_flags` (517-532) and `float_sqrt` (574-585), with
HOL `sqrt` as `Real.sqrt`. Unlike the sqrt-specialised real renderings of
`RoundAgreement` (which read every comparison directly against `sqrt r` and drop
the `abs` that `sqrt r ≥ 0` makes redundant), these take an arbitrary real
argument and keep every HOL clause, `abs` and flag test as written; HOL's choice
operator is `Classical.epsilon` and propositions are decided classically.

The theorems prove that at `x = Real.sqrt r` these literal renderings coincide
with the sqrt-specialised real renderings, so by `holFloatSqrt_agreement` the
executed rational-cut `holFloatSqrt`/`holFp64Sqrt` equal the literal real
`holFloatSqrtR`/`holFp64SqrtR` for every rounding mode and input, with no
supplied agreement, radicand, success or target premise.

These are Flapjack-specific infrastructure: everything is proved inside Lean,
no HOL-to-Lean equivalence is assumed or established (Mathlib `ℝ` as HOL `real`
is the standard carrier reading), and only the fixed-width binary64 wrapper below is source-tagged. Generic
`HolFloat t w` infrastructure remains untagged: its broad carrier permits zero
widths beyond HOL's positive type dimensions. The executed compiler continues
using the cut rendering, with the unconditional equality below connecting it
to the reviewed binary64 real specification.
-/

namespace Flapjack

open Classical

/-- HOL `float_value = Float real | Infinity | NaN` (`binary_ieeeScript.sml:41-42`)
with HOL `real` as Mathlib `ℝ`. -/
inductive HolFloatValueR where
  | float (r : ℝ)
  | infinity
  | nan

/-- HOL `float_to_real_def` (`binary_ieeeScript.sml:47-56`) over `ℝ`. -/
noncomputable def holFloatToRealR {t w : Nat} (x : HolFloat t w) : ℝ :=
  let s : ℝ := (-1) ^ x.sign.toNat
  if x.exponent = 0 then
    s * (2 / 2 ^ holFloatBias w) * ((x.significand.toNat : ℝ) / 2 ^ t)
  else
    s * (2 ^ x.exponent.toNat / 2 ^ holFloatBias w) * (1 + (x.significand.toNat : ℝ) / 2 ^ t)

/-- HOL `float_value_def` (`binary_ieeeScript.sml:58-63`) over `ℝ`. -/
noncomputable def holFloatValueR {t w : Nat} (x : HolFloat t w) : HolFloatValueR :=
  if x.exponent = BitVec.allOnes w then
    if x.significand = 0 then .infinity else .nan
  else .float (holFloatToRealR x)

/-- HOL `is_closest_def` (`binary_ieeeScript.sml:253-257`) over `ℝ`. -/
def holIsClosestR {t w : Nat} (s : HolFloat t w → Prop) (x : ℝ) (a : HolFloat t w) : Prop :=
  s a ∧ ∀ b, s b → |holFloatToRealR a - x| ≤ |holFloatToRealR b - x|

/-- HOL `closest_such_def` (`binary_ieeeScript.sml:347-350`) over `ℝ`. -/
noncomputable def holClosestSuchR {t w : Nat} (p : HolFloat t w → Prop)
    (s : HolFloat t w → Prop) (x : ℝ) : HolFloat t w :=
  Classical.epsilon (fun a => holIsClosestR s x a ∧ ∀ b, holIsClosestR s x b ∧ p b → p a)

/-- HOL `closest_def` (`binary_ieeeScript.sml:352-353`) over `ℝ`. -/
noncomputable def holClosestR {t w : Nat} (s : HolFloat t w → Prop) (x : ℝ) : HolFloat t w :=
  holClosestSuchR (fun _ => True) s x

/-- HOL `largest_def` (`binary_ieeeScript.sml:355-359`) over `ℝ`. -/
noncomputable def holFloatLargestR (t w : Nat) : ℝ :=
  (2 ^ (holUintMax w - 1) / 2 ^ holFloatBias w) * (2 - (2 ^ t : ℝ)⁻¹)

/-- HOL `threshold_def` (`binary_ieeeScript.sml:361-365`) over `ℝ`. -/
noncomputable def holFloatThresholdR (t w : Nat) : ℝ :=
  (2 ^ (holUintMax w - 1) / 2 ^ holFloatBias w) * (2 - (2 ^ (t + 1) : ℝ)⁻¹)

/-- HOL `round_def` (`binary_ieeeScript.sml:411-443`) over `ℝ`, all four modes. -/
noncomputable def holRoundR {t w : Nat} (mode : HolRounding) (x : ℝ) : HolFloat t w :=
  match mode with
  | .roundTiesToEven =>
      let th := holFloatThresholdR t w
      if x ≤ -th then holFloatMinusInfinity t w
      else if x ≥ th then holFloatPlusInfinity t w
      else holClosestSuchR (fun a => a.significand.getLsbD 0 = false)
        (fun a => holFloatIsFinite a = true) x
  | .roundTowardZero =>
      let th := holFloatLargestR t w
      if x < -th then holFloatBottom t w
      else if x > th then holFloatTop t w
      else holClosestR (fun a => holFloatIsFinite a = true ∧ |holFloatToRealR a| ≤ |x|) x
  | .roundTowardPositive =>
      let th := holFloatLargestR t w
      if x < -th then holFloatBottom t w
      else if x > th then holFloatPlusInfinity t w
      else holClosestR (fun a => holFloatIsFinite a = true ∧ holFloatToRealR a ≥ x) x
  | .roundTowardNegative =>
      let th := holFloatLargestR t w
      if x < -th then holFloatMinusInfinity t w
      else if x > th then holFloatTop t w
      else holClosestR (fun a => holFloatIsFinite a = true ∧ holFloatToRealR a ≤ x) x

/-- HOL `float_round_def` (`binary_ieeeScript.sml:507-515`) over `ℝ`. -/
noncomputable def holFloatRoundR {t w : Nat} (mode : HolRounding) (toneg : Bool) (r : ℝ) :
    HolFloat t w :=
  let x : HolFloat t w := holRoundR mode r
  if holFloatIsZero x then
    if toneg then holFloatMinusZero t w else holFloatPlusZero t w
  else x

/-- HOL `float_round_with_flags_def` (`binary_ieeeScript.sml:517-532`) over `ℝ`;
`a = abs r` and `inexact = (float_value x ≠ Float r)` as in HOL. -/
noncomputable def holFloatRoundWithFlagsR {t w : Nat} (mode : HolRounding) (toNeg : Bool)
    (r : ℝ) : HolFloatFlags × HolFloat t w :=
  let x : HolFloat t w := holFloatRoundR mode toNeg r
  let a := |r|
  let inexact := decide (holFloatValueR x ≠ .float r)
  ({ holClearFlags with
      overflow := holFloatIsInfinite x || decide ((2 : ℝ) ^ holIntMin w ≤ a)
      underflowBeforeRounding := inexact && decide (a < 2 / 2 ^ holFloatBias w)
      underflowAfterRounding := inexact &&
        decide ((holFloatRoundR mode toNeg r : HolFloat t (w + 1)).exponent ≤
          BitVec.ofNat (w + 1) (holIntMin w))
      precision := inexact }, x)

/-- HOL `float_sqrt_def` (`binary_ieeeScript.sml:574-585`) over `ℝ`, with HOL `sqrt`
as `Real.sqrt`. -/
noncomputable def holFloatSqrtR {t w : Nat} (mode : HolRounding) (x : HolFloat t w) :
    HolFloatFlags × HolFloat t w :=
  if x.sign = 0 then
    match holFloatValueR x with
    | .nan => (holCheckForSignalling [x], holFloatSomeQnan (.fpSqrt mode x))
    | .infinity => (holClearFlags, holFloatPlusInfinity t w)
    | .float r => holFloatRoundWithFlagsR mode false (Real.sqrt r)
  else if x = holFloatMinusZero t w then (holClearFlags, holFloatMinusZero t w)
  else (holInvalidopFlags, holFloatSomeQnan (.fpSqrt mode x))

/-- Source-reviewed generated HOL `machine_ieee$fp64_sqrt` at the literal
52/11/64 factory invocation. Its unary flag-dropping lift is
`float_to_fp64 (SND (float_sqrt mode (fp64_to_float a)))`.
The reachable real specification retains all original rounding, flag, choice,
signed-zero and NaN clauses over Mathlib `ℝ`; the cut-to-real equality below
requires no assumed cut criterion. The conservative IEEE qualifier remains
because the codecs and real/zero/classification helpers are in the reviewed
rendering family; it does not claim an independent HOL-to-Lean equivalence
proof. Generic real helpers are infrastructure, not generic HOL ports. -/
@[hol "HOL/src/floating-point/machine_ieeeScript.sml" "fp64_sqrt_def" 16
  (reals_as_rational_cuts)]
noncomputable def holFp64SqrtR (mode : HolRounding) (a : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatSqrtR mode (holFp64ToFloat a)).2

/-! ## The real carrier at `Real.sqrt r` is the sqrt-specialised real rendering -/

theorem holFloatToRealR_eq_cast {t w : Nat} (x : HolFloat t w) :
    holFloatToRealR x = (holFloatToReal x : ℝ) := by
  unfold holFloatToRealR holFloatToReal
  split <;> push_cast <;> rfl

theorem holFloatValueR_eq {t w : Nat} (x : HolFloat t w) :
    holFloatValueR x = match holFloatValue x with
      | .float q => .float (q : ℝ)
      | .infinity => .infinity
      | .nan => .nan := by
  unfold holFloatValueR holFloatValue
  split
  · split <;> rfl
  · simp [holFloatToRealR_eq_cast]

theorem holFloatLargestR_eq_cast (t w : Nat) :
    holFloatLargestR t w = (holFloatLargest t w : ℝ) := by
  unfold holFloatLargestR holFloatLargest; push_cast; rfl

theorem holFloatThresholdR_eq_cast (t w : Nat) :
    holFloatThresholdR t w = (holFloatThreshold t w : ℝ) := by
  unfold holFloatThresholdR holFloatThreshold; push_cast; rfl

theorem holRatAbs_cast (q : Rat) : ((holRatAbs q : Rat) : ℝ) = |(q : ℝ)| := by
  unfold holRatAbs
  split
  · rename_i h
    have : (q : ℝ) < 0 := by exact_mod_cast h
    rw [abs_of_neg this]; push_cast; rfl
  · rename_i h
    have : (0 : ℝ) ≤ q := by exact_mod_cast (not_lt.mp h)
    rw [abs_of_nonneg this]

theorem holIsClosestR_sqrt {t w : Nat} (s : HolFloat t w → Prop) (r : Rat) (a : HolFloat t w) :
    holIsClosestR s (realSqrtOfRat r) a ↔ holIsClosestSqrtReal s r a := by
  unfold holIsClosestR holIsClosestSqrtReal realSqrtDistLe
  simp only [holFloatToRealR_eq_cast]

theorem holClosestSuchR_sqrt {t w : Nat} (p s : HolFloat t w → Prop) (r : Rat) :
    holClosestSuchR p s (realSqrtOfRat r) = holClosestSuchSqrtReal p s r := by
  unfold holClosestSuchR holClosestSuchSqrtReal
  congr 1
  funext a
  simp only [holIsClosestR_sqrt]

theorem holClosestR_sqrt {t w : Nat} (s : HolFloat t w → Prop) (r : Rat) :
    holClosestR s (realSqrtOfRat r) = holClosestSqrtReal s r :=
  holClosestSuchR_sqrt (fun _ => True) s r

/-- HOL `round mode (sqrt r)` over the real carrier is the sqrt-specialised real
rendering, for every mode and every rational `r` (`Real.sqrt` is nonnegative). -/
theorem holRoundR_sqrt {t w : Nat} (mode : HolRounding) (r : Rat) :
    (holRoundR mode (realSqrtOfRat r) : HolFloat t w) = holRoundSqrtReal mode r := by
  have hs : |realSqrtOfRat r| = realSqrtOfRat r := abs_of_nonneg (realSqrtOfRat_nonneg r)
  cases mode with
  | roundTiesToEven =>
      simp only [holRoundR, holRoundSqrtReal, holFloatThresholdR_eq_cast, holClosestSuchR_sqrt]
      push_cast; rfl
  | roundTowardZero =>
      simp only [holRoundR, holRoundSqrtReal, holFloatLargestR_eq_cast, hs]
      push_cast
      congr 2
      rw [holClosestR_sqrt]
      congr 1
      funext a
      rw [holFloatToRealR_eq_cast, holRatAbs_cast]
  | roundTowardPositive =>
      simp only [holRoundR, holRoundSqrtReal, holFloatLargestR_eq_cast]
      push_cast
      congr 2
      rw [holClosestR_sqrt]
      congr 1
      funext a
      rw [holFloatToRealR_eq_cast]
  | roundTowardNegative =>
      simp only [holRoundR, holRoundSqrtReal, holFloatLargestR_eq_cast]
      push_cast
      congr 2
      rw [holClosestR_sqrt]
      congr 1
      funext a
      rw [holFloatToRealR_eq_cast]

theorem holFloatRoundR_sqrt {t w : Nat} (mode : HolRounding) (toneg : Bool) (r : Rat) :
    (holFloatRoundR mode toneg (realSqrtOfRat r) : HolFloat t w) =
      holFloatRoundSqrtReal mode toneg r := by
  unfold holFloatRoundR holFloatRoundSqrtReal
  rw [holRoundR_sqrt mode r]

theorem holFloatRoundWithFlagsR_sqrt {t w : Nat} (mode : HolRounding) (toNeg : Bool) (r : Rat) :
    (holFloatRoundWithFlagsR mode toNeg (realSqrtOfRat r) : HolFloatFlags × HolFloat t w) =
      holFloatRoundWithFlagsSqrtReal mode toNeg r := by
  have hs : |realSqrtOfRat r| = realSqrtOfRat r := abs_of_nonneg (realSqrtOfRat_nonneg r)
  unfold holFloatRoundWithFlagsR holFloatRoundWithFlagsSqrtReal
  simp only [holFloatRoundR_sqrt mode toNeg r, hs, holFloatValueR_eq]
  push_cast
  cases holFloatValue (holFloatRoundSqrtReal mode toNeg r : HolFloat t w) <;> simp

/-- HOL `float_sqrt mode` over the real carrier is the sqrt-specialised real
rendering, for every mode and input. -/
theorem holFloatSqrtR_eq_real {t w : Nat} (mode : HolRounding) (x : HolFloat t w) :
    holFloatSqrtR mode x = holFloatSqrtReal mode x := by
  unfold holFloatSqrtR holFloatSqrtReal
  rw [holFloatValueR_eq]
  cases holFloatValue x with
  | nan => rfl
  | infinity => rfl
  | float q =>
      simp only [← holFloatRoundWithFlagsR_sqrt]
      rfl

/-- The executed rational-cut `float_sqrt` equals the literal real-carrier HOL
`float_sqrt`, for every rounding mode and input (no premise). -/
theorem holFloatSqrt_eq_holFloatSqrtR {t w : Nat} (mode : HolRounding) (x : HolFloat t w) :
    holFloatSqrt mode x = holFloatSqrtR mode x :=
  (holFloatSqrt_agreement mode x).trans (holFloatSqrtR_eq_real mode x).symm

/-- The executed rational-cut `fp64_sqrt` equals the literal real-carrier HOL
`fp64_sqrt`, for every rounding mode and input (no premise). -/
theorem holFp64Sqrt_eq_holFp64SqrtR (mode : HolRounding) (a : BitVec 64) :
    holFp64Sqrt mode a = holFp64SqrtR mode a := by
  unfold holFp64Sqrt holFp64SqrtR
  rw [holFloatSqrt_eq_holFloatSqrtR]

end Flapjack
