import Flapjack.Misc.BinaryIeeeRound
import Flapjack.Misc.MachineIeee

/-!
# HOL `binary_ieee` arithmetic and the `machine_ieee` fp64 lifts

A rendering of `float_add`, `float_sub`, `float_mul`, `float_div` and
`float_mul_add` from `HOL/src/floating-point/binary_ieeeScript.sml:587-722`,
together with the `fp64_add`/`fp64_sub`/`fp64_mul`/`fp64_div`/`fp64_mul_add`
lifts that `machine_ieeeLib` generates (bead `flapjack-h29l.6.2.2`).  This is
the HOL standard library, so nothing here is tagged.

Each operation returns HOL's `(flags, float)` pair.  The fp64 lifts are HOL's
`float_to_fp64 (SND (float_op mode (fp64_to_float a) ...))`.  The operations
round through the choice-based `float_round_with_flags`, and produce NaNs
through `float_some_qnan`, so they are `noncomputable`.  Bead
`flapjack-h29l.6.2.3` proves a computable binary64 agreement for
`roundTiesToEven`.
-/

namespace Flapjack

/-- HOL `float_add_def` (`binary_ieeeScript.sml:587-606`).  The cases are, in
    HOL order:
    * a NaN operand gives `float_some_qnan` with `check_for_signalling`;
    * two infinities give `x` when their signs agree and an invalid NaN
      otherwise;
    * a single infinity is returned unchanged;
    * two finite values round `r1 + r2`.  The zero sign is `x.Sign = 1w` when
      both are zero with equal signs, and `mode = roundTowardNegative`
      otherwise. -/
noncomputable def holFloatAdd {t w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (x y : HolFloat t w) :
    HolFloatFlags × HolFloat t w :=
  match holFloatValue x, holFloatValue y with
  | .nan, _ => (holCheckForSignalling [x, y], holFloatSomeQnan (.fpAdd mode x y))
  | _, .nan => (holCheckForSignalling [y], holFloatSomeQnan (.fpAdd mode x y))
  | .infinity, .infinity =>
      if x.sign = y.sign then (holClearFlags, x)
      else (holInvalidopFlags, holFloatSomeQnan (.fpAdd mode x y))
  | .infinity, _ => (holClearFlags, x)
  | _, .infinity => (holClearFlags, y)
  | .float r1, .float r2 =>
      holFloatRoundWithFlags mode
        (if r1 = 0 ∧ r2 = 0 ∧ x.sign = y.sign then x.sign = 1 else mode = .roundTowardNegative)
        (r1 + r2)

/-- HOL `float_sub_def` (`binary_ieeeScript.sml:608-627`).  It mirrors
    `float_add` with these differences:
    * infinities of the same sign are invalid;
    * `_ - Infinity` is `float_negate y`;
    * the zero sign of `0 - 0` uses `x.Sign ≠ y.Sign`. -/
noncomputable def holFloatSub {t w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (x y : HolFloat t w) :
    HolFloatFlags × HolFloat t w :=
  match holFloatValue x, holFloatValue y with
  | .nan, _ => (holCheckForSignalling [x, y], holFloatSomeQnan (.fpSub mode x y))
  | _, .nan => (holCheckForSignalling [y], holFloatSomeQnan (.fpSub mode x y))
  | .infinity, .infinity =>
      if x.sign = y.sign then (holInvalidopFlags, holFloatSomeQnan (.fpSub mode x y))
      else (holClearFlags, x)
  | .infinity, _ => (holClearFlags, x)
  | _, .infinity => (holClearFlags, holFloatNegate y)
  | .float r1, .float r2 =>
      holFloatRoundWithFlags mode
        (if r1 = 0 ∧ r2 = 0 ∧ x.sign ≠ y.sign then x.sign = 1 else mode = .roundTowardNegative)
        (r1 - r2)

/-- HOL `float_mul_def` (`binary_ieeeScript.sml:629-659`).
    * Infinity times zero is invalid.
    * Infinity times a nonzero value or infinity is an infinity signed by
      `x.Sign = y.Sign`.
    * Two finite values round `r1 * r2` with zero sign `x.Sign ≠ y.Sign`. -/
noncomputable def holFloatMul {t w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (x y : HolFloat t w) :
    HolFloatFlags × HolFloat t w :=
  let signedInf : HolFloat t w :=
    if x.sign = y.sign then holFloatPlusInfinity t w else holFloatMinusInfinity t w
  match holFloatValue x, holFloatValue y with
  | .nan, _ => (holCheckForSignalling [x, y], holFloatSomeQnan (.fpMul mode x y))
  | _, .nan => (holCheckForSignalling [y], holFloatSomeQnan (.fpMul mode x y))
  | .infinity, .float r =>
      if r = 0 then (holInvalidopFlags, holFloatSomeQnan (.fpMul mode x y))
      else (holClearFlags, signedInf)
  | .float r, .infinity =>
      if r = 0 then (holInvalidopFlags, holFloatSomeQnan (.fpMul mode x y))
      else (holClearFlags, signedInf)
  | .infinity, .infinity => (holClearFlags, signedInf)
  | .float r1, .float r2 => holFloatRoundWithFlags mode (x.sign ≠ y.sign) (r1 * r2)

/-- HOL `float_div_def` (`binary_ieeeScript.sml:661-690`).
    * Infinity over infinity is invalid.
    * Infinity over a finite value is an infinity, and a finite value over
      infinity is a zero, each signed by `x.Sign = y.Sign`.
    * `0 / 0` is invalid, and a nonzero value over zero is a signed infinity
      with the divide-by-zero flag.
    * Otherwise `r1 / r2` is rounded with zero sign `x.Sign ≠ y.Sign`. -/
noncomputable def holFloatDiv {t w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (x y : HolFloat t w) :
    HolFloatFlags × HolFloat t w :=
  let signedInf : HolFloat t w :=
    if x.sign = y.sign then holFloatPlusInfinity t w else holFloatMinusInfinity t w
  match holFloatValue x, holFloatValue y with
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
      else holFloatRoundWithFlags mode (x.sign ≠ y.sign) (r1 / r2)

/-- HOL `float_mul_add_def` (`binary_ieeeScript.sml:692-722`), with
    `signP = x.Sign ?? y.Sign` and `infP` meaning either factor is infinite.
    The checks are, in order:
    * a NaN operand;
    * an invalid infinity-times-zero, or an infinite `z` opposing an infinite
      product;
    * a positive infinity, then a negative infinity;
    * otherwise round `r = x*y + z`.  The zero sign is chosen as HOL does:
      when `r = 0` it follows the same rule as `float_add` on `x*y` and `z`,
      and a negative `r` also selects it. -/
noncomputable def holFloatMulAdd {t w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (x y z : HolFloat t w) :
    HolFloatFlags × HolFloat t w :=
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
    let r1 := holFloatToReal x * holFloatToReal y
    let r2 := holFloatToReal z
    let r := r1 + r2
    holFloatRoundWithFlags mode
      (decide (r = 0 ∧
          (if r1 = 0 ∧ r2 = 0 ∧ signP = z.sign then signP = 1 else mode = .roundTowardNegative)) ||
        decide (r < 0))
      r

/-- HOL `fp64_add mode a b = float_to_fp64 (SND (float_add mode (fp64_to_float a)
    (fp64_to_float b)))`. -/
noncomputable def holFp64Add (mode : HolRounding) (a b : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatAdd mode (holFp64ToFloat a) (holFp64ToFloat b)).2

/-- HOL `fp64_sub`, lifted like `fp64_add`. -/
noncomputable def holFp64Sub (mode : HolRounding) (a b : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatSub mode (holFp64ToFloat a) (holFp64ToFloat b)).2

/-- HOL `fp64_mul`, lifted like `fp64_add`. -/
noncomputable def holFp64Mul (mode : HolRounding) (a b : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatMul mode (holFp64ToFloat a) (holFp64ToFloat b)).2

/-- HOL `fp64_div`, lifted like `fp64_add`. -/
noncomputable def holFp64Div (mode : HolRounding) (a b : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatDiv mode (holFp64ToFloat a) (holFp64ToFloat b)).2

/-- HOL `fp64_mul_add mode a b c = float_to_fp64 (SND (float_mul_add mode
    (fp64_to_float a) (fp64_to_float b) (fp64_to_float c)))`. -/
noncomputable def holFp64MulAdd (mode : HolRounding) (a b c : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatMulAdd mode (holFp64ToFloat a) (holFp64ToFloat b) (holFp64ToFloat c)).2

end Flapjack
