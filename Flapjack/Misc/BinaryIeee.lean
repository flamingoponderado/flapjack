/-!
# HOL `binary_ieee` floats: carrier, values, classification and comparison

A rendering of part of HOL's IEEE-754 library
`HOL/src/floating-point/binary_ieeeScript.sml` (bead `flapjack-h29l.6.1`).
The source is the HOL standard library, outside `cakeml/`, so nothing here
carries an `@[hol]` tag; the wordSem `inst_def` port uses these definitions
through `Flapjack.Misc.MachineIeee`.

Rendering choices:
* HOL `('t, 'w) float` is `HolFloat t w`.  `'t word` and `'w word` are
  `BitVec t` and `BitVec w`, and `word1` is `BitVec 1`.  HOL
  `precision (:'t) = dimindex (:'t)` is `t`, and `bias (:'w) = INT_MAX (:'w)
  = 2 ^ (dimindex (:'w) - 1) - 1` is `holFloatBias w`.
* HOL `real` values of floats are rendered as Lean `Rat`.  Flapjack has no
  real numbers.  `float_to_real` only uses `+`, `*`, `/`, `pow` and `-1r pow`
  on rational constants, so its value is a (dyadic) rational.  The HOL
  comparisons `r1 < r2` and `r1 = r2` on such values agree with `Rat`
  comparisons, because `ℚ → ℝ` is an ordered-field embedding.  That
  agreement is a documented rendering argument, not a kernel-checked theorem
  about HOL reals.
* The Boolean HOL predicates are `Bool`-valued.

Rounding (`round`, `float_round`, the arithmetic operations) is not in this
module; see beads `flapjack-h29l.6.2` and `flapjack-h29l.6.3`.
-/

namespace Flapjack

/-- HOL `binary_ieee$float` (`binary_ieeeScript.sml:30-32`):
    `<| Sign : word1; Exponent : 'w word; Significand : 't word |>`. -/
structure HolFloat (t w : Nat) [NeZero t] [NeZero w] where
  sign : BitVec 1
  exponent : BitVec w
  significand : BitVec t
  deriving DecidableEq, Repr

/-- HOL `bias (:'w) = INT_MAX (:'w) = 2 ^ (dimindex (:'w) - 1) - 1`. -/
def holFloatBias (w : Nat) : Nat := 2 ^ (w - 1) - 1

/-- HOL `float_to_real_def` (`binary_ieeeScript.sml:47-56`) over `Rat`.
    * Exponent `0w`: `-1 pow sign * (2 / 2 pow bias) * (&significand / 2 pow
      precision)`.
    * Otherwise: `-1 pow sign * (2 pow exponent / 2 pow bias) * (1 +
      &significand / 2 pow precision)`. -/
def holFloatToReal {t w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : Rat :=
  let s : Rat := (-1) ^ x.sign.toNat
  if x.exponent = 0 then
    s * (2 / 2 ^ holFloatBias w) * ((x.significand.toNat : Rat) / 2 ^ t)
  else
    s * (2 ^ x.exponent.toNat / 2 ^ holFloatBias w) * (1 + (x.significand.toNat : Rat) / 2 ^ t)

/-- HOL `float_value = Float real | Infinity | NaN`
    (`binary_ieeeScript.sml:41-42`), with `real` rendered as `Rat`. -/
inductive HolFloatValue where
  | float (r : Rat)
  | infinity
  | nan
  deriving DecidableEq, Repr

/-- HOL `float_value_def` (`binary_ieeeScript.sml:58-63`).  An all-ones
    exponent (`UINT_MAXw`) is `Infinity` when the significand is `0w` and
    `NaN` otherwise.  Every other float is `Float (float_to_real x)`. -/
def holFloatValue {t w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : HolFloatValue :=
  if x.exponent = BitVec.allOnes w then
    if x.significand = 0 then .infinity else .nan
  else .float (holFloatToReal x)

/-- HOL `float_is_nan_def` (`binary_ieeeScript.sml:88-93`). -/
def holFloatIsNan {t w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : Bool :=
  match holFloatValue x with
  | .nan => true
  | _ => false

/-- HOL `float_is_signalling_def` (`binary_ieeeScript.sml:95-98`):
    `float_is_nan x ∧ ¬word_msb x.Significand`. -/
def holFloatIsSignalling {t w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : Bool :=
  holFloatIsNan x && !x.significand.msb

/-- HOL `float_is_infinite_def` (`binary_ieeeScript.sml:100-105`). -/
def holFloatIsInfinite {t w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : Bool :=
  match holFloatValue x with
  | .infinity => true
  | _ => false

/-- HOL `float_is_normal_def` (`binary_ieeeScript.sml:107-110`):
    `x.Exponent ≠ 0w ∧ x.Exponent ≠ UINT_MAXw`. -/
def holFloatIsNormal {t w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : Bool :=
  decide (x.exponent ≠ 0) && decide (x.exponent ≠ BitVec.allOnes w)

/-- HOL `float_is_subnormal_def` (`binary_ieeeScript.sml:112-115`):
    `x.Exponent = 0w ∧ x.Significand ≠ 0w`. -/
def holFloatIsSubnormal {t w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : Bool :=
  decide (x.exponent = 0) && decide (x.significand ≠ 0)

/-- HOL `float_is_zero_def` (`binary_ieeeScript.sml:117-122`): `Float r` with
    `r = 0`. -/
def holFloatIsZero {t w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : Bool :=
  match holFloatValue x with
  | .float r => decide (r = 0)
  | _ => false

/-- HOL `float_is_finite_def` (`binary_ieeeScript.sml:124-129`). -/
def holFloatIsFinite {t w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : Bool :=
  match holFloatValue x with
  | .float _ => true
  | _ => false

/-- HOL `float_negate_def` (`binary_ieeeScript.sml:153-155`):
    `x with Sign := ~x.Sign`. -/
def holFloatNegate {t w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : HolFloat t w :=
  { x with sign := ~~~x.sign }

/-- HOL `float_abs_def` (`binary_ieeeScript.sml:157-159`):
    `x with Sign := 0w`. -/
def holFloatAbs {t w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : HolFloat t w :=
  { x with sign := 0 }

/-- HOL `float_compare = LT | EQ | GT | UN` (`binary_ieeeScript.sml:755`). -/
inductive HolFloatCompare where
  | lt
  | eq
  | gt
  | un
  deriving DecidableEq, Repr

/-- HOL `float_compare_def` (`binary_ieeeScript.sml:758-777`), with its clauses
    in HOL order:
    * a `NaN` on either side is `UN`;
    * two infinities compare by sign;
    * one infinity is below or above every finite value according to its sign;
    * two finite values compare by their values. -/
def holFloatCompare {t w : Nat} [NeZero t] [NeZero w] (x y : HolFloat t w) : HolFloatCompare :=
  match holFloatValue x, holFloatValue y with
  | .nan, _ => .un
  | _, .nan => .un
  | .infinity, .infinity =>
      if x.sign = y.sign then .eq else if x.sign = 1 then .lt else .gt
  | .infinity, _ => if x.sign = 1 then .lt else .gt
  | _, .infinity => if y.sign = 1 then .gt else .lt
  | .float r1, .float r2 => if r1 < r2 then .lt else if r1 = r2 then .eq else .gt

/-- HOL `float_less_than_def` (`binary_ieeeScript.sml:779-782`):
    `float_compare x y = LT`. -/
def holFloatLessThan {t w : Nat} [NeZero t] [NeZero w] (x y : HolFloat t w) : Bool :=
  holFloatCompare x y == .lt

/-- HOL `float_less_equal_def` (`binary_ieeeScript.sml:784-790`): `LT` or
    `EQ`. -/
def holFloatLessEqual {t w : Nat} [NeZero t] [NeZero w] (x y : HolFloat t w) : Bool :=
  match holFloatCompare x y with
  | .lt => true
  | .eq => true
  | _ => false

/-- HOL `float_greater_than_def` (`binary_ieeeScript.sml:792-795`):
    `float_compare x y = GT`. -/
def holFloatGreaterThan {t w : Nat} [NeZero t] [NeZero w] (x y : HolFloat t w) : Bool :=
  holFloatCompare x y == .gt

/-- HOL `float_greater_equal_def` (`binary_ieeeScript.sml:797-803`): `GT` or
    `EQ`. -/
def holFloatGreaterEqual {t w : Nat} [NeZero t] [NeZero w] (x y : HolFloat t w) : Bool :=
  match holFloatCompare x y with
  | .gt => true
  | .eq => true
  | _ => false

/-- HOL `float_equal_def` (`binary_ieeeScript.sml:805-808`):
    `float_compare x y = EQ`. -/
def holFloatEqual {t w : Nat} [NeZero t] [NeZero w] (x y : HolFloat t w) : Bool :=
  holFloatCompare x y == .eq

end Flapjack
