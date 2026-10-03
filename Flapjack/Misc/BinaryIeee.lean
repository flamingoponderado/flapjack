import Flapjack.HolRef

/-!
# HOL `binary_ieee` floats: carrier, values, classification and comparison

A rendering of part of HOL's IEEE-754 library
`HOL/src/floating-point/binary_ieeeScript.sml` (bead `flapjack-h29l.6.1`).
Declarations matching the pinned HOL source are tagged with references to
`HOL/src/floating-point/binary_ieeeScript.sml` (bead `flapjack-h29l.6.2.8`);
the wordSem `inst_def` port uses them through `Flapjack.Misc.MachineIeee`.
`HolFloatValue` carries `Rat` where HOL `float_value` carries `real` and its
own source names no rendering declaration, so it stays untagged; the tagged
`float_value` datatype over Mathlib `ℝ` is `HolFloatValueR`
(`Flapjack.Misc.BinaryIeeeSqrt.RealCarrier`).

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
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float" 32
  (words_as_type_indexed_bitvec)]
structure HolFloat (t : Nat) (w : Nat) [NeZero t] [NeZero w] where
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
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_to_real_def"
  (words_as_type_indexed_bitvec)
  (reals_as_rational_cuts)]
def holFloatToReal {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : Rat :=
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
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_value_def"
  (words_as_type_indexed_bitvec)
  (reals_as_rational_cuts)]
def holFloatValue {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : HolFloatValue :=
  if x.exponent = BitVec.allOnes w then
    if x.significand = 0 then .infinity else .nan
  else .float (holFloatToReal x)

/-- HOL `float_is_nan_def` (`binary_ieeeScript.sml:88-93`). -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_is_nan_def"
  (words_as_type_indexed_bitvec)
  (reals_as_rational_cuts)]
def holFloatIsNan {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : Bool :=
  match holFloatValue x with
  | .nan => true
  | _ => false

/-- HOL `float_is_signalling_def` (`binary_ieeeScript.sml:95-98`):
    `float_is_nan x ∧ ¬word_msb x.Significand`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_is_signalling_def"
  (words_as_type_indexed_bitvec)
  (reals_as_rational_cuts)]
def holFloatIsSignalling {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : Bool :=
  holFloatIsNan x && !x.significand.msb

/-- HOL `float_is_infinite_def` (`binary_ieeeScript.sml:100-105`). -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_is_infinite_def"
  (words_as_type_indexed_bitvec)
  (reals_as_rational_cuts)]
def holFloatIsInfinite {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : Bool :=
  match holFloatValue x with
  | .infinity => true
  | _ => false

/-- HOL `float_is_normal_def` (`binary_ieeeScript.sml:107-110`):
    `x.Exponent ≠ 0w ∧ x.Exponent ≠ UINT_MAXw`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_is_normal_def"
  (words_as_type_indexed_bitvec)]
def holFloatIsNormal {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : Bool :=
  decide (x.exponent ≠ 0) && decide (x.exponent ≠ BitVec.allOnes w)

/-- HOL `float_is_subnormal_def` (`binary_ieeeScript.sml:112-115`):
    `x.Exponent = 0w ∧ x.Significand ≠ 0w`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_is_subnormal_def"
  (words_as_type_indexed_bitvec)]
def holFloatIsSubnormal {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : Bool :=
  decide (x.exponent = 0) && decide (x.significand ≠ 0)

/-- HOL `float_is_zero_def` (`binary_ieeeScript.sml:117-122`): `Float r` with
    `r = 0`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_is_zero_def"
  (words_as_type_indexed_bitvec)
  (reals_as_rational_cuts)]
def holFloatIsZero {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : Bool :=
  match holFloatValue x with
  | .float r => decide (r = 0)
  | _ => false

/-- HOL `float_is_finite_def` (`binary_ieeeScript.sml:124-129`). -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_is_finite_def"
  (words_as_type_indexed_bitvec)
  (reals_as_rational_cuts)]
def holFloatIsFinite {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : Bool :=
  match holFloatValue x with
  | .float _ => true
  | _ => false

/-- HOL `float_negate_def` (`binary_ieeeScript.sml:153-155`):
    `x with Sign := ~x.Sign`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_negate_def"
  (words_as_type_indexed_bitvec)]
def holFloatNegate {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : HolFloat t w :=
  { x with sign := ~~~x.sign }

/-- HOL `float_abs_def` (`binary_ieeeScript.sml:157-159`):
    `x with Sign := 0w`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_abs_def"
  (words_as_type_indexed_bitvec)]
def holFloatAbs {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : HolFloat t w :=
  { x with sign := 0 }

/-- HOL `float_compare = LT | EQ | GT | UN` (`binary_ieeeScript.sml:755`). -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_compare"
  (reals_as_rational_cuts)]
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
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_compare_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
def holFloatCompare {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x y : HolFloat t w) : HolFloatCompare :=
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
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_less_than_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
def holFloatLessThan {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x y : HolFloat t w) : Bool :=
  holFloatCompare x y == .lt

/-- HOL `float_less_equal_def` (`binary_ieeeScript.sml:784-790`): `LT` or
    `EQ`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_less_equal_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
def holFloatLessEqual {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x y : HolFloat t w) : Bool :=
  match holFloatCompare x y with
  | .lt => true
  | .eq => true
  | _ => false

/-- HOL `float_greater_than_def` (`binary_ieeeScript.sml:792-795`):
    `float_compare x y = GT`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_greater_than_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
def holFloatGreaterThan {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x y : HolFloat t w) : Bool :=
  holFloatCompare x y == .gt

/-- HOL `float_greater_equal_def` (`binary_ieeeScript.sml:797-803`): `GT` or
    `EQ`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_greater_equal_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
def holFloatGreaterEqual {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x y : HolFloat t w) : Bool :=
  match holFloatCompare x y with
  | .gt => true
  | .eq => true
  | _ => false

/-- HOL `float_equal_def` (`binary_ieeeScript.sml:805-808`):
    `float_compare x y = EQ`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_equal_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
def holFloatEqual {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x y : HolFloat t w) : Bool :=
  holFloatCompare x y == .eq

end Flapjack
