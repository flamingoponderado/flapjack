import Flapjack.Misc.BinaryIeeeRoundFp64
import Flapjack.Misc.MachineIeee

/-!
# HOL `binary_ieee` integer conversions and their binary64 lifts

A rendering of `float_to_int` and of `real_to_float` restricted to rational
inputs (`HOL/src/floating-point/binary_ieeeScript.sml:539-572`), with the
`fp64_to_int`, `real_to_fp64` and `int_to_fp64` encodings that
`machine_ieeeLib` generates (bead `flapjack-h29l.6.3.1`).  These are used by
wordSem `inst_def`'s `FPToInt` and `FPFromInt` cases.  HOL `INT_FLOOR` and
`INT_CEILING` are `Rat.floor` and `Rat.ceil`, and `Num (ABS f)` is
`Int.natAbs`.  `float_to_int` is tagged; the `Rat`-input `real_to_float`
rendering is not (see `holRealToFloat`), and the generated `machine_ieeeLib`
wrappers stay untagged here.
-/

namespace Flapjack

/-- HOL `float_to_int_def` (`binary_ieeeScript.sml:555-572`).  A finite float
    `Float r` is converted by the mode:
    * roundTiesToEven: `f = INT_FLOOR r` when `abs (r - f) < 1/2`, or when it
      equals `1/2` and `Num (ABS f)` is even, and `INT_CEILING r` otherwise;
    * roundTowardPositive: the ceiling; roundTowardNegative: the floor;
    * roundTowardZero: the ceiling for a negative sign, else the floor.
    Infinities and NaNs give `NONE`.  The real `r` is a float value, a
    rational, so `INT_FLOOR`/`INT_CEILING` on it are `Rat.floor`/`Rat.ceil`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_to_int_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
def holFloatToInt {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (x : HolFloat t w) : Option Int :=
  match holFloatValue x with
  | .float r =>
      some (match mode with
        | .roundTiesToEven =>
            let f := r.floor
            let df := holRatAbs (r - (f : Rat))
            if df < 1 / 2 ∨ (df = 1 / 2 ∧ f.natAbs % 2 = 0) then f else r.ceil
        | .roundTowardPositive => r.ceil
        | .roundTowardNegative => r.floor
        | .roundTowardZero => if x.sign = 1 then r.ceil else r.floor)
  | _ => none

/-- HOL `real_to_float_def` (`binary_ieeeScript.sml:539-541`):
    `real_to_float m = float_round m (m = roundTowardNegative)`, restricted to
    rational inputs.  HOL's `real_to_float` accepts an arbitrary real; the
    tagged general-real port is `holRealToFloatR`
    (`Flapjack.Misc.BinaryIeeeSqrt.RealCarrier`).  This `Rat` restriction is
    not an exact port; its only use here is `int_to_fp64`, whose argument
    `real_of_int a` is an integer and so lies in the covered domain. -/
noncomputable def holRealToFloat {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (r : Rat) : HolFloat t w :=
  holFloatRound mode (decide (mode = .roundTowardNegative)) r

/-- HOL `fp64_to_int mode = float_to_int mode o fp64_to_float`. -/
def holFp64ToInt (mode : HolRounding) (a : BitVec 64) : Option Int :=
  holFloatToInt mode (holFp64ToFloat a)

/-- HOL `real_to_fp64 mode = float_to_fp64 o real_to_float mode`, restricted
    to rational inputs like `holRealToFloat`. -/
noncomputable def holRealToFp64 (mode : HolRounding) (r : Rat) : BitVec 64 :=
  holFloatToFp64 (holRealToFloat mode r)

/-- HOL `int_to_fp64 mode a = real_to_fp64 mode (real_of_int a)`. -/
noncomputable def holIntToFp64 (mode : HolRounding) (a : Int) : BitVec 64 :=
  holRealToFp64 mode (a : Rat)

/-- `int_to_fp64 roundTiesToEven` through the computable rounding. -/
theorem holIntToFp64_rte (a : Int) :
    holIntToFp64 .roundTiesToEven a = holFloatToFp64 (holFp64RoundTiesToEven false (a : Rat)) := by
  unfold holIntToFp64 holRealToFp64 holRealToFloat
  rw [holFloatRound_rte_fp64]
  rfl

end Flapjack
