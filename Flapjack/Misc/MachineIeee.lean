import Flapjack.Misc.BinaryIeee

/-!
# HOL `machine_ieee` binary64 encoding and exact lifted operations

A rendering of the `fp64` encoding that `machine_ieeeLib.mk_fp_encoding`
generates in `HOL/src/floating-point/machine_ieeeScript.sml` (bead
`flapjack-h29l.6.1`).  For binary64 the significand width is `t = 52` and the
exponent width `w = 11`.  `fp64_to_float` extracts the sign (bit 63), exponent
(bits 62-52) and significand (bits 51-0).  `float_to_fp64` concatenates them
back.  The comparison and sign operations are the `binary_ieee` ones composed
with these encodings.  This is the HOL standard library, so nothing here is
tagged.
-/

namespace Flapjack

/-- HOL `fp64_to_float w = <| Sign := (63 >< 63) w; Exponent := (62 >< 52) w;
    Significand := (51 >< 0) w |>`. -/
def holFp64ToFloat (w : BitVec 64) : HolFloat 52 11 :=
  { sign := w.extractLsb' 63 1, exponent := w.extractLsb' 52 11,
    significand := w.extractLsb' 0 52 }

/-- HOL `float_to_fp64 x = x.Sign @@ x.Exponent @@ x.Significand`; the
    concatenation is exactly 64 bits wide. -/
def holFloatToFp64 (x : HolFloat 52 11) : BitVec 64 :=
  (x.sign ++ x.exponent ++ x.significand).cast (by decide)

/-- HOL `fp64_lessThan a b = float_less_than (fp64_to_float a) (fp64_to_float b)`. -/
def holFp64LessThan (a b : BitVec 64) : Bool :=
  holFloatLessThan (holFp64ToFloat a) (holFp64ToFloat b)

/-- HOL `fp64_lessEqual a b = float_less_equal (fp64_to_float a) (fp64_to_float b)`. -/
def holFp64LessEqual (a b : BitVec 64) : Bool :=
  holFloatLessEqual (holFp64ToFloat a) (holFp64ToFloat b)

/-- HOL `fp64_greaterThan a b = float_greater_than (fp64_to_float a)
    (fp64_to_float b)`. -/
def holFp64GreaterThan (a b : BitVec 64) : Bool :=
  holFloatGreaterThan (holFp64ToFloat a) (holFp64ToFloat b)

/-- HOL `fp64_greaterEqual a b = float_greater_equal (fp64_to_float a)
    (fp64_to_float b)`. -/
def holFp64GreaterEqual (a b : BitVec 64) : Bool :=
  holFloatGreaterEqual (holFp64ToFloat a) (holFp64ToFloat b)

/-- HOL `fp64_equal a b = float_equal (fp64_to_float a) (fp64_to_float b)`. -/
def holFp64Equal (a b : BitVec 64) : Bool :=
  holFloatEqual (holFp64ToFloat a) (holFp64ToFloat b)

/-- HOL `fp64_abs = float_to_fp64 o float_abs o fp64_to_float`. -/
def holFp64Abs (a : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatAbs (holFp64ToFloat a))

/-- HOL `fp64_negate = float_to_fp64 o float_negate o fp64_to_float`. -/
def holFp64Negate (a : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatNegate (holFp64ToFloat a))

end Flapjack
