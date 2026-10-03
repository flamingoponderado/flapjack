import Flapjack.Misc.BinaryIeee

/-!
# HOL `binary_ieee` rounding specification

A rendering of the rounding specification of
`HOL/src/floating-point/binary_ieeeScript.sml:161-540` (bead
`flapjack-h29l.6.2.1`): float constants, `flags`, `rounding`, `is_closest`,
`closest_such`/`closest`, `largest`/`threshold`, `round`, `fp_op`,
`float_some_qnan`, `float_round`, `float_round_with_flags`, and
`check_for_signalling`.  This is the HOL standard library, so nothing here is
tagged.

HOL specifies rounding by Hilbert choice (`@`), and the rendering keeps it
that way: HOL `@a. P a` is `Classical.epsilon P` on the inhabited float type.
Both pick an element satisfying `P` whenever one exists, and are otherwise
unspecified.  The definitions are therefore `noncomputable`.  Two points are
genuinely underspecified in HOL itself, and are left underspecified here:
* `closest_such` is not unique between `+0` and `-0`, so the zero sign of
  `round` is unspecified.  `float_round` fixes it from `toneg`.
* `float_some_qnan` is some quiet NaN with an unspecified bit pattern.

A computable binary64 algorithm, and its kernel-checked agreement with
`float_round roundTiesToEven`, is bead `flapjack-h29l.6.2.3`.

HOL `real` is rendered as `Rat` exactly as in `Flapjack.Misc.BinaryIeee`.
Every operation that reaches `round` in beads `h29l.6.2.x` (`+`, `-`, `*`,
`/` on float values) produces a rational.  HOL `sqrt` is not rational and is
handled separately in bead `h29l.6.3`.
-/

namespace Flapjack

instance {t w : Nat} [NeZero t] [NeZero w] : Inhabited (HolFloat t w) := ⟨{ sign := 0, exponent := 0, significand := 0 }⟩

/-- HOL `abs` on reals, rendered on `Rat`: `abs x = if x < 0 then -x else x`
    (HOL `realTheory.abs`). -/
def holRatAbs (x : Rat) : Rat := if x < 0 then -x else x

/-- HOL `UINT_MAX (:'w) = 2 ^ dimindex (:'w) - 1`. -/
def holUintMax (w : Nat) : Nat := 2 ^ w - 1

/-- HOL `INT_MIN (:'w) = 2 ^ (dimindex (:'w) - 1)`. -/
def holIntMin (w : Nat) : Nat := 2 ^ (w - 1)

/-- HOL `float_plus_infinity_def` (`binary_ieeeScript.sml:165-170`). -/
def holFloatPlusInfinity (t w : Nat) [NeZero t] [NeZero w] : HolFloat t w :=
  { sign := 0, exponent := BitVec.allOnes w, significand := 0 }

/-- HOL `float_plus_zero_def` (`binary_ieeeScript.sml:172-177`). -/
def holFloatPlusZero (t w : Nat) [NeZero t] [NeZero w] : HolFloat t w :=
  { sign := 0, exponent := 0, significand := 0 }

/-- HOL `float_top_def` (`binary_ieeeScript.sml:179-184`):
    `Exponent := UINT_MAXw - 1w; Significand := UINT_MAXw`. -/
def holFloatTop (t w : Nat) [NeZero t] [NeZero w] : HolFloat t w :=
  { sign := 0, exponent := BitVec.allOnes w - 1, significand := BitVec.allOnes t }

/-- HOL `float_plus_min_def` (`binary_ieeeScript.sml:187-192`). -/
def holFloatPlusMin (t w : Nat) [NeZero t] [NeZero w] : HolFloat t w :=
  { sign := 0, exponent := 0, significand := 1 }

/-- HOL `float_minus_infinity_def` (`binary_ieeeScript.sml:194-197`). -/
def holFloatMinusInfinity (t w : Nat) [NeZero t] [NeZero w] : HolFloat t w :=
  holFloatNegate (holFloatPlusInfinity t w)

/-- HOL `float_minus_zero_def` (`binary_ieeeScript.sml:199-201`). -/
def holFloatMinusZero (t w : Nat) [NeZero t] [NeZero w] : HolFloat t w := holFloatNegate (holFloatPlusZero t w)

/-- HOL `float_bottom_def` (`binary_ieeeScript.sml:203-205`). -/
def holFloatBottom (t w : Nat) [NeZero t] [NeZero w] : HolFloat t w := holFloatNegate (holFloatTop t w)

/-- HOL `float_minus_min_def` (`binary_ieeeScript.sml:207-209`). -/
def holFloatMinusMin (t w : Nat) [NeZero t] [NeZero w] : HolFloat t w := holFloatNegate (holFloatPlusMin t w)

/-- HOL `binary_ieee$flags` (`binary_ieeeScript.sml:217-225`), with its fields
    in HOL order. -/
structure HolFloatFlags where
  divideByZero : Bool
  invalidOp : Bool
  overflow : Bool
  precision : Bool
  underflowBeforeRounding : Bool
  underflowAfterRounding : Bool
  deriving DecidableEq, Repr

/-- HOL `clear_flags_def` (`binary_ieeeScript.sml:227-235`). -/
def holClearFlags : HolFloatFlags :=
  { divideByZero := false, invalidOp := false, overflow := false, precision := false,
    underflowBeforeRounding := false, underflowAfterRounding := false }

/-- HOL `invalidop_flags_def` (`binary_ieeeScript.sml:237-239`). -/
def holInvalidopFlags : HolFloatFlags := { holClearFlags with invalidOp := true }

/-- HOL `dividezero_flags_def` (`binary_ieeeScript.sml:241-243`). -/
def holDividezeroFlags : HolFloatFlags := { holClearFlags with divideByZero := true }

/-- HOL `binary_ieee$rounding` (`binary_ieeeScript.sml:245-250`). -/
inductive HolRounding where
  | roundTiesToEven
  | roundTowardPositive
  | roundTowardNegative
  | roundTowardZero
  deriving DecidableEq, Repr

/-- HOL `is_closest_def` (`binary_ieeeScript.sml:253-257`).  `a IN s` and
    every `b IN s` is at least as far from `x`.  HOL sets are rendered as
    predicates. -/
def holIsClosest {t w : Nat} [NeZero t] [NeZero w] (s : HolFloat t w → Prop) (x : Rat) (a : HolFloat t w) : Prop :=
  s a ∧ ∀ b, s b → holRatAbs (holFloatToReal a - x) ≤ holRatAbs (holFloatToReal b - x)

/-- HOL `closest_such_def` (`binary_ieeeScript.sml:347-350`):
    `@a. is_closest s x a ∧ ∀b. is_closest s x b ∧ p b ⇒ p a`. -/
noncomputable def holClosestSuch {t w : Nat} [NeZero t] [NeZero w] (p : HolFloat t w → Prop)
    (s : HolFloat t w → Prop) (x : Rat) : HolFloat t w :=
  Classical.epsilon (fun a => holIsClosest s x a ∧ ∀ b, holIsClosest s x b ∧ p b → p a)

/-- HOL `closest_def` (`binary_ieeeScript.sml:352-353`):
    `closest = closest_such (K T)`. -/
noncomputable def holClosest {t w : Nat} [NeZero t] [NeZero w] (s : HolFloat t w → Prop) (x : Rat) : HolFloat t w :=
  holClosestSuch (fun _ => True) s x

/-- HOL `largest_def` (`binary_ieeeScript.sml:355-359`):
    `(2 pow (UINT_MAX (:'w) - 1) / 2 pow (INT_MAX (:'w))) * (2 - inv (2 pow
    dimindex (:'t)))`. -/
def holFloatLargest (t w : Nat) [NeZero t] [NeZero w] : Rat :=
  (2 ^ (holUintMax w - 1) / 2 ^ holFloatBias w) * (2 - (2 ^ t : Rat)⁻¹)

/-- HOL `threshold_def` (`binary_ieeeScript.sml:361-365`):
    `(2 pow (UINT_MAX (:'w) - 1) / 2 pow (INT_MAX (:'w))) * (2 - inv (2 pow SUC
    (dimindex (:'t))))`. -/
def holFloatThreshold (t w : Nat) [NeZero t] [NeZero w] : Rat :=
  (2 ^ (holUintMax w - 1) / 2 ^ holFloatBias w) * (2 - (2 ^ (t + 1) : Rat)⁻¹)

/-- HOL `round_def` (`binary_ieeeScript.sml:411-443`), for all four modes.
    Each mode first sends values beyond `threshold` (ties-to-even) or
    `largest` (the others) to an infinity or to `top`/`bottom`.  Otherwise it
    takes the closest float of the mode's candidate set; ties-to-even prefers
    an even significand (`¬word_lsb`). -/
noncomputable def holRound {t w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (x : Rat) : HolFloat t w :=
  match mode with
  | .roundTiesToEven =>
      let th := holFloatThreshold t w
      if x ≤ -th then holFloatMinusInfinity t w
      else if x ≥ th then holFloatPlusInfinity t w
      else holClosestSuch (fun a => a.significand.getLsbD 0 = false)
        (fun a => holFloatIsFinite a = true) x
  | .roundTowardZero =>
      let th := holFloatLargest t w
      if x < -th then holFloatBottom t w
      else if x > th then holFloatTop t w
      else holClosest (fun a => holFloatIsFinite a = true ∧ holRatAbs (holFloatToReal a) ≤ holRatAbs x) x
  | .roundTowardPositive =>
      let th := holFloatLargest t w
      if x < -th then holFloatBottom t w
      else if x > th then holFloatPlusInfinity t w
      else holClosest (fun a => holFloatIsFinite a = true ∧ holFloatToReal a ≥ x) x
  | .roundTowardNegative =>
      let th := holFloatLargest t w
      if x < -th then holFloatMinusInfinity t w
      else if x > th then holFloatTop t w
      else holClosest (fun a => holFloatIsFinite a = true ∧ holFloatToReal a ≤ x) x

/-- HOL `binary_ieee$fp_op` (`binary_ieeeScript.sml:481-489`). -/
inductive HolFpOp (t w : Nat) [NeZero t] [NeZero w] where
  | fpSqrt (mode : HolRounding) (x : HolFloat t w)
  | fpAdd (mode : HolRounding) (x y : HolFloat t w)
  | fpSub (mode : HolRounding) (x y : HolFloat t w)
  | fpMul (mode : HolRounding) (x y : HolFloat t w)
  | fpDiv (mode : HolRounding) (x y : HolFloat t w)
  | fpMulAdd (mode : HolRounding) (x y z : HolFloat t w)
  | fpMulSub (mode : HolRounding) (x y z : HolFloat t w)

/-- HOL `float_some_qnan_def` (`binary_ieeeScript.sml:495-499`):
    `(@f. let qnan = f fp_op in float_is_nan qnan ∧ ¬float_is_signalling qnan)
    fp_op`.  Like HOL, this chooses a function and applies it to the
    operation, so the NaN's bit pattern is unspecified. -/
noncomputable def holFloatSomeQnan {t w : Nat} [NeZero t] [NeZero w] (fpOp : HolFpOp t w) : HolFloat t w :=
  (Classical.epsilon (fun f : HolFpOp t w → HolFloat t w =>
    holFloatIsNan (f fpOp) = true ∧ holFloatIsSignalling (f fpOp) = false)) fpOp

/-- HOL `float_round_def` (`binary_ieeeScript.sml:507-515`): round, then
    replace a zero result by `-0` or `+0` according to `toneg`. -/
noncomputable def holFloatRound {t w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (toneg : Bool) (r : Rat) :
    HolFloat t w :=
  let x : HolFloat t w := holRound mode r
  if holFloatIsZero x then
    if toneg then holFloatMinusZero t w else holFloatPlusZero t w
  else x

/-- HOL `float_round_with_flags_def` (`binary_ieeeScript.sml:517-532`).
    * Overflow: `float_is_infinite x ∨ 2 pow INT_MIN (:'w) ≤ abs r`.
    * Underflow before rounding: `inexact ∧ abs r < 2 / 2 pow bias`.
    * Underflow after rounding: `inexact` and the exponent of `r` rounded at
      exponent width `w + 1` is `<=+ n2w (INT_MIN (:'w))`.
    * Precision: `inexact`, where `inexact = (float_value x ≠ Float r)`. -/
noncomputable def holFloatRoundWithFlags {t w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (toNeg : Bool)
    (r : Rat) : HolFloatFlags × HolFloat t w :=
  let x : HolFloat t w := holFloatRound mode toNeg r
  let a := holRatAbs r
  let inexact := decide (holFloatValue x ≠ .float r)
  ({ holClearFlags with
      overflow := holFloatIsInfinite x || decide ((2 : Rat) ^ holIntMin w ≤ a)
      underflowBeforeRounding := inexact && decide (a < 2 / 2 ^ holFloatBias w)
      underflowAfterRounding := inexact &&
        decide ((holFloatRound mode toNeg r : HolFloat t (w + 1)).exponent ≤
          BitVec.ofNat (w + 1) (holIntMin w))
      precision := inexact }, x)

/-- HOL `check_for_signalling_def` (`binary_ieeeScript.sml:534-537`):
    `clear_flags with InvalidOp := EXISTS float_is_signalling l`. -/
def holCheckForSignalling {t w : Nat} [NeZero t] [NeZero w] (l : List (HolFloat t w)) : HolFloatFlags :=
  { holClearFlags with invalidOp := l.any holFloatIsSignalling }

/-- `closest_such` meets HOL's own specification whenever some candidate
    does, which is the defining property of HOL `@`. -/
theorem holClosestSuch_spec {t w : Nat} [NeZero t] [NeZero w] (p : HolFloat t w → Prop) (s : HolFloat t w → Prop)
    (x : Rat) (h : ∃ a, holIsClosest s x a ∧ ∀ b, holIsClosest s x b ∧ p b → p a) :
    holIsClosest s x (holClosestSuch p s x) ∧
      ∀ b, holIsClosest s x b ∧ p b → p (holClosestSuch p s x) :=
  Classical.epsilon_spec h

/-- `float_some_qnan` is a quiet NaN (HOL's `float_some_qnan` specification). -/
theorem holFloatSomeQnan_spec {t w : Nat} [NeZero t] [NeZero w] (fpOp : HolFpOp t w) :
    holFloatIsNan (holFloatSomeQnan fpOp) = true ∧
      holFloatIsSignalling (holFloatSomeQnan fpOp) = false := by
  unfold holFloatSomeQnan
  let q : HolFloat t w :=
    { sign := 0, exponent := BitVec.allOnes w, significand := BitVec.allOnes t }
  have hq : holFloatIsNan q = true ∧ holFloatIsSignalling q = false := by
    have hmsb : q.significand.msb = true := by
      simp [q, BitVec.msb_allOnes (Nat.pos_of_ne_zero (NeZero.ne t))]
    simp [holFloatIsNan, holFloatIsSignalling, holFloatValue, q, hmsb]
  exact Classical.epsilon_spec (p := fun f : HolFpOp t w → HolFloat t w =>
    holFloatIsNan (f fpOp) = true ∧ holFloatIsSignalling (f fpOp) = false) ⟨fun _ => q, hq⟩

end Flapjack
