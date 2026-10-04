import Flapjack.Misc.BinaryIeeeRound
import Flapjack.Misc.MachineIeee

/-!
# HOL `binary_ieee` square root, rendered with rational cuts

HOL `float_sqrt` (`HOL/src/floating-point/binary_ieeeScript.sml:574-585`)
rounds the real number `sqrt r` of a nonnegative float value `r`.  That real
is generally irrational, so the `Rat` rendering of `Flapjack.Misc.BinaryIeee`
cannot express it (bead `flapjack-h29l.6.3.2.1`).  Following the
coordinator-approved design, this module renders the `sqrt`-specialised
`round`, `float_round`, `float_round_with_flags` and `float_sqrt`.  Every real
comparison that HOL makes against `s = sqrt r` (with `r ≥ 0` rational) is
replaced by its exact rational criterion:

* `s ≤ q` is `0 ≤ q ∧ r ≤ q * q` (`holSqrtLe`);
* `s < q` is `0 < q ∧ r < q * q` (`holSqrtLt`);
* `q ≤ s` is `q ≤ 0 ∨ q * q ≤ r` (`holSqrtGe`);
* `q < s` is `q < 0 ∨ q * q < r` (`holSqrtGt`);
* `q = s` is `0 ≤ q ∧ q * q = r` (`holSqrtEq`);
* `abs (A - s) ≤ abs (B - s)` is `A = B`, or `A < B ∧ s ≤ (A + B) / 2`, or
  `B < A ∧ (A + B) / 2 ≤ s` (`holSqrtDistLe`);
* `abs s = s`.

These are standard facts about the real square root.  They are proved against
Mathlib `ℝ` in `Flapjack.Misc.BinaryIeeeSqrt.RealAgreement`, and
`Flapjack.Misc.BinaryIeeeSqrt.RealCarrier` proves `holFloatSqrt` equal to the
tagged real-carrier `float_sqrt` port `holFloatSqrtR`
(`holFloatSqrt_eq_holFloatSqrtR`).  Agreement of that real carrier with HOL's
reals remains the external assumption of `docs/SOUNDNESS.md` item 8.  The
rendering is not an exact `@[hol]` port.  Everything else follows HOL clause
for clause: the Hilbert choice (as `Classical.epsilon`), the tie-to-even
preference, the flags, and the NaN, `-0` and negative cases.  A computable
binary64 algorithm with a kernel conformance proof against this specification
is bead `flapjack-h29l.6.3.2.2`.  These declarations are untagged because
the rational-cut rendering changes HOL's real-number domain, not because
their originals are in the HOL standard library rather than CakeML.
-/

namespace Flapjack

/-- `sqrt r ≤ q` for `r ≥ 0`. -/
def holSqrtLe (r q : Rat) : Prop := 0 ≤ q ∧ r ≤ q * q

/-- `sqrt r < q` for `r ≥ 0`. -/
def holSqrtLt (r q : Rat) : Prop := 0 < q ∧ r < q * q

/-- `q ≤ sqrt r` for `r ≥ 0`. -/
def holSqrtGe (r q : Rat) : Prop := q ≤ 0 ∨ q * q ≤ r

/-- `q < sqrt r` for `r ≥ 0`. -/
def holSqrtGt (r q : Rat) : Prop := q < 0 ∨ q * q < r

/-- `q = sqrt r` for `r ≥ 0`. -/
def holSqrtEq (r q : Rat) : Prop := 0 ≤ q ∧ q * q = r

/-- `abs (A - sqrt r) ≤ abs (B - sqrt r)` for `r ≥ 0`: equal points, or
    `sqrt r` lies on `A`'s side of the midpoint. -/
def holSqrtDistLe (r A B : Rat) : Prop :=
  A = B ∨ (A < B ∧ holSqrtLe r ((A + B) / 2)) ∨ (B < A ∧ holSqrtGe r ((A + B) / 2))

instance (r q : Rat) : Decidable (holSqrtLe r q) := by unfold holSqrtLe; infer_instance
instance (r q : Rat) : Decidable (holSqrtLt r q) := by unfold holSqrtLt; infer_instance
instance (r q : Rat) : Decidable (holSqrtGe r q) := by unfold holSqrtGe; infer_instance
instance (r q : Rat) : Decidable (holSqrtGt r q) := by unfold holSqrtGt; infer_instance
instance (r q : Rat) : Decidable (holSqrtEq r q) := by unfold holSqrtEq; infer_instance
instance (r A B : Rat) : Decidable (holSqrtDistLe r A B) := by
  unfold holSqrtDistLe; infer_instance

/-- HOL `is_closest s (sqrt r) a` (`binary_ieeeScript.sml:253-257`) with the
    distance comparison rendered by `holSqrtDistLe`. -/
def holIsClosestSqrt {t : Nat} {w : Nat} [NeZero t] [NeZero w] (s : HolFloat t w → Prop) (r : Rat) (a : HolFloat t w) : Prop :=
  s a ∧ ∀ b, s b → holSqrtDistLe r (holFloatToReal a) (holFloatToReal b)

/-- HOL `closest_such p s (sqrt r)` (`binary_ieeeScript.sml:347-350`). -/
noncomputable def holClosestSuchSqrt {t : Nat} {w : Nat} [NeZero t] [NeZero w] (p : HolFloat t w → Prop)
    (s : HolFloat t w → Prop) (r : Rat) : HolFloat t w :=
  Classical.epsilon (fun a => holIsClosestSqrt s r a ∧ ∀ b, holIsClosestSqrt s r b ∧ p b → p a)

/-- HOL `closest s (sqrt r) = closest_such (K T) s (sqrt r)`. -/
noncomputable def holClosestSqrt {t : Nat} {w : Nat} [NeZero t] [NeZero w] (s : HolFloat t w → Prop) (r : Rat) : HolFloat t w :=
  holClosestSuchSqrt (fun _ => True) s r

/-- HOL `round mode (sqrt r)` (`binary_ieeeScript.sml:411-443`), for all four
    modes.  The threshold tests and candidate sets compare float values with
    `sqrt r` through the rational criteria. -/
noncomputable def holRoundSqrt {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (r : Rat) : HolFloat t w :=
  match mode with
  | .roundTiesToEven =>
      let th := holFloatThreshold t w
      if holSqrtLe r (-th) then holFloatMinusInfinity t w
      else if holSqrtGe r th then holFloatPlusInfinity t w
      else holClosestSuchSqrt (fun a => a.significand.getLsbD 0 = false)
        (fun a => holFloatIsFinite a = true) r
  | .roundTowardZero =>
      let th := holFloatLargest t w
      if holSqrtLt r (-th) then holFloatBottom t w
      else if holSqrtGt r th then holFloatTop t w
      else holClosestSqrt
        (fun a => holFloatIsFinite a = true ∧ holSqrtGe r (holRatAbs (holFloatToReal a))) r
  | .roundTowardPositive =>
      let th := holFloatLargest t w
      if holSqrtLt r (-th) then holFloatBottom t w
      else if holSqrtGt r th then holFloatPlusInfinity t w
      else holClosestSqrt (fun a => holFloatIsFinite a = true ∧ holSqrtLe r (holFloatToReal a)) r
  | .roundTowardNegative =>
      let th := holFloatLargest t w
      if holSqrtLt r (-th) then holFloatMinusInfinity t w
      else if holSqrtGt r th then holFloatTop t w
      else holClosestSqrt (fun a => holFloatIsFinite a = true ∧ holSqrtGe r (holFloatToReal a)) r

/-- HOL `float_round mode toneg (sqrt r)` (`binary_ieeeScript.sml:507-515`). -/
noncomputable def holFloatRoundSqrt {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (toneg : Bool) (r : Rat) :
    HolFloat t w :=
  let x : HolFloat t w := holRoundSqrt mode r
  if holFloatIsZero x then
    if toneg then holFloatMinusZero t w else holFloatPlusZero t w
  else x

/-- HOL `float_round_with_flags mode toNeg (sqrt r)`
    (`binary_ieeeScript.sml:517-532`), with `abs (sqrt r) = sqrt r`.
    * `inexact` means the rounded value is not `Float (sqrt r)`.
    * Overflow: `2 pow INT_MIN (:'w) ≤ sqrt r`.
    * Underflow before rounding: `sqrt r < 2 / 2 pow bias`. -/
noncomputable def holFloatRoundWithFlagsSqrt {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (toNeg : Bool)
    (r : Rat) : HolFloatFlags × HolFloat t w :=
  let x : HolFloat t w := holFloatRoundSqrt mode toNeg r
  let inexact : Bool :=
    match holFloatValue x with
    | .float q => !decide (holSqrtEq r q)
    | _ => true
  ({ holClearFlags with
      overflow := holFloatIsInfinite x || decide (holSqrtGe r ((2 : Rat) ^ holIntMin w))
      underflowBeforeRounding := inexact && decide (holSqrtLt r (2 / 2 ^ holFloatBias w))
      underflowAfterRounding := inexact &&
        decide ((holFloatRoundSqrt mode toNeg r : HolFloat t (w + 1)).exponent ≤
          BitVec.ofNat (w + 1) (holIntMin w))
      precision := inexact }, x)

/-- HOL `float_sqrt_def` (`binary_ieeeScript.sml:574-585`).
    * Positive sign: a NaN gives `float_some_qnan` with
      `check_for_signalling`, an infinity gives `+inf`, and `Float r` rounds
      `sqrt r` with zero sign `F`.
    * Negative sign: `-0` gives `-0`, and anything else is invalid. -/
noncomputable def holFloatSqrt {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (x : HolFloat t w) :
    HolFloatFlags × HolFloat t w :=
  if x.sign = 0 then
    match holFloatValue x with
    | .nan => (holCheckForSignalling [x], holFloatSomeQnan (.fpSqrt mode x))
    | .infinity => (holClearFlags, holFloatPlusInfinity t w)
    | .float r => holFloatRoundWithFlagsSqrt mode false r
  else if x = holFloatMinusZero t w then (holClearFlags, holFloatMinusZero t w)
  else (holInvalidopFlags, holFloatSomeQnan (.fpSqrt mode x))

/-- HOL `fp64_sqrt mode = float_to_fp64 o SND o float_sqrt mode o fp64_to_float`
    (`machine_ieeeLib` `lift1` with flags). -/
noncomputable def holFp64Sqrt (mode : HolRounding) (a : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatSqrt mode (holFp64ToFloat a)).2

end Flapjack
