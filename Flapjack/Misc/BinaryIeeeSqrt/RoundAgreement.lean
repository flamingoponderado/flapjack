import Flapjack.Misc.BinaryIeeeSqrt
import Flapjack.Misc.BinaryIeeeSqrt.RealAgreement

/-!
# Real-square-root rounding agrees with the rational-cut rendering

`Flapjack.Misc.BinaryIeeeSqrt` renders HOL `float_sqrt` with exact rational
comparisons against `sqrt r` (the predicates `holSqrtLe/Lt/Ge/Gt/Eq/DistLe`).
`Flapjack.Misc.BinaryIeeeSqrt.RealAgreement` already proves each of those
predicates equivalent, for `r ≥ 0`, to the corresponding comparison against
`realSqrtOfRat r = Real.sqrt (r : ℝ)`.

This module defines the real-distance counterparts of the `roundTiesToEven`
rounder (`holIsClosestSqrtReal`, `holClosestSuchSqrtReal`,
`holRoundSqrtRealTiesToEven`, `holFloatRoundSqrtReal`,
`holFloatRoundWithFlagsSqrtReal`, `holFloatSqrtReal`) and proves that they are
extensionally equal to the cut renderings, by lifting the six pointwise iff
lemmas through the `Classical.epsilon` choices and the `decide`d flag tests.
The final corollary `holFp64Sqrt_tiesToEven_agreement` transfers this to
`holFp64Sqrt .roundTiesToEven`.

These declarations are Flapjack-specific infrastructure. They are not an exact
`@[hol]` port: the real-sqrt rounder is a Lean-side reference rendering, and
the cut renderer stays the definition used by the compiler. The remaining
external assumption (agreement with HOL `real`) is recorded in
`docs/SOUNDNESS.md`.
-/

namespace Flapjack

/-- `abs (a - sqrt r) ≤ abs (b - sqrt r)` in `ℝ`, the real reading of
    `holSqrtDistLe`. -/
def realSqrtDistLe (r a b : Rat) : Prop :=
  |(a : ℝ) - realSqrtOfRat r| ≤ |(b : ℝ) - realSqrtOfRat r|

/-- HOL `is_closest s (sqrt r) a` with distances measured against the real
    `realSqrtOfRat r` instead of the rational cut `holSqrtDistLe`. -/
def holIsClosestSqrtReal {t w : Nat} (s : HolFloat t w → Prop) (r : Rat)
    (a : HolFloat t w) : Prop :=
  s a ∧ ∀ b, s b → realSqrtDistLe r (holFloatToReal a) (holFloatToReal b)

/-- HOL `closest_such p s (sqrt r)` with real distances. -/
noncomputable def holClosestSuchSqrtReal {t w : Nat} (p : HolFloat t w → Prop)
    (s : HolFloat t w → Prop) (r : Rat) : HolFloat t w :=
  Classical.epsilon
    (fun a => holIsClosestSqrtReal s r a ∧ ∀ b, holIsClosestSqrtReal s r b ∧ p b → p a)

/-- HOL `closest s (sqrt r)` with real distances. -/
noncomputable def holClosestSqrtReal {t w : Nat} (s : HolFloat t w → Prop) (r : Rat) :
    HolFloat t w :=
  holClosestSuchSqrtReal (fun _ => True) s r

/-- HOL `round roundTiesToEven (sqrt r)`, real-distance rendering.  Only the
    mode used by `fp64_sqrt` (`roundTiesToEven`) is given a real counterpart. -/
noncomputable def holRoundSqrtRealTiesToEven {t w : Nat} (r : Rat) : HolFloat t w :=
  let th := holFloatThreshold t w
  if realSqrtOfRat r ≤ ((-th : Rat) : ℝ) then holFloatMinusInfinity t w
  else if ((th : Rat) : ℝ) ≤ realSqrtOfRat r then holFloatPlusInfinity t w
  else holClosestSuchSqrtReal (fun a => a.significand.getLsbD 0 = false)
        (fun a => holFloatIsFinite a = true) r

/-- HOL `float_round roundTiesToEven toneg (sqrt r)`, real-distance
    rendering. -/
noncomputable def holFloatRoundSqrtReal {t w : Nat} (toneg : Bool) (r : Rat) : HolFloat t w :=
  let x : HolFloat t w := holRoundSqrtRealTiesToEven r
  if holFloatIsZero x then
    if toneg then holFloatMinusZero t w else holFloatPlusZero t w
  else x

/-- HOL `float_round_with_flags roundTiesToEven toNeg (sqrt r)`, real-distance
    rendering. -/
noncomputable def holFloatRoundWithFlagsSqrtReal {t w : Nat} (toNeg : Bool) (r : Rat) :
    HolFloatFlags × HolFloat t w :=
  let x : HolFloat t w := holFloatRoundSqrtReal toNeg r
  let inexact : Bool :=
    match holFloatValue x with
    | .float q => !decide ((q : ℝ) = realSqrtOfRat r)
    | _ => true
  ({ holClearFlags with
      overflow := holFloatIsInfinite x ||
        decide (((((2 : Rat) ^ holIntMin w) : Rat) : ℝ) ≤ realSqrtOfRat r)
      underflowBeforeRounding := inexact &&
        decide (realSqrtOfRat r < ((2 / 2 ^ holFloatBias w : Rat) : ℝ))
      underflowAfterRounding := inexact &&
        decide ((holFloatRoundSqrtReal toNeg r : HolFloat t (w + 1)).exponent ≤
          BitVec.ofNat (w + 1) (holIntMin w))
      precision := inexact }, x)

/-- HOL `float_sqrt roundTiesToEven`, real-distance rendering. -/
noncomputable def holFloatSqrtReal {t w : Nat} (x : HolFloat t w) :
    HolFloatFlags × HolFloat t w :=
  if x.sign = 0 then
    match holFloatValue x with
    | .nan => (holCheckForSignalling [x], holFloatSomeQnan (.fpSqrt .roundTiesToEven x))
    | .infinity => (holClearFlags, holFloatPlusInfinity t w)
    | .float r => holFloatRoundWithFlagsSqrtReal false r
  else if x = holFloatMinusZero t w then (holClearFlags, holFloatMinusZero t w)
  else (holInvalidopFlags, holFloatSomeQnan (.fpSqrt .roundTiesToEven x))

/-- The real and cut closeness predicates are pointwise equivalent for
    `r ≥ 0`, by `holSqrtDistLe_real_iff`. -/
theorem holIsClosestSqrt_real_iff {t w : Nat} (s : HolFloat t w → Prop) {r : Rat}
    (hr : 0 ≤ r) (a : HolFloat t w) :
    holIsClosestSqrt s r a ↔ holIsClosestSqrtReal s r a := by
  unfold holIsClosestSqrt holIsClosestSqrtReal realSqrtDistLe
  constructor
  · rintro ⟨ha, h⟩
    exact ⟨ha, fun b hb => (holSqrtDistLe_real_iff hr).mp (h b hb)⟩
  · rintro ⟨ha, h⟩
    exact ⟨ha, fun b hb => (holSqrtDistLe_real_iff hr).mpr (h b hb)⟩

/-- The `Classical.epsilon` choices of the cut and real `closest_such`
    coincide, because their predicates are pointwise equivalent. -/
theorem holClosestSuchSqrt_real_eq {t w : Nat} (p s : HolFloat t w → Prop) {r : Rat}
    (hr : 0 ≤ r) :
    holClosestSuchSqrt p s r = holClosestSuchSqrtReal p s r := by
  unfold holClosestSuchSqrt holClosestSuchSqrtReal
  congr 1
  funext a
  exact propext (by
    constructor
    · rintro ⟨ha, hp⟩
      exact ⟨(holIsClosestSqrt_real_iff s hr a).mp ha,
        fun b hb => hp b ⟨(holIsClosestSqrt_real_iff s hr b).mpr hb.1, hb.2⟩⟩
    · rintro ⟨ha, hp⟩
      exact ⟨(holIsClosestSqrt_real_iff s hr a).mpr ha,
        fun b hb => hp b ⟨(holIsClosestSqrt_real_iff s hr b).mp hb.1, hb.2⟩⟩)

/-- Pointwise equality of the cut and real `closest` (the `K T` instance). -/
theorem holClosestSqrt_real_eq {t w : Nat} (s : HolFloat t w → Prop) {r : Rat}
    (hr : 0 ≤ r) :
    holClosestSqrt s r = holClosestSqrtReal s r :=
  holClosestSuchSqrt_real_eq (fun _ => True) s hr

/-- `round roundTiesToEven (sqrt r)` agrees between the cut and real
    renderings for `r ≥ 0`. -/
theorem holRoundSqrt_tiesToEven_eq_real {t w : Nat} {r : Rat} (hr : 0 ≤ r) :
    (holRoundSqrt .roundTiesToEven r : HolFloat t w) =
      (holRoundSqrtRealTiesToEven r : HolFloat t w) := by
  unfold holRoundSqrt holRoundSqrtRealTiesToEven
  by_cases h1 : holSqrtLe r (-(holFloatThreshold t w))
  · have h1' : realSqrtOfRat r ≤ ((-(holFloatThreshold t w) : Rat) : ℝ) :=
      (holSqrtLe_real_iff).mp h1
    rw [if_pos h1, if_pos h1']
  · have h1' : ¬ realSqrtOfRat r ≤ ((-(holFloatThreshold t w) : Rat) : ℝ) :=
      fun hh => h1 ((holSqrtLe_real_iff).mpr hh)
    rw [if_neg h1, if_neg h1']
    by_cases h2 : holSqrtGe r (holFloatThreshold t w)
    · have h2' : ((holFloatThreshold t w : Rat) : ℝ) ≤ realSqrtOfRat r :=
        (holSqrtGe_real_iff hr).mp h2
      rw [if_pos h2, if_pos h2']
    · have h2' : ¬ ((holFloatThreshold t w : Rat) : ℝ) ≤ realSqrtOfRat r :=
        fun hh => h2 ((holSqrtGe_real_iff hr).mpr hh)
      rw [if_neg h2, if_neg h2']
      exact holClosestSuchSqrt_real_eq _ _ hr

/-- `float_round roundTiesToEven toneg (sqrt r)` agrees between the cut and
    real renderings for `r ≥ 0`. -/
theorem holFloatRoundSqrt_tiesToEven_eq_real {t w : Nat} (toneg : Bool) {r : Rat}
    (hr : 0 ≤ r) :
    (holFloatRoundSqrt .roundTiesToEven toneg r : HolFloat t w) =
      (holFloatRoundSqrtReal toneg r : HolFloat t w) := by
  unfold holFloatRoundSqrt holFloatRoundSqrtReal
  rw [holRoundSqrt_tiesToEven_eq_real hr]

/-- `float_round_with_flags roundTiesToEven toNeg (sqrt r)` agrees between the
    cut and real renderings for `r ≥ 0`. -/
theorem holFloatRoundWithFlagsSqrt_tiesToEven_agreement {t w : Nat} (toNeg : Bool) {r : Rat}
    (hr : 0 ≤ r) :
    (holFloatRoundWithFlagsSqrt .roundTiesToEven toNeg r : HolFloatFlags × HolFloat t w) =
      (holFloatRoundWithFlagsSqrtReal toNeg r : HolFloatFlags × HolFloat t w) := by
  unfold holFloatRoundWithFlagsSqrt holFloatRoundWithFlagsSqrtReal
  simp only [holFloatRoundSqrt_tiesToEven_eq_real toNeg hr, holSqrtEq_real_iff hr,
    holSqrtGe_real_iff hr, holSqrtLt_real_iff hr]
  apply Prod.ext
  · congr 1
  · rfl

/-- A positive-sign float has a nonnegative real value. -/
theorem holFloatToReal_nonneg_of_sign_zero {t w : Nat} {x : HolFloat t w}
    (hs : x.sign = 0) : 0 ≤ holFloatToReal x := by
  unfold holFloatToReal
  rw [hs]
  have h0 : (0 : BitVec 1).toNat = 0 := rfl
  rw [h0]
  simp only [pow_zero, one_mul]
  split <;> positivity

/-- `float_sqrt roundTiesToEven` agrees between the cut and real renderings. -/
theorem holFloatSqrt_tiesToEven_agreement {t w : Nat} (x : HolFloat t w) :
    holFloatSqrt .roundTiesToEven x = holFloatSqrtReal x := by
  unfold holFloatSqrt holFloatSqrtReal
  by_cases hs : x.sign = 0
  · rw [if_pos hs, if_pos hs]
    cases hv : holFloatValue x with
    | nan => rfl
    | infinity => rfl
    | float r =>
      have hxr : holFloatToReal x = r := by
        unfold holFloatValue at hv
        split at hv
        · split at hv <;> simp at hv
        · simpa using hv
      exact holFloatRoundWithFlagsSqrt_tiesToEven_agreement false (hxr ▸ holFloatToReal_nonneg_of_sign_zero hs)
  · rw [if_neg hs, if_neg hs]

/-- Real-distance rendering of HOL `fp64_sqrt roundTiesToEven`. -/
noncomputable def holFp64SqrtReal (a : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatSqrtReal (holFp64ToFloat a)).2

/-- `fp64_sqrt roundTiesToEven` agrees between the cut and real renderings. -/
theorem holFp64Sqrt_tiesToEven_agreement (a : BitVec 64) :
    holFp64Sqrt .roundTiesToEven a = holFp64SqrtReal a := by
  unfold holFp64Sqrt holFp64SqrtReal
  rw [holFloatSqrt_tiesToEven_agreement]

end Flapjack
