import Flapjack.Misc.BinaryIeeeSqrt
import Flapjack.Misc.BinaryIeeeSqrt.RealAgreement

/-!
# Real-square-root rounding agrees with the rational-cut rendering

`Flapjack.Misc.BinaryIeeeSqrt` renders HOL `float_sqrt` with exact rational
comparisons against `sqrt r` (the predicates `holSqrtLe/Lt/Ge/Gt/Eq/DistLe`).
`Flapjack.Misc.BinaryIeeeSqrt.RealAgreement` already proves each of those
predicates equivalent, for `r ≥ 0`, to the corresponding comparison against
`realSqrtOfRat r = Real.sqrt (r : ℝ)`.

This module defines the real-distance counterparts of every `HolRounding` mode
(`holRoundSqrtReal`, `holFloatRoundSqrtReal`, `holFloatRoundWithFlagsSqrtReal`,
`holFloatSqrtReal`, `holFp64SqrtReal`) and proves that they are extensionally
equal to the cut renderings, by lifting the six pointwise iff lemmas through
the `Classical.epsilon` choices and the `decide`d flag tests.  The real
renderer mirrors `holRound`: the same threshold (`roundTiesToEven`) or
`largest` (the other three modes) tests, the same infinities / `top` / `bottom`
targets, and the same mode-specific candidate set, only with each comparison
against `sqrt r` read as a comparison against `realSqrtOfRat r`.  The single
general theorem `holRoundSqrt_eq_real` (and its `float_round`,
`float_round_with_flags`, `float_sqrt`, `fp64_sqrt` lifts) covers all four
constructors; the earlier `*_tiesToEven_*` theorems are kept as corollaries so
existing consumers keep compiling.  `holRoundSqrtRealTiesToEven` is kept as an
abbreviation for the `roundTiesToEven` specialization.

These declarations are Flapjack-specific infrastructure. They are not an exact
`@[hol]` port: the real-sqrt rounder is a Lean-side reference rendering, and
the cut renderer stays the definition used by the compiler. The theorems here
are purely Lean-side: they relate the cut rendering to the real rendering
built on Mathlib's `Real.sqrt`. No HOL-to-Lean equivalence is claimed or
assumed; the Lean statements and definitions above should be reviewed on their
own terms (a separate review covers the full `fpSem` target).
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

/-- HOL `round mode (sqrt r)`, real-distance rendering, for all four modes.
    The threshold or `largest` test and the mode's candidate set compare float
    values with the real `realSqrtOfRat r` instead of the rational cuts of
    `holRoundSqrt`. -/
noncomputable def holRoundSqrtReal {t w : Nat} (mode : HolRounding) (r : Rat) : HolFloat t w :=
  match mode with
  | .roundTiesToEven =>
      let th := holFloatThreshold t w
      if realSqrtOfRat r ≤ ((-th : Rat) : ℝ) then holFloatMinusInfinity t w
      else if ((th : Rat) : ℝ) ≤ realSqrtOfRat r then holFloatPlusInfinity t w
      else holClosestSuchSqrtReal (fun a => a.significand.getLsbD 0 = false)
            (fun a => holFloatIsFinite a = true) r
  | .roundTowardZero =>
      let th := holFloatLargest t w
      if realSqrtOfRat r < ((-th : Rat) : ℝ) then holFloatBottom t w
      else if ((th : Rat) : ℝ) < realSqrtOfRat r then holFloatTop t w
      else holClosestSqrtReal
            (fun a => holFloatIsFinite a = true ∧
              ((holRatAbs (holFloatToReal a) : Rat) : ℝ) ≤ realSqrtOfRat r) r
  | .roundTowardPositive =>
      let th := holFloatLargest t w
      if realSqrtOfRat r < ((-th : Rat) : ℝ) then holFloatBottom t w
      else if ((th : Rat) : ℝ) < realSqrtOfRat r then holFloatPlusInfinity t w
      else holClosestSqrtReal
            (fun a => holFloatIsFinite a = true ∧
              realSqrtOfRat r ≤ ((holFloatToReal a : Rat) : ℝ)) r
  | .roundTowardNegative =>
      let th := holFloatLargest t w
      if realSqrtOfRat r < ((-th : Rat) : ℝ) then holFloatMinusInfinity t w
      else if ((th : Rat) : ℝ) < realSqrtOfRat r then holFloatTop t w
      else holClosestSqrtReal
            (fun a => holFloatIsFinite a = true ∧
              ((holFloatToReal a : Rat) : ℝ) ≤ realSqrtOfRat r) r

/-- `round roundTiesToEven (sqrt r)`, real-distance rendering, kept as the
    `roundTiesToEven` specialization of `holRoundSqrtReal`. -/
noncomputable def holRoundSqrtRealTiesToEven {t w : Nat} (r : Rat) : HolFloat t w :=
  holRoundSqrtReal .roundTiesToEven r

/-- HOL `float_round mode toneg (sqrt r)`, real-distance rendering. -/
noncomputable def holFloatRoundSqrtReal {t w : Nat} (mode : HolRounding) (toneg : Bool)
    (r : Rat) : HolFloat t w :=
  let x : HolFloat t w := holRoundSqrtReal mode r
  if holFloatIsZero x then
    if toneg then holFloatMinusZero t w else holFloatPlusZero t w
  else x

/-- HOL `float_round_with_flags mode toNeg (sqrt r)`, real-distance
    rendering. -/
noncomputable def holFloatRoundWithFlagsSqrtReal {t w : Nat} (mode : HolRounding)
    (toNeg : Bool) (r : Rat) : HolFloatFlags × HolFloat t w :=
  let x : HolFloat t w := holFloatRoundSqrtReal mode toNeg r
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
        decide ((holFloatRoundSqrtReal mode toNeg r : HolFloat t (w + 1)).exponent ≤
          BitVec.ofNat (w + 1) (holIntMin w))
      precision := inexact }, x)

/-- HOL `float_sqrt mode`, real-distance rendering. -/
noncomputable def holFloatSqrtReal {t w : Nat} (mode : HolRounding) (x : HolFloat t w) :
    HolFloatFlags × HolFloat t w :=
  if x.sign = 0 then
    match holFloatValue x with
    | .nan => (holCheckForSignalling [x], holFloatSomeQnan (.fpSqrt mode x))
    | .infinity => (holClearFlags, holFloatPlusInfinity t w)
    | .float r => holFloatRoundWithFlagsSqrtReal mode false r
  else if x = holFloatMinusZero t w then (holClearFlags, holFloatMinusZero t w)
  else (holInvalidopFlags, holFloatSomeQnan (.fpSqrt mode x))

/-- Real-distance rendering of HOL `fp64_sqrt mode`. -/
noncomputable def holFp64SqrtReal (mode : HolRounding) (a : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatSqrtReal mode (holFp64ToFloat a)).2

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

/-- Congruence of the real `closest` in its candidate predicate. -/
theorem holClosestSqrtReal_congr {t w : Nat} {s s' : HolFloat t w → Prop} {r : Rat}
    (h : s = s') : holClosestSqrtReal s r = holClosestSqrtReal s' r :=
  congrArg (fun u => holClosestSqrtReal u r) h

/-- `round mode (sqrt r)` agrees between the cut and real renderings for
    `r ≥ 0`, for every rounding mode. -/
theorem holRoundSqrt_eq_real {t w : Nat} (mode : HolRounding) {r : Rat} (hr : 0 ≤ r) :
    (holRoundSqrt mode r : HolFloat t w) = holRoundSqrtReal mode r := by
  cases mode with
  | roundTiesToEven =>
      simp only [holRoundSqrt, holRoundSqrtReal]
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
  | roundTowardZero =>
      simp only [holRoundSqrt, holRoundSqrtReal]
      by_cases h1 : holSqrtLt r (-(holFloatLargest t w))
      · have h1' : realSqrtOfRat r < ((-(holFloatLargest t w) : Rat) : ℝ) :=
          (holSqrtLt_real_iff hr).mp h1
        rw [if_pos h1, if_pos h1']
      · have h1' : ¬ realSqrtOfRat r < ((-(holFloatLargest t w) : Rat) : ℝ) :=
          fun hh => h1 ((holSqrtLt_real_iff hr).mpr hh)
        rw [if_neg h1, if_neg h1']
        by_cases h2 : holSqrtGt r (holFloatLargest t w)
        · have h2' : ((holFloatLargest t w : Rat) : ℝ) < realSqrtOfRat r :=
            (holSqrtGt_real_iff).mp h2
          rw [if_pos h2, if_pos h2']
        · have h2' : ¬ ((holFloatLargest t w : Rat) : ℝ) < realSqrtOfRat r :=
            fun hh => h2 ((holSqrtGt_real_iff).mpr hh)
          rw [if_neg h2, if_neg h2']
          have hs : (fun a : HolFloat t w =>
                holFloatIsFinite a = true ∧ holSqrtGe r (holRatAbs (holFloatToReal a)))
              = (fun a : HolFloat t w =>
                holFloatIsFinite a = true ∧
                  ((holRatAbs (holFloatToReal a) : Rat) : ℝ) ≤ realSqrtOfRat r) := by
            funext a
            apply propext
            constructor
            · rintro ⟨hf, hge⟩
              exact ⟨hf, (holSqrtGe_real_iff hr).mp hge⟩
            · rintro ⟨hf, hle⟩
              exact ⟨hf, (holSqrtGe_real_iff hr).mpr hle⟩
          exact (holClosestSqrt_real_eq _ hr).trans (holClosestSqrtReal_congr hs)
  | roundTowardPositive =>
      simp only [holRoundSqrt, holRoundSqrtReal]
      by_cases h1 : holSqrtLt r (-(holFloatLargest t w))
      · have h1' : realSqrtOfRat r < ((-(holFloatLargest t w) : Rat) : ℝ) :=
          (holSqrtLt_real_iff hr).mp h1
        rw [if_pos h1, if_pos h1']
      · have h1' : ¬ realSqrtOfRat r < ((-(holFloatLargest t w) : Rat) : ℝ) :=
          fun hh => h1 ((holSqrtLt_real_iff hr).mpr hh)
        rw [if_neg h1, if_neg h1']
        by_cases h2 : holSqrtGt r (holFloatLargest t w)
        · have h2' : ((holFloatLargest t w : Rat) : ℝ) < realSqrtOfRat r :=
            (holSqrtGt_real_iff).mp h2
          rw [if_pos h2, if_pos h2']
        · have h2' : ¬ ((holFloatLargest t w : Rat) : ℝ) < realSqrtOfRat r :=
            fun hh => h2 ((holSqrtGt_real_iff).mpr hh)
          rw [if_neg h2, if_neg h2']
          have hs : (fun a : HolFloat t w =>
                holFloatIsFinite a = true ∧ holSqrtLe r (holFloatToReal a))
              = (fun a : HolFloat t w =>
                holFloatIsFinite a = true ∧
                  realSqrtOfRat r ≤ ((holFloatToReal a : Rat) : ℝ)) := by
            funext a
            apply propext
            constructor
            · rintro ⟨hf, hle⟩
              exact ⟨hf, (holSqrtLe_real_iff).mp hle⟩
            · rintro ⟨hf, hle⟩
              exact ⟨hf, (holSqrtLe_real_iff).mpr hle⟩
          exact (holClosestSqrt_real_eq _ hr).trans (holClosestSqrtReal_congr hs)
  | roundTowardNegative =>
      simp only [holRoundSqrt, holRoundSqrtReal]
      by_cases h1 : holSqrtLt r (-(holFloatLargest t w))
      · have h1' : realSqrtOfRat r < ((-(holFloatLargest t w) : Rat) : ℝ) :=
          (holSqrtLt_real_iff hr).mp h1
        rw [if_pos h1, if_pos h1']
      · have h1' : ¬ realSqrtOfRat r < ((-(holFloatLargest t w) : Rat) : ℝ) :=
          fun hh => h1 ((holSqrtLt_real_iff hr).mpr hh)
        rw [if_neg h1, if_neg h1']
        by_cases h2 : holSqrtGt r (holFloatLargest t w)
        · have h2' : ((holFloatLargest t w : Rat) : ℝ) < realSqrtOfRat r :=
            (holSqrtGt_real_iff).mp h2
          rw [if_pos h2, if_pos h2']
        · have h2' : ¬ ((holFloatLargest t w : Rat) : ℝ) < realSqrtOfRat r :=
            fun hh => h2 ((holSqrtGt_real_iff).mpr hh)
          rw [if_neg h2, if_neg h2']
          have hs : (fun a : HolFloat t w =>
                holFloatIsFinite a = true ∧ holSqrtGe r (holFloatToReal a))
              = (fun a : HolFloat t w =>
                holFloatIsFinite a = true ∧
                  ((holFloatToReal a : Rat) : ℝ) ≤ realSqrtOfRat r) := by
            funext a
            apply propext
            constructor
            · rintro ⟨hf, hge⟩
              exact ⟨hf, (holSqrtGe_real_iff hr).mp hge⟩
            · rintro ⟨hf, hle⟩
              exact ⟨hf, (holSqrtGe_real_iff hr).mpr hle⟩
          exact (holClosestSqrt_real_eq _ hr).trans (holClosestSqrtReal_congr hs)

/-- `float_round mode toneg (sqrt r)` agrees between the cut and real
    renderings for `r ≥ 0`, for every rounding mode. -/
theorem holFloatRoundSqrt_eq_real {t w : Nat} (mode : HolRounding) (toneg : Bool) {r : Rat}
    (hr : 0 ≤ r) :
    (holFloatRoundSqrt mode toneg r : HolFloat t w) =
      (holFloatRoundSqrtReal mode toneg r : HolFloat t w) := by
  unfold holFloatRoundSqrt holFloatRoundSqrtReal
  rw [holRoundSqrt_eq_real mode hr]

/-- `float_round_with_flags mode toNeg (sqrt r)` agrees between the cut and
    real renderings for `r ≥ 0`, for every rounding mode. -/
theorem holFloatRoundWithFlagsSqrt_agreement {t w : Nat} (mode : HolRounding) (toNeg : Bool)
    {r : Rat} (hr : 0 ≤ r) :
    (holFloatRoundWithFlagsSqrt mode toNeg r : HolFloatFlags × HolFloat t w) =
      (holFloatRoundWithFlagsSqrtReal mode toNeg r : HolFloatFlags × HolFloat t w) := by
  unfold holFloatRoundWithFlagsSqrt holFloatRoundWithFlagsSqrtReal
  simp only [holFloatRoundSqrt_eq_real mode toNeg hr, holSqrtEq_real_iff hr,
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

/-- `float_sqrt mode` agrees between the cut and real renderings, for every
    rounding mode. -/
theorem holFloatSqrt_agreement {t w : Nat} (mode : HolRounding) (x : HolFloat t w) :
    holFloatSqrt mode x = holFloatSqrtReal mode x := by
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
      exact holFloatRoundWithFlagsSqrt_agreement mode false
        (hxr ▸ holFloatToReal_nonneg_of_sign_zero hs)
  · rw [if_neg hs, if_neg hs]

/-- `fp64_sqrt mode` agrees between the cut and real renderings, for every
    rounding mode. -/
theorem holFp64Sqrt_agreement (mode : HolRounding) (a : BitVec 64) :
    holFp64Sqrt mode a = holFp64SqrtReal mode a := by
  unfold holFp64Sqrt holFp64SqrtReal
  rw [holFloatSqrt_agreement]

/-- `round roundTiesToEven (sqrt r)` agrees between the cut and real
    renderings for `r ≥ 0` (corollary of `holRoundSqrt_eq_real`). -/
theorem holRoundSqrt_tiesToEven_eq_real {t w : Nat} {r : Rat} (hr : 0 ≤ r) :
    (holRoundSqrt .roundTiesToEven r : HolFloat t w) =
      (holRoundSqrtRealTiesToEven r : HolFloat t w) :=
  holRoundSqrt_eq_real .roundTiesToEven hr

/-- `float_round roundTiesToEven toneg (sqrt r)` agrees between the cut and
    real renderings for `r ≥ 0` (corollary of `holFloatRoundSqrt_eq_real`). -/
theorem holFloatRoundSqrt_tiesToEven_eq_real {t w : Nat} (toneg : Bool) {r : Rat}
    (hr : 0 ≤ r) :
    (holFloatRoundSqrt .roundTiesToEven toneg r : HolFloat t w) =
      (holFloatRoundSqrtReal .roundTiesToEven toneg r : HolFloat t w) :=
  holFloatRoundSqrt_eq_real .roundTiesToEven toneg hr

/-- `float_round_with_flags roundTiesToEven toNeg (sqrt r)` agrees between the
    cut and real renderings for `r ≥ 0` (corollary of
    `holFloatRoundWithFlagsSqrt_agreement`). -/
theorem holFloatRoundWithFlagsSqrt_tiesToEven_agreement {t w : Nat} (toNeg : Bool) {r : Rat}
    (hr : 0 ≤ r) :
    (holFloatRoundWithFlagsSqrt .roundTiesToEven toNeg r : HolFloatFlags × HolFloat t w) =
      (holFloatRoundWithFlagsSqrtReal .roundTiesToEven toNeg r :
        HolFloatFlags × HolFloat t w) :=
  holFloatRoundWithFlagsSqrt_agreement .roundTiesToEven toNeg hr

/-- `float_sqrt roundTiesToEven` agrees between the cut and real renderings
    (corollary of `holFloatSqrt_agreement`). -/
theorem holFloatSqrt_tiesToEven_agreement {t w : Nat} (x : HolFloat t w) :
    holFloatSqrt .roundTiesToEven x = holFloatSqrtReal .roundTiesToEven x :=
  holFloatSqrt_agreement .roundTiesToEven x

/-- `fp64_sqrt roundTiesToEven` agrees between the cut and real renderings
    (corollary of `holFp64Sqrt_agreement`). -/
theorem holFp64Sqrt_tiesToEven_agreement (a : BitVec 64) :
    holFp64Sqrt .roundTiesToEven a = holFp64SqrtReal .roundTiesToEven a :=
  holFp64Sqrt_agreement .roundTiesToEven a

end Flapjack
