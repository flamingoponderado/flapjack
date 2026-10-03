import Flapjack.Misc.BinaryIeeeArith
import Flapjack.Misc.BinaryIeeeRoundFp64
import Flapjack.FpSemHOL

/-!
# binary64 arithmetic through the computable roundTiesToEven

For each of `float_add`, `float_sub`, `float_mul`, `float_div` and
`float_mul_add` at binary64 and `roundTiesToEven` (bead
`flapjack-h29l.6.2.4`), this module gives a variant with the same case
structure.  The variant's finite branch uses the computable
`holFp64RoundTiesToEven` in place of the choice-based
`float_round_with_flags`.  Each variant is proved equal to the float
component of the HOL rendering (`holFloatAdd_rte64` and the others), using
the conformance theorem `holFloatRound_rte_fp64`.  NaN results still go
through the unspecified `float_some_qnan`, so the variants stay
`noncomputable`, but the kernel evaluates every non-NaN branch.  The `fp64`
lifts and the tagged `fpSem` `fpfma` are rewritten accordingly.  HOL
standard library, so untagged.
-/

namespace Flapjack

/-- The float component of `float_round_with_flags` is `float_round`. -/
theorem holFloatRoundWithFlags_snd {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (toNeg : Bool) (r : Rat) :
    (holFloatRoundWithFlags mode toNeg r : HolFloatFlags × HolFloat t w).2 =
      holFloatRound mode toNeg r := rfl

/-- `float_add roundTiesToEven` at binary64 with the computable rounding. -/
noncomputable def holFloatAddRte64 (x y : HolFloat 52 11) : HolFloat 52 11 :=
  match holFloatValue x, holFloatValue y with
  | .nan, _ => (holFloatSomeQnan (.fpAdd .roundTiesToEven x y))
  | _, .nan => (holFloatSomeQnan (.fpAdd .roundTiesToEven x y))
  | .infinity, .infinity =>
      if x.sign = y.sign then (x)
      else (holFloatSomeQnan (.fpAdd .roundTiesToEven x y))
  | .infinity, _ => (x)
  | _, .infinity => (y)
  | .float r1, .float r2 =>
      holFp64RoundTiesToEven
        (if r1 = 0 ∧ r2 = 0 ∧ x.sign = y.sign then x.sign = 1 else .roundTiesToEven = HolRounding.roundTowardNegative)
        (r1 + r2)

theorem holFloatAdd_rte64 (x y : HolFloat 52 11) :
    (holFloatAdd .roundTiesToEven x y).2 = holFloatAddRte64 x y := by
  unfold holFloatAdd holFloatAddRte64
  repeat' split
  all_goals first
    | rfl
    | (exfalso; simp_all; done)
    | (rw [holFloatRoundWithFlags_snd, holFloatRound_rte_fp64]; done)
    | (rw [holFloatRoundWithFlags_snd, holFloatRound_rte_fp64]; simp_all; done)
    | (simp_all; done)

/-- `float_sub roundTiesToEven` at binary64 with the computable rounding. -/
noncomputable def holFloatSubRte64 (x y : HolFloat 52 11) : HolFloat 52 11 :=
  match holFloatValue x, holFloatValue y with
  | .nan, _ => (holFloatSomeQnan (.fpSub .roundTiesToEven x y))
  | _, .nan => (holFloatSomeQnan (.fpSub .roundTiesToEven x y))
  | .infinity, .infinity =>
      if x.sign = y.sign then (holFloatSomeQnan (.fpSub .roundTiesToEven x y))
      else (x)
  | .infinity, _ => (x)
  | _, .infinity => (holFloatNegate y)
  | .float r1, .float r2 =>
      holFp64RoundTiesToEven
        (if r1 = 0 ∧ r2 = 0 ∧ x.sign ≠ y.sign then x.sign = 1 else .roundTiesToEven = HolRounding.roundTowardNegative)
        (r1 - r2)

theorem holFloatSub_rte64 (x y : HolFloat 52 11) :
    (holFloatSub .roundTiesToEven x y).2 = holFloatSubRte64 x y := by
  unfold holFloatSub holFloatSubRte64
  repeat' split
  all_goals first
    | rfl
    | (exfalso; simp_all; done)
    | (rw [holFloatRoundWithFlags_snd, holFloatRound_rte_fp64]; done)
    | (rw [holFloatRoundWithFlags_snd, holFloatRound_rte_fp64]; simp_all; done)
    | (simp_all; done)

/-- `float_mul roundTiesToEven` at binary64 with the computable rounding. -/
noncomputable def holFloatMulRte64 (x y : HolFloat 52 11) : HolFloat 52 11 :=
  let signedInf : HolFloat 52 11 :=
    if x.sign = y.sign then holFloatPlusInfinity 52 11 else holFloatMinusInfinity 52 11
  match holFloatValue x, holFloatValue y with
  | .nan, _ => (holFloatSomeQnan (.fpMul .roundTiesToEven x y))
  | _, .nan => (holFloatSomeQnan (.fpMul .roundTiesToEven x y))
  | .infinity, .float r =>
      if r = 0 then (holFloatSomeQnan (.fpMul .roundTiesToEven x y))
      else (signedInf)
  | .float r, .infinity =>
      if r = 0 then (holFloatSomeQnan (.fpMul .roundTiesToEven x y))
      else (signedInf)
  | .infinity, .infinity => (signedInf)
  | .float r1, .float r2 => holFp64RoundTiesToEven (x.sign ≠ y.sign) (r1 * r2)

theorem holFloatMul_rte64 (x y : HolFloat 52 11) :
    (holFloatMul .roundTiesToEven x y).2 = holFloatMulRte64 x y := by
  unfold holFloatMul holFloatMulRte64
  repeat' split
  all_goals first
    | rfl
    | (exfalso; simp_all; done)
    | (rw [holFloatRoundWithFlags_snd, holFloatRound_rte_fp64]; done)
    | (rw [holFloatRoundWithFlags_snd, holFloatRound_rte_fp64]; simp_all; done)
    | (simp_all; done)

/-- `float_div roundTiesToEven` at binary64 with the computable rounding. -/
noncomputable def holFloatDivRte64 (x y : HolFloat 52 11) : HolFloat 52 11 :=
  let signedInf : HolFloat 52 11 :=
    if x.sign = y.sign then holFloatPlusInfinity 52 11 else holFloatMinusInfinity 52 11
  match holFloatValue x, holFloatValue y with
  | .nan, _ => (holFloatSomeQnan (.fpDiv .roundTiesToEven x y))
  | _, .nan => (holFloatSomeQnan (.fpDiv .roundTiesToEven x y))
  | .infinity, .infinity => (holFloatSomeQnan (.fpDiv .roundTiesToEven x y))
  | .infinity, _ => (signedInf)
  | _, .infinity =>
      (if x.sign = y.sign then holFloatPlusZero 52 11 else holFloatMinusZero 52 11)
  | .float r1, .float r2 =>
      if r2 = 0 then
        if r1 = 0 then (holFloatSomeQnan (.fpDiv .roundTiesToEven x y))
        else (signedInf)
      else holFp64RoundTiesToEven (x.sign ≠ y.sign) (r1 / r2)

theorem holFloatDiv_rte64 (x y : HolFloat 52 11) :
    (holFloatDiv .roundTiesToEven x y).2 = holFloatDivRte64 x y := by
  unfold holFloatDiv holFloatDivRte64
  repeat' split
  all_goals first
    | rfl
    | (exfalso; simp_all; done)
    | (rw [holFloatRoundWithFlags_snd, holFloatRound_rte_fp64]; done)
    | (rw [holFloatRoundWithFlags_snd, holFloatRound_rte_fp64]; simp_all; done)
    | (simp_all; done)

/-- `float_mul_add roundTiesToEven` at binary64 with the computable rounding. -/
noncomputable def holFloatMulAddRte64 (x y z : HolFloat 52 11) : HolFloat 52 11 :=
  let signP := x.sign ^^^ y.sign
  let infP := holFloatIsInfinite x || holFloatIsInfinite y
  if holFloatIsNan x || holFloatIsNan y || holFloatIsNan z then
    (holFloatSomeQnan (.fpMulAdd .roundTiesToEven x y z))
  else if (holFloatIsInfinite x && holFloatIsZero y) || (holFloatIsZero x && holFloatIsInfinite y) ||
      (holFloatIsInfinite z && infP && decide (signP ≠ z.sign)) then
    (holFloatSomeQnan (.fpMulAdd .roundTiesToEven x y z))
  else if (holFloatIsInfinite z && decide (z.sign = 0)) || (infP && decide (signP = 0)) then
    (holFloatPlusInfinity 52 11)
  else if (holFloatIsInfinite z && decide (z.sign = 1)) || (infP && decide (signP = 1)) then
    (holFloatMinusInfinity 52 11)
  else
    let r1 := holFloatToReal x * holFloatToReal y
    let r2 := holFloatToReal z
    let r := r1 + r2
    holFp64RoundTiesToEven
      (decide (r = 0 ∧
          (if r1 = 0 ∧ r2 = 0 ∧ signP = z.sign then signP = 1 else .roundTiesToEven = HolRounding.roundTowardNegative)) ||
        decide (r < 0))
      r

theorem holFloatMulAdd_rte64 (x y z : HolFloat 52 11) :
    (holFloatMulAdd .roundTiesToEven x y z).2 = holFloatMulAddRte64 x y z := by
  unfold holFloatMulAdd holFloatMulAddRte64
  dsimp only
  repeat' split
  all_goals first
    | rfl
    | (exfalso; simp_all; done)
    | (rw [holFloatRoundWithFlags_snd, holFloatRound_rte_fp64]; done)
    | (rw [holFloatRoundWithFlags_snd, holFloatRound_rte_fp64]; simp_all; done)
    | (simp_all; done)

/-- `fp64_add roundTiesToEven` through the computable rounding. -/
theorem holFp64Add_rte (a b : BitVec 64) : holFp64Add .roundTiesToEven a b =
    holFloatToFp64 (holFloatAddRte64 (holFp64ToFloat a) (holFp64ToFloat b)) := by
  unfold holFp64Add; rw [holFloatAdd_rte64]

/-- `fp64_sub roundTiesToEven` through the computable rounding. -/
theorem holFp64Sub_rte (a b : BitVec 64) : holFp64Sub .roundTiesToEven a b =
    holFloatToFp64 (holFloatSubRte64 (holFp64ToFloat a) (holFp64ToFloat b)) := by
  unfold holFp64Sub; rw [holFloatSub_rte64]

/-- `fp64_mul roundTiesToEven` through the computable rounding. -/
theorem holFp64Mul_rte (a b : BitVec 64) : holFp64Mul .roundTiesToEven a b =
    holFloatToFp64 (holFloatMulRte64 (holFp64ToFloat a) (holFp64ToFloat b)) := by
  unfold holFp64Mul; rw [holFloatMul_rte64]

/-- `fp64_div roundTiesToEven` through the computable rounding. -/
theorem holFp64Div_rte (a b : BitVec 64) : holFp64Div .roundTiesToEven a b =
    holFloatToFp64 (holFloatDivRte64 (holFp64ToFloat a) (holFp64ToFloat b)) := by
  unfold holFp64Div; rw [holFloatDiv_rte64]

/-- The tagged `fpSem` `fpfma` through the computable rounding. -/
theorem fpSemFpfma_rte (v1 v2 v3 : BitVec 64) : fpSemFpfma v1 v2 v3 =
    holFloatToFp64 (holFloatMulAddRte64 (holFp64ToFloat v2) (holFp64ToFloat v3)
      (holFp64ToFloat v1)) := by
  unfold fpSemFpfma holFp64MulAdd; rw [holFloatMulAdd_rte64]

end Flapjack
