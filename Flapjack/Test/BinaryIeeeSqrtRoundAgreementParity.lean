import Flapjack.Misc.BinaryIeeeSqrt.RoundAgreement
import Flapjack.Misc.BinaryIeeeSqrtFp64

/-!
# Concrete agreement of the real-sqrt and rational-cut `fp64_sqrt` renderings

For every `HolRounding` mode, `holFp64Sqrt_agreement` states that the
Lean rational-cut rendering `holFp64Sqrt` equals the
real-distance rendering `holFp64SqrtReal` from
`Flapjack.Misc.BinaryIeeeSqrt.RoundAgreement`.  Each `roundTiesToEven` row
below instantiates that agreement on a concrete input and then kernel-evaluates
the computable cut algorithm `holFp64Sqrt_rte`
(`Flapjack.Misc.BinaryIeeeSqrtFp64`), so the real-rendering result is
kernel-checked too.

The other three rounding modes have no computable rendering in Flapjack: their
`round` uses `closest`, expressed by Hilbert choice over the finite float carrier,
and this harness supplies no numeric conversion for that choice. The existing
`isqrtLib` oracle path used here supports `roundTiesToEven`.  Their finite rows are
therefore only concrete instances of the general agreement theorem, not
evaluated numbers.  The `+infinity` and `-0` rows below are kernel-evaluated
for the non-`roundTiesToEven` modes because those branches of `float_sqrt` do
not invoke the choice.  The non-square rows are not HOL oracles (HOL `EVAL`
cannot reduce an irrational `sqrt`); they are cross-checked against Lean's
hardware `Float.sqrt`, as in `Flapjack.Test.MachineIeeeSqrtExactParity`.
-/

namespace Flapjack.Test.BinaryIeeeSqrtRoundAgreementParity

open Flapjack

/-- `sqrt_four=0x4000000000000000w` through the real rendering. -/
theorem sqrtFourReal :
    holFp64SqrtReal .roundTiesToEven 0x4010000000000000 = 0x4000000000000000 := by
  rw [← holFp64Sqrt_tiesToEven_agreement]
  rw [holFp64Sqrt_rte]
  decide +kernel
/-- `sqrt_one=0x3FF0000000000000w` through the real rendering. -/
theorem sqrtOneReal :
    holFp64SqrtReal .roundTiesToEven 0x3FF0000000000000 = 0x3FF0000000000000 := by
  rw [← holFp64Sqrt_tiesToEven_agreement]
  rw [holFp64Sqrt_rte]
  decide +kernel
/-- `sqrt_min_sub=0x1E60000000000000w` through the real rendering. -/
theorem sqrtMinSubReal :
    holFp64SqrtReal .roundTiesToEven 0x1 = 0x1E60000000000000 := by
  rw [← holFp64Sqrt_tiesToEven_agreement]
  rw [holFp64Sqrt_rte]
  decide +kernel
/-- `sqrt_2p1022=0x5FE0000000000000w` through the real rendering. -/
theorem sqrt2p1022Real :
    holFp64SqrtReal .roundTiesToEven 0x7FD0000000000000 = 0x5FE0000000000000 := by
  rw [← holFp64Sqrt_tiesToEven_agreement]
  rw [holFp64Sqrt_rte]
  decide +kernel
/-- Non-square: `sqrt 2.0` through the real rendering; not a HOL oracle row. -/
theorem sqrtTwoReal :
    holFp64SqrtReal .roundTiesToEven 0x4000000000000000 = 0x3FF6A09E667F3BCD := by
  rw [← holFp64Sqrt_tiesToEven_agreement]
  rw [holFp64Sqrt_rte]
  decide +kernel
#guard (Float.sqrt (Float.ofBits 0x4000000000000000)).toBits == 0x3FF6A09E667F3BCD
/-- Non-square: `sqrt 1.7976931348623157e308` through the real rendering; not a
    HOL oracle row. -/
theorem sqrtMaxFinReal :
    holFp64SqrtReal .roundTiesToEven 0x7FEFFFFFFFFFFFFF = 0x5FEFFFFFFFFFFFFF := by
  rw [← holFp64Sqrt_tiesToEven_agreement]
  rw [holFp64Sqrt_rte]
  decide +kernel
#guard (Float.sqrt (Float.ofBits 0x7FEFFFFFFFFFFFFF)).toBits == 0x5FEFFFFFFFFFFFFF

/-- The `roundTiesToEven` cut and real rounders agree at a concrete input. -/
theorem roundFourReal :
    (holRoundSqrtRealTiesToEven (4 : Rat) : HolFloat 52 11) =
      holRoundSqrt .roundTiesToEven (4 : Rat) := by
  rw [holRoundSqrt_tiesToEven_eq_real (by norm_num : (0 : Rat) ≤ 4)]

/-- The `roundTowardZero` cut and real rounders agree at a concrete input
    (finite rows of the non-`roundTiesToEven` modes lack a numeric conversion here,
    so this is a concrete instance of the general theorem rather than a number). -/
theorem roundFourTowardZero :
    (holRoundSqrtReal .roundTowardZero (4 : Rat) : HolFloat 52 11) =
      holRoundSqrt .roundTowardZero (4 : Rat) :=
  (holRoundSqrt_eq_real .roundTowardZero (by norm_num : (0 : Rat) ≤ 4)).symm

/-- The `roundTowardPositive` cut and real rounders agree at a concrete input. -/
theorem roundFourTowardPositive :
    (holRoundSqrtReal .roundTowardPositive (4 : Rat) : HolFloat 52 11) =
      holRoundSqrt .roundTowardPositive (4 : Rat) :=
  (holRoundSqrt_eq_real .roundTowardPositive (by norm_num : (0 : Rat) ≤ 4)).symm

/-- The `roundTowardNegative` cut and real rounders agree at a concrete input. -/
theorem roundFourTowardNegative :
    (holRoundSqrtReal .roundTowardNegative (4 : Rat) : HolFloat 52 11) =
      holRoundSqrt .roundTowardNegative (4 : Rat) :=
  (holRoundSqrt_eq_real .roundTowardNegative (by norm_num : (0 : Rat) ≤ 4)).symm

/-- `fp64_sqrt` agreement is available uniformly over all four modes. -/
theorem fp64SqrtAgreementAllModes (mode : HolRounding) (a : BitVec 64) :
    holFp64Sqrt mode a = holFp64SqrtReal mode a :=
  holFp64Sqrt_agreement mode a

/-- The `+infinity` branch does not invoke the choice, so the non-
    `roundTiesToEven` real rendering is kernel-evaluable there. -/
theorem sqrtPinfTowardZero :
    holFp64SqrtReal .roundTowardZero 0x7FF0000000000000 = 0x7FF0000000000000 := by
  decide +kernel
/-- `+infinity` through the `roundTowardPositive` real rendering. -/
theorem sqrtPinfTowardPositive :
    holFp64SqrtReal .roundTowardPositive 0x7FF0000000000000 = 0x7FF0000000000000 := by
  decide +kernel
/-- `+infinity` through the `roundTowardNegative` real rendering. -/
theorem sqrtPinfTowardNegative :
    holFp64SqrtReal .roundTowardNegative 0x7FF0000000000000 = 0x7FF0000000000000 := by
  decide +kernel
/-- `-0` through the `roundTowardZero` real rendering. -/
theorem sqrtNzTowardZero :
    holFp64SqrtReal .roundTowardZero 0x8000000000000000 = 0x8000000000000000 := by
  decide +kernel
/-- `-0` through the `roundTowardPositive` real rendering. -/
theorem sqrtNzTowardPositive :
    holFp64SqrtReal .roundTowardPositive 0x8000000000000000 = 0x8000000000000000 := by
  decide +kernel
/-- `-0` through the `roundTowardNegative` real rendering. -/
theorem sqrtNzTowardNegative :
    holFp64SqrtReal .roundTowardNegative 0x8000000000000000 = 0x8000000000000000 := by
  decide +kernel

/-- Negative finite inputs retain all original invalid-operation flags for every mode. -/
theorem sqrtNegativeFlagsAllModes (mode : HolRounding) :
    (holFloatSqrtReal mode (holFp64ToFloat 0xC010000000000000)).1 = holInvalidopFlags := by
  cases mode <;> decide +kernel

/-- A quiet NaN preserves the original clear flags for every mode. Payload
choice is not replaced by a numerical representative. -/
theorem sqrtQuietNanFlagsAllModes (mode : HolRounding) :
    (holFloatSqrtReal mode (holFp64ToFloat 0x7FF8000000000001)).1 = holClearFlags := by
  cases mode <;> decide +kernel

def runChecks : IO Bool := do
  IO.println "PASS real-sqrt rounding agrees with the rational-cut rendering on concrete fp64_sqrt inputs for all HolRounding modes (kernel-checked)"
  pure true

end Flapjack.Test.BinaryIeeeSqrtRoundAgreementParity
