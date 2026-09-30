import Flapjack.Misc.BinaryIeeeSqrt.RoundAgreement
import Flapjack.Misc.BinaryIeeeSqrtFp64

/-!
# Concrete agreement of the real-sqrt and rational-cut `fp64_sqrt` renderings

`holFp64Sqrt_tiesToEven_agreement` states, for every binary64 input, that the
rational-cut rendering `holFp64Sqrt` of HOL `fp64_sqrt roundTiesToEven` equals
the real-distance rendering `holFp64SqrtReal` from
`Flapjack.Misc.BinaryIeeeSqrt.RoundAgreement`.  Each theorem below instantiates
that agreement on a concrete input and then kernel-evaluates the computable
cut algorithm, so the real-rendering result is kernel-checked too.

The non-square rows are not HOL oracles (HOL `EVAL` cannot reduce an irrational
`sqrt`); they are cross-checked against Lean's hardware `Float.sqrt`, as in
`Flapjack.Test.MachineIeeeSqrtExactParity`.
-/

namespace Flapjack.Test.BinaryIeeeSqrtRoundAgreementParity

open Flapjack

/-- `sqrt_four=0x4000000000000000w` through the real rendering. -/
theorem sqrtFourReal : holFp64SqrtReal 0x4010000000000000 = 0x4000000000000000 := by
  rw [← holFp64Sqrt_tiesToEven_agreement]
  rw [holFp64Sqrt_rte]
  decide +kernel
/-- `sqrt_one=0x3FF0000000000000w` through the real rendering. -/
theorem sqrtOneReal : holFp64SqrtReal 0x3FF0000000000000 = 0x3FF0000000000000 := by
  rw [← holFp64Sqrt_tiesToEven_agreement]
  rw [holFp64Sqrt_rte]
  decide +kernel
/-- `sqrt_min_sub=0x1E60000000000000w` through the real rendering. -/
theorem sqrtMinSubReal : holFp64SqrtReal 0x1 = 0x1E60000000000000 := by
  rw [← holFp64Sqrt_tiesToEven_agreement]
  rw [holFp64Sqrt_rte]
  decide +kernel
/-- `sqrt_2p1022=0x5FE0000000000000w` through the real rendering. -/
theorem sqrt2p1022Real : holFp64SqrtReal 0x7FD0000000000000 = 0x5FE0000000000000 := by
  rw [← holFp64Sqrt_tiesToEven_agreement]
  rw [holFp64Sqrt_rte]
  decide +kernel
/-- Non-square: `sqrt 2.0` through the real rendering; not a HOL oracle row. -/
theorem sqrtTwoReal : holFp64SqrtReal 0x4000000000000000 = 0x3FF6A09E667F3BCD := by
  rw [← holFp64Sqrt_tiesToEven_agreement]
  rw [holFp64Sqrt_rte]
  decide +kernel
#guard (Float.sqrt (Float.ofBits 0x4000000000000000)).toBits == 0x3FF6A09E667F3BCD
/-- Non-square: `sqrt 1.7976931348623157e308` through the real rendering; not a
    HOL oracle row. -/
theorem sqrtMaxFinReal : holFp64SqrtReal 0x7FEFFFFFFFFFFFFF = 0x5FEFFFFFFFFFFFFF := by
  rw [← holFp64Sqrt_tiesToEven_agreement]
  rw [holFp64Sqrt_rte]
  decide +kernel
#guard (Float.sqrt (Float.ofBits 0x7FEFFFFFFFFFFFFF)).toBits == 0x5FEFFFFFFFFFFFFF

/-- The `roundTiesToEven` cut and real rounders agree at a concrete input. -/
theorem roundFourReal :
    (holRoundSqrtRealTiesToEven (4 : Rat) : HolFloat 52 11) =
      holRoundSqrt .roundTiesToEven (4 : Rat) := by
  rw [holRoundSqrt_tiesToEven_eq_real (by norm_num : (0 : Rat) ≤ 4)]

def runChecks : IO Bool := do
  IO.println "PASS real-sqrt rounding agrees with the rational-cut rendering on concrete fp64_sqrt inputs (kernel-checked)"
  pure true

end Flapjack.Test.BinaryIeeeSqrtRoundAgreementParity
