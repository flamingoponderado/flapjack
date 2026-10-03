import Flapjack.Misc.MachineIeee
import Flapjack.Misc.BinaryIeeeSqrt.RealCarrier

/-!
# HOL `machine_ieee` fp64 square root over Mathlib reals

The `fp64_sqrt` definition that `machine_ieeeLib` generates at the
`("fp64", 52, 11, SOME "double")` call of
`HOL/src/floating-point/machine_ieeeScript.sml:16`, over the arbitrary-real
`float_sqrt` port of `Flapjack.Misc.BinaryIeeeSqrt.RealCarrier`, and its
agreement with the executed rational-cut `holFp64Sqrt`.
-/

namespace Flapjack

/-- Source-reviewed generated HOL `machine_ieee$fp64_sqrt` at the literal
52/11/64 factory invocation. Its unary flag-dropping lift is
`float_to_fp64 (SND (float_sqrt mode (fp64_to_float a)))`.
The reachable real specification retains all original rounding, flag, choice,
signed-zero and NaN clauses over Mathlib `ℝ`; the cut-to-real equality below
requires no assumed cut criterion. The conservative IEEE qualifier remains
because the codecs and real/zero/classification helpers are in the reviewed
rendering family; it does not claim an independent HOL-to-Lean equivalence
proof. Generic real helpers are infrastructure, not generic HOL ports. -/
@[hol "HOL/src/floating-point/machine_ieeeScript.sml" "fp64_sqrt_def" 16
  (reals_as_rational_cuts)]
noncomputable def holFp64SqrtR (mode : HolRounding) (a : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatSqrtR mode (holFp64ToFloat a)).2

/-- The executed rational-cut `fp64_sqrt` equals the literal real-carrier HOL
`fp64_sqrt`, for every rounding mode and input (no premise). -/
theorem holFp64Sqrt_eq_holFp64SqrtR (mode : HolRounding) (a : BitVec 64) :
    holFp64Sqrt mode a = holFp64SqrtR mode a := by
  unfold holFp64Sqrt holFp64SqrtR
  rw [holFloatSqrt_eq_holFloatSqrtR]

end Flapjack
