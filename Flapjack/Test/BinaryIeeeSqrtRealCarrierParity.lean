import Flapjack.Misc.MachineIeee.SqrtReal
import Flapjack.Misc.BinaryIeeeSqrtFp64

/-!
# Original `fp64_sqrt` rows through the literal real-carrier `float_sqrt`

`holFp64Sqrt_eq_holFp64SqrtR` states that the executed rational-cut
`holFp64Sqrt` equals `holFp64SqrtR`, the literal HOL `float_sqrt` over Mathlib
`ℝ` with `Real.sqrt`. Each row below instantiates that equality and then
kernel-evaluates the computable cut algorithm `holFp64Sqrt_rte`, so the
real-carrier result is kernel-checked against the original HOL `EVAL` rows of
the existing `fp64_sqrt` probe (`sqrt_four`, `sqrt_one`, `sqrt_min_sub`,
`sqrt_2p1022`).
-/

namespace Flapjack.Test.BinaryIeeeSqrtRealCarrierParity

open Flapjack

/-- `sqrt_four=0x4000000000000000w` through the real-carrier `fp64_sqrt`. -/
theorem sqrtFourR : holFp64SqrtR .roundTiesToEven 0x4010000000000000 = 0x4000000000000000 := by
  rw [← holFp64Sqrt_eq_holFp64SqrtR, holFp64Sqrt_rte]
  decide +kernel
/-- `sqrt_one=0x3FF0000000000000w` through the real-carrier `fp64_sqrt`. -/
theorem sqrtOneR : holFp64SqrtR .roundTiesToEven 0x3FF0000000000000 = 0x3FF0000000000000 := by
  rw [← holFp64Sqrt_eq_holFp64SqrtR, holFp64Sqrt_rte]
  decide +kernel
/-- `sqrt_min_sub=0x1E60000000000000w` through the real-carrier `fp64_sqrt`. -/
theorem sqrtMinSubR : holFp64SqrtR .roundTiesToEven 0x1 = 0x1E60000000000000 := by
  rw [← holFp64Sqrt_eq_holFp64SqrtR, holFp64Sqrt_rte]
  decide +kernel
/-- `sqrt_2p1022=0x5FE0000000000000w` through the real-carrier `fp64_sqrt`. -/
theorem sqrt2p1022R : holFp64SqrtR .roundTiesToEven 0x7FD0000000000000 = 0x5FE0000000000000 := by
  rw [← holFp64Sqrt_eq_holFp64SqrtR, holFp64Sqrt_rte]
  decide +kernel

def runChecks : IO Bool := do
  IO.println "PASS literal real-carrier fp64_sqrt matches four original HOL rows via the cut agreement (kernel-checked)"
  pure true

end Flapjack.Test.BinaryIeeeSqrtRealCarrierParity
