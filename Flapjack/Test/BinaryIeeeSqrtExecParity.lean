import Flapjack.Misc.BinaryIeeeSqrtExec

/-!
The executable binary64 square root `execFp64Sqrt` against the direct HOL
`fp64_sqrt roundTiesToEven` oracle rows of
`scripts/hol-probes/machine_ieee_fp64_sqrt_exact_probe.out` and
`machine_ieee_fp64_sqrt_special_probe.out` (bit-equal in every choice-free
branch), plus the choice branches (negative input, NaN input), where it must
return a quiet NaN, as `holFp64Sqrt_refines_exec` states.
-/

namespace Flapjack.Test.BinaryIeeeSqrtExecParity

open Flapjack

-- machine_ieee_fp64_sqrt_exact_probe.out
#guard execFp64Sqrt 0x4010000000000000 = 0x4000000000000000  -- sqrt_four
#guard execFp64Sqrt 0x3FD0000000000000 = 0x3FE0000000000000  -- sqrt_quarter
#guard execFp64Sqrt 0x4022000000000000 = 0x4008000000000000  -- sqrt_nine
#guard execFp64Sqrt 0x3FF0000000000000 = 0x3FF0000000000000  -- sqrt_one
#guard execFp64Sqrt 0x0000000000000000 = 0x0000000000000000  -- sqrt_pz
#guard execFp64Sqrt 0x0000000000000001 = 0x1E60000000000000  -- sqrt_min_sub
#guard execFp64Sqrt 0x7FD0000000000000 = 0x5FE0000000000000  -- sqrt_2p1022
-- machine_ieee_fp64_sqrt_special_probe.out
#guard execFp64Sqrt 0x7FF0000000000000 = 0x7FF0000000000000  -- sqrt_pinf
#guard execFp64Sqrt 0x8000000000000000 = 0x8000000000000000  -- sqrt_nz
-- choice branches: a quiet NaN is produced
#guard holFp64IsNan (execFp64Sqrt 0xBFF0000000000000) && !holFp64IsSignalling (execFp64Sqrt 0xBFF0000000000000)
#guard holFp64IsNan (execFp64Sqrt 0x7FF8000000000000) && !holFp64IsSignalling (execFp64Sqrt 0x7FF8000000000000)
#guard holFp64IsNan (execFp64Sqrt 0x7FF0000000000001) && !holFp64IsSignalling (execFp64Sqrt 0x7FF0000000000001)

example (a : BitVec 64) : fp64Refines (holFp64Sqrt .roundTiesToEven a) (execFp64Sqrt a) :=
  holFp64Sqrt_refines_exec a

end Flapjack.Test.BinaryIeeeSqrtExecParity
