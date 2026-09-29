import Flapjack.Misc.BinaryIeeeSqrtFp64

/-!
Direct HOL oracle rows for binary64 `fp64_sqrt roundTiesToEven` on exact
squares (`scripts/hol-probes/machine_ieee_fp64_sqrt_exact_probe.out`, generated
by `machine_ieee_fp64_sqrt_exact_probeScript.sml`; HOL `isqrtLib` proves each
`sqrt` from `realTheory.POW_2_SQRT`).  Each row is a kernel-checked theorem
about the rational-cut rendering `holFp64Sqrt`, proved through
`holFp64Sqrt_rte` and kernel evaluation.

The non-square rows below are not HOL oracles, since HOL EVAL cannot reduce
an irrational `sqrt`.  They are kernel-checked values of the specification.
The `#guard`s cross-check them against Lean's hardware `Float.sqrt`, which
is IEEE-754 correctly rounded.
-/

namespace Flapjack.Test.MachineIeeeSqrtExactParity

open Flapjack

/-- `sqrt_four=0x4000000000000000w` -/
theorem sqrtFour : holFp64Sqrt .roundTiesToEven 0x4010000000000000 = 0x4000000000000000 := by
  rw [holFp64Sqrt_rte]; decide +kernel
/-- `sqrt_quarter=0x3FE0000000000000w` -/
theorem sqrtQuarter : holFp64Sqrt .roundTiesToEven 0x3FD0000000000000 = 0x3FE0000000000000 := by
  rw [holFp64Sqrt_rte]; decide +kernel
/-- `sqrt_nine=0x4008000000000000w` -/
theorem sqrtNine : holFp64Sqrt .roundTiesToEven 0x4022000000000000 = 0x4008000000000000 := by
  rw [holFp64Sqrt_rte]; decide +kernel
/-- `sqrt_one=0x3FF0000000000000w` -/
theorem sqrtOne : holFp64Sqrt .roundTiesToEven 0x3FF0000000000000 = 0x3FF0000000000000 := by
  rw [holFp64Sqrt_rte]; decide +kernel
/-- `sqrt_pz=0w` -/
theorem sqrtPz : holFp64Sqrt .roundTiesToEven 0x0 = 0 := by
  rw [holFp64Sqrt_rte]; decide +kernel
/-- `sqrt_min_sub=0x1E60000000000000w` -/
theorem sqrtMinSub : holFp64Sqrt .roundTiesToEven 0x1 = 0x1E60000000000000 := by
  rw [holFp64Sqrt_rte]; decide +kernel
/-- `sqrt_2p1022=0x5FE0000000000000w` -/
theorem sqrt2p1022 : holFp64Sqrt .roundTiesToEven 0x7FD0000000000000 = 0x5FE0000000000000 := by
  rw [holFp64Sqrt_rte]; decide +kernel

/-- Non-square: `sqrt 2.0`, not a HOL oracle row. -/
theorem sqrtTwo : holFp64Sqrt .roundTiesToEven 0x4000000000000000 = 0x3FF6A09E667F3BCD := by
  rw [holFp64Sqrt_rte]; decide +kernel
#guard (Float.sqrt (Float.ofBits 0x4000000000000000)).toBits == 0x3FF6A09E667F3BCD
/-- Non-square: `sqrt 3.0`, not a HOL oracle row. -/
theorem sqrtThree : holFp64Sqrt .roundTiesToEven 0x4008000000000000 = 0x3FFBB67AE8584CAA := by
  rw [holFp64Sqrt_rte]; decide +kernel
#guard (Float.sqrt (Float.ofBits 0x4008000000000000)).toBits == 0x3FFBB67AE8584CAA
/-- Non-square: `sqrt 0.5`, not a HOL oracle row. -/
theorem sqrtHalf : holFp64Sqrt .roundTiesToEven 0x3FE0000000000000 = 0x3FE6A09E667F3BCD := by
  rw [holFp64Sqrt_rte]; decide +kernel
#guard (Float.sqrt (Float.ofBits 0x3FE0000000000000)).toBits == 0x3FE6A09E667F3BCD
/-- Non-square: `sqrt 1.7976931348623157e308`, not a HOL oracle row. -/
theorem sqrtMaxFin : holFp64Sqrt .roundTiesToEven 0x7FEFFFFFFFFFFFFF = 0x5FEFFFFFFFFFFFFF := by
  rw [holFp64Sqrt_rte]; decide +kernel
#guard (Float.sqrt (Float.ofBits 0x7FEFFFFFFFFFFFFF)).toBits == 0x5FEFFFFFFFFFFFFF

def runChecks : IO Bool := do
  IO.println "PASS binary64 fp64_sqrt matches all 7 exact-square HOL oracle rows (kernel-checked); 4 non-square values kernel-checked and cross-checked against hardware sqrt"
  pure true

end Flapjack.Test.MachineIeeeSqrtExactParity
