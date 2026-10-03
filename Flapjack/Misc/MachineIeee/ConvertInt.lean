import Flapjack.Misc.BinaryIeeeConvert
import Flapjack.Misc.MachineIeee

/-!
# HOL `machine_ieee` fp64 integer conversions

The `fp64_to_int`, `real_to_fp64` and `int_to_fp64` definitions that
`machine_ieeeLib` generates at the `("fp64", 52, 11, SOME "double")` call of
`HOL/src/floating-point/machine_ieeeScript.sml:16`, used by wordSem
`inst_def`'s `FPToInt` and `FPFromInt` cases.  The executed `real_to_fp64`
here takes `Rat`, a restriction of HOL's arbitrary-real domain, and is
untagged; its tagged arbitrary-real port is `holRealToFp64R`
(`Flapjack.Misc.MachineIeee.ConvertReal`).
-/

namespace Flapjack

/-- HOL `fp64_to_int mode = float_to_int mode o fp64_to_float`. -/
def holFp64ToInt (mode : HolRounding) (a : BitVec 64) : Option Int :=
  holFloatToInt mode (holFp64ToFloat a)

/-- HOL `real_to_fp64 mode = float_to_fp64 o real_to_float mode`, restricted
    to rational inputs like `holRealToFloat`. -/
noncomputable def holRealToFp64 (mode : HolRounding) (r : Rat) : BitVec 64 :=
  holFloatToFp64 (holRealToFloat mode r)

/-- HOL `int_to_fp64 mode a = real_to_fp64 mode (real_of_int a)`. -/
noncomputable def holIntToFp64 (mode : HolRounding) (a : Int) : BitVec 64 :=
  holRealToFp64 mode (a : Rat)

/-- `int_to_fp64 roundTiesToEven` through the computable rounding. -/
theorem holIntToFp64_rte (a : Int) :
    holIntToFp64 .roundTiesToEven a = holFloatToFp64 (holFp64RoundTiesToEven false (a : Rat)) := by
  unfold holIntToFp64 holRealToFp64 holRealToFloat
  rw [holFloatRound_rte_fp64]
  rfl

end Flapjack
