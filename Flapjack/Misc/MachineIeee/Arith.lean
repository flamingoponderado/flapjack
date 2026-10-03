import Flapjack.Misc.BinaryIeeeArith
import Flapjack.Misc.MachineIeee

/-!
# HOL `machine_ieee` fp64 arithmetic lifts

The `fp64_add`/`fp64_sub`/`fp64_mul`/`fp64_div`/`fp64_mul_add` definitions that
`machine_ieeeLib` generates at the `("fp64", 52, 11, SOME "double")` call of
`HOL/src/floating-point/machine_ieeeScript.sml:16`: each is
`float_to_fp64 (SND (float_op mode (fp64_to_float a) ...))` over the
`binary_ieee` operations of `Flapjack.Misc.BinaryIeeeArith`.  WordSem observes
only the output word, not IEEE flags.
-/

namespace Flapjack

/-- HOL `fp64_add mode a b = float_to_fp64 (SND (float_add mode (fp64_to_float a)
    (fp64_to_float b)))`. -/
noncomputable def holFp64Add (mode : HolRounding) (a b : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatAdd mode (holFp64ToFloat a) (holFp64ToFloat b)).2

/-- HOL `fp64_sub`, lifted like `fp64_add`. -/
noncomputable def holFp64Sub (mode : HolRounding) (a b : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatSub mode (holFp64ToFloat a) (holFp64ToFloat b)).2

/-- HOL `fp64_mul`, lifted like `fp64_add`. -/
noncomputable def holFp64Mul (mode : HolRounding) (a b : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatMul mode (holFp64ToFloat a) (holFp64ToFloat b)).2

/-- HOL `fp64_div`, lifted like `fp64_add`. -/
noncomputable def holFp64Div (mode : HolRounding) (a b : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatDiv mode (holFp64ToFloat a) (holFp64ToFloat b)).2

/-- HOL `fp64_mul_add mode a b c = float_to_fp64 (SND (float_mul_add mode
    (fp64_to_float a) (fp64_to_float b) (fp64_to_float c)))`. -/
noncomputable def holFp64MulAdd (mode : HolRounding) (a b c : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatMulAdd mode (holFp64ToFloat a) (holFp64ToFloat b) (holFp64ToFloat c)).2

end Flapjack
