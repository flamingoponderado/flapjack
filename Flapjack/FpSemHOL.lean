import Flapjack.HolRef
import Flapjack.Misc.BinaryIeeeArith

/-!
# CakeML `fpSem` operations used by wordSem

Lean counterpart of `cakeml/semantics/fpSemScript.sml` (bead
`flapjack-h29l.6.2.2`).  Only `fpfma_def` is ported so far.  It is the
fused multiply-add used by wordSem `inst_def`'s `FPFma` case, over the
rendered HOL `machine_ieee` `fp64_mul_add` (`Flapjack.Misc.BinaryIeeeArith`).
-/

namespace Flapjack

/-- Exact HOL `fpfma_def` (`fpSemScript.sml:60-62`):
    `fpfma v1 v2 v3 = fp64_mul_add roundTiesToEven v2 v3 v1`, so the first
    argument is the addend.  HOL `word64` is `BitVec 64`. -/
@[hol "cakeml/semantics/fpSemScript.sml" "fpfma_def"]
noncomputable def fpSemFpfma (v1 v2 v3 : BitVec 64) : BitVec 64 :=
  holFp64MulAdd .roundTiesToEven v2 v3 v1

end Flapjack
