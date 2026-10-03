import Flapjack.FpSemHOL
import Flapjack.Misc.MachineIeee.SqrtReal

namespace Flapjack

/-- Flapjack consumer agreement with no separate HOL original: the actual
unary evaluator's sqrt clause equals the literal Mathlib-real rendering on
all binary64 inputs. HOL-to-Lean real correspondence remains SOUNDNESS item 8.
This proof-only module keeps real-analysis imports out of the compiler. -/
theorem fpSemFpUopComp_sqrt_real (w : BitVec 64) :
    fpSemFpUopComp .sqrt w = holFp64SqrtR .roundTiesToEven w :=
  holFp64Sqrt_eq_holFp64SqrtR .roundTiesToEven w

end Flapjack
