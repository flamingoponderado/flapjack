import Flapjack.Compiler.Backend.Semantics.WordSem.Inst
import Flapjack.Misc.MachineIeee.SqrtReal

namespace Flapjack.WordSemStateFiniteExact

/-- Flapjack consumer agreement with no separate HOL original: the actual
native instruction's sqrt clause equals the literal Mathlib-real rendering,
including missing-register failure. No successful evaluation is assumed.
HOL-to-Lean real correspondence remains SOUNDNESS item 8; this proof-only
module keeps real-analysis imports out of the compiler. -/
theorem inst_fpSqrt_real {width : Nat} [NeZero width] {C F : Type}
    (d1 d2 : Nat) (s : WordSemStateFiniteExact width C F) :
    inst (.fp (.fpSqrt d1 d2)) s =
      (getFpVar d2 s).map
        (fun f => setFpVar d1 (holFp64SqrtR .roundTiesToEven f) s) := by
  simp only [inst]
  cases getFpVar d2 s with
  | none => rfl
  | some f => simp only [Option.map_some, holFp64Sqrt_eq_holFp64SqrtR]

end Flapjack.WordSemStateFiniteExact
