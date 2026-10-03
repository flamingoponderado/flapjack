import Flapjack.Misc.BinaryIeeeSqrtFp64
import Flapjack.Misc.BinaryIeeeArithExec

/-!
# Computable binary64 square root with a canonical quiet NaN

Flapjack-specific executable producer with no HOL declaration of its own. It
follows the reviewed roundTiesToEven `float_sqrt` branch structure
(`holFloatSqrtRte64`), replacing only HOL's unspecified quiet-NaN choice
(`float_some_qnan`) by the concrete `defaultQuietNanFloat`. The unconditional
refinement theorem relates the whole result to the original rendering, with
bit equality in every non-choice branch. Like the arithmetic producers in
`BinaryIeeeArithExec`, it retains the SOUNDNESS item 8 real-sqrt rendering
assumption and does not claim a cross-assistant equivalence theorem.
-/
namespace Flapjack

/-- Executable `float_sqrt roundTiesToEven` at binary64 with the canonical
choice NaN. -/
def execFloatSqrtRte64 (x : HolFloat 52 11) : HolFloat 52 11 :=
  if x.sign = 0 then
    match holFloatValue x with
    | .nan => defaultQuietNanFloat
    | .infinity => holFloatPlusInfinity 52 11
    | .float r => holFp64SqrtRoundRte false r
  else if x = holFloatMinusZero 52 11 then holFloatMinusZero 52 11
  else defaultQuietNanFloat

/-- Whole-result refinement for arbitrary inputs; no NaN or success premise. -/
theorem holFloatSqrtRte64_refines_exec (x : HolFloat 52 11) :
    holFloatRefines (holFloatSqrtRte64 x) (execFloatSqrtRte64 x) := by
  unfold holFloatSqrtRte64 execFloatSqrtRte64
  by_cases hs : x.sign = 0
  · rw [if_pos hs, if_pos hs]
    cases holFloatValue x with
    | nan => exact holFloatSomeQnan_refines_defaultQuietNanFloat _
    | infinity => exact Or.inl rfl
    | float r => exact Or.inl rfl
  · rw [if_neg hs, if_neg hs]
    by_cases hz : x = holFloatMinusZero 52 11
    · rw [if_pos hz, if_pos hz]; exact Or.inl rfl
    · rw [if_neg hz, if_neg hz]; exact holFloatSomeQnan_refines_defaultQuietNanFloat _

/-- Executable binary64 square root at WordSem's roundTiesToEven mode.
WordSem observes only the output word, not IEEE flags. -/
def execFp64Sqrt (a : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (execFloatSqrtRte64 (holFp64ToFloat a))

/-- Full arbitrary-input word refinement to the rendered `fp64_sqrt
roundTiesToEven`. -/
theorem holFp64Sqrt_refines_exec (a : BitVec 64) :
    fp64Refines (holFp64Sqrt .roundTiesToEven a) (execFp64Sqrt a) := by
  rw [holFp64Sqrt_rte]
  exact holFloatRefines_to_fp64 (holFloatSqrtRte64_refines_exec _)

end Flapjack
