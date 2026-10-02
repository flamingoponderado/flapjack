import Flapjack.Misc.MachineIeee
import Flapjack.HolRef
import Flapjack.Misc.BinaryIeeeConvert

/-!
# Cross-format machine IEEE conversions

Literal source family: `HOL/src/floating-point/machine_ieeeScript.sml:24-82`.
Finite source floats have rational values. The finite branch uses the reviewed
rational rounding rendering (SOUNDNESS item 8); this does not establish HOL-to-Lean
real-number equivalence. The NaN branch retains arbitrary NaN choice, including
signalling output NaNs, rather than using `float_some_qnan`.

Source/carrier review is tracked on bead flapjack-pxn.18.5.13.8.2.7.1.
Full family acceptance remains open pending the complete gates and coordinator review.
-/

namespace Flapjack

/-- Fixed binary32 codec, from machine_ieeeLib's 1/8/23 field extraction. -/
@[hol "HOL/src/floating-point/machine_ieeeScript.sml" "fp32_to_float_def" 15]
def holFp32ToFloat (a : BitVec 32) : HolFloat 23 8 :=
  { sign := a.extractLsb' 31 1, exponent := a.extractLsb' 23 8,
    significand := a.extractLsb' 0 23 }

/-- Fixed binary32 codec, preserving sign/exponent/significand concatenation. -/
@[hol "HOL/src/floating-point/machine_ieeeScript.sml" "float_to_fp32_def" 15]
def holFloatToFp32 (a : HolFloat 23 8) : BitVec 32 :=
  (a.sign ++ a.exponent ++ a.significand).cast (by decide)

/-- Full `convert_def` branches, with its independently typed input/output
codecs and supplied finite-real/flags converter. The arbitrary choice is exactly
`@fp. float_is_nan fp`; imposing a quiet-NaN condition would change the source. -/
@[hol "HOL/src/floating-point/machine_ieeeScript.sml" "convert_def" (reals_as_rational_cuts) (words_as_type_indexed_bitvec)]
noncomputable def holMachineConvert {a : Nat} {b : Nat} {c : Nat} {d : Nat} {e : Nat} {f : Nat}
    [NeZero a] [NeZero b] [NeZero c] [NeZero d] [NeZero e] [NeZero f]
    (toFloat : BitVec a → HolFloat b c)
    (fromFloat : HolFloat d e → BitVec f)
    (fromRealWithFlags : HolRounding → Rat → HolFloatFlags × BitVec f)
    (mode : HolRounding) (word : BitVec a) : HolFloatFlags × BitVec f :=
  let x := toFloat word
  match holFloatValue x with
  | .float r => fromRealWithFlags mode r
  | .nan => (holCheckForSignalling [x],
      fromFloat (Classical.epsilon (fun y => holFloatIsNan y = true)))
  | .infinity => (holClearFlags,
      fromFloat (if x.sign = 0 then holFloatPlusInfinity d e
                 else holFloatMinusInfinity d e))

/-- Fixed binary32 real conversion with the literal mode-dependent zero sign
and all six original flag fields; no flags are discarded in this helper. -/
@[hol "HOL/src/floating-point/machine_ieeeScript.sml" "real_to_fp32_with_flags_def" 15 (reals_as_rational_cuts)]
noncomputable def holRealToFp32WithFlags (mode : HolRounding) (r : Rat) :
    HolFloatFlags × BitVec 32 :=
  let result : HolFloatFlags × HolFloat 23 8 :=
    holFloatRoundWithFlags mode (decide (mode = .roundTowardNegative)) r
  (result.1, holFloatToFp32 result.2)

/-- Fixed binary64 version of the same original generated encoding wrapper. -/
@[hol "HOL/src/floating-point/machine_ieeeScript.sml" "real_to_fp64_with_flags_def" 16 (reals_as_rational_cuts)]
noncomputable def holRealToFp64WithFlags (mode : HolRounding) (r : Rat) :
    HolFloatFlags × BitVec 64 :=
  let result : HolFloatFlags × HolFloat 52 11 :=
    holFloatRoundWithFlags mode (decide (mode = .roundTowardNegative)) r
  (result.1, holFloatToFp64 result.2)

/-- Full original widening converter; rounding is ties-to-even independently
of the instruction's accepted static or dynamic mode. -/
@[hol "HOL/src/floating-point/machine_ieeeScript.sml" "fp32_to_fp64_with_flags_def" (reals_as_rational_cuts)]
noncomputable def holFp32ToFp64WithFlags (word : BitVec 32) :
    HolFloatFlags × BitVec 64 :=
  holMachineConvert holFp32ToFloat holFloatToFp64 holRealToFp64WithFlags
    .roundTiesToEven word

/-- Full original narrowing converter; retains the requested rounding mode. -/
@[hol "HOL/src/floating-point/machine_ieeeScript.sml" "fp64_to_fp32_with_flags_def" (reals_as_rational_cuts)]
noncomputable def holFp64ToFp32WithFlags (mode : HolRounding) (word : BitVec 64) :
    HolFloatFlags × BitVec 32 :=
  holMachineConvert holFp64ToFloat holFloatToFp32 holRealToFp32WithFlags mode word

/-- Original SND wrapper, discarding flags only at this explicit boundary. -/
@[hol "HOL/src/floating-point/machine_ieeeScript.sml" "fp32_to_fp64_def" (reals_as_rational_cuts)]
noncomputable def holFp32ToFp64 (word : BitVec 32) : BitVec 64 :=
  (holFp32ToFp64WithFlags word).2

/-- Original mode-dependent SND wrapper. -/
@[hol "HOL/src/floating-point/machine_ieeeScript.sml" "fp64_to_fp32_def" (reals_as_rational_cuts)]
noncomputable def holFp64ToFp32 (mode : HolRounding) (word : BitVec 64) : BitVec 32 :=
  (holFp64ToFp32WithFlags mode word).2

end Flapjack
