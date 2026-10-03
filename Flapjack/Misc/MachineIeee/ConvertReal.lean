import Flapjack.Misc.MachineIeee.Convert
import Flapjack.Misc.BinaryIeeeSqrt.RealCarrier

/-!
# Arbitrary-real machine IEEE conversion wrappers

HOL `convert_def` and the generated `real_to_fp64`, `real_to_fp32_with_flags`
and `real_to_fp64_with_flags` (`HOL/src/floating-point/machine_ieeeScript.sml`)
take HOL `real` arguments.  `Flapjack.Misc.MachineIeee.Convert` renders them
over `Rat` for the executed cross-format conversions, which restricts HOL's
arbitrary-real domain, so those renderings are untagged.  This module gives
the tagged ports over Mathlib `ℝ`, built from the arbitrary-real
`binary_ieee` ports of `Flapjack.Misc.BinaryIeeeSqrt.RealCarrier`, and proves
that the executed `Rat` wrappers and the tagged cross-format converters agree
with them, for every mode and input, with no premise.  No HOL-to-Lean
equivalence is assumed or established.
-/

namespace Flapjack

open Classical

/-- HOL `convert_def` (`machine_ieeeScript.sml:24-36`) over `ℝ`: the finite
branch passes the float's real value to the supplied real/flags converter; the
NaN branch is `(check_for_signalling [f], from_float (@fp. float_is_nan fp))`;
an infinity keeps its sign with `clear_flags`. -/
@[hol "HOL/src/floating-point/machine_ieeeScript.sml" "convert_def"
  (reals_as_rational_cuts) (words_as_type_indexed_bitvec)]
noncomputable def holMachineConvertR {a : Nat} {b : Nat} {c : Nat} {d : Nat} {e : Nat} {f : Nat}
    [NeZero a] [NeZero b] [NeZero c] [NeZero d] [NeZero e] [NeZero f]
    (toFloat : BitVec a → HolFloat b c)
    (fromFloat : HolFloat d e → BitVec f)
    (fromRealWithFlags : HolRounding → ℝ → HolFloatFlags × BitVec f)
    (mode : HolRounding) (word : BitVec a) : HolFloatFlags × BitVec f :=
  let x := toFloat word
  match holFloatValueR x with
  | .float r => fromRealWithFlags mode r
  | .nan => (holCheckForSignalling [x],
      fromFloat (Classical.epsilon (fun y => holFloatIsNan y = true)))
  | .infinity => (holClearFlags,
      fromFloat (if x.sign = 0 then holFloatPlusInfinity d e
                 else holFloatMinusInfinity d e))

/-- Generated HOL `real_to_fp32_with_flags` at the 23/8/32 encoding
(`machine_ieeeScript.sml:15`): `real_to_float_with_flags` at binary32, with the
float encoded by `float_to_fp32` and all six flags kept, for an arbitrary real. -/
@[hol "HOL/src/floating-point/machine_ieeeScript.sml" "real_to_fp32_with_flags_def" 15
  (reals_as_rational_cuts)]
noncomputable def holRealToFp32WithFlagsR (mode : HolRounding) (r : ℝ) :
    HolFloatFlags × BitVec 32 :=
  let result : HolFloatFlags × HolFloat 23 8 := holRealToFloatWithFlagsR mode r
  (result.1, holFloatToFp32 result.2)

/-- Generated HOL `real_to_fp64_with_flags` at the 52/11/64 encoding
(`machine_ieeeScript.sml:16`), for an arbitrary real. -/
@[hol "HOL/src/floating-point/machine_ieeeScript.sml" "real_to_fp64_with_flags_def" 16
  (reals_as_rational_cuts)]
noncomputable def holRealToFp64WithFlagsR (mode : HolRounding) (r : ℝ) :
    HolFloatFlags × BitVec 64 :=
  let result : HolFloatFlags × HolFloat 52 11 := holRealToFloatWithFlagsR mode r
  (result.1, holFloatToFp64 result.2)

/-- Generated HOL `real_to_fp64 mode = float_to_fp64 o real_to_float mode`
(`machine_ieeeScript.sml:16`), applied to an arbitrary real. The executed
`holRealToFp64` is its restriction to rationals (`holRealToFp64R_ratCast`). -/
@[hol "HOL/src/floating-point/machine_ieeeScript.sml" "real_to_fp64_def" 16
  (reals_as_rational_cuts)]
noncomputable def holRealToFp64R (mode : HolRounding) (r : ℝ) : BitVec 64 :=
  holFloatToFp64 (holRealToFloatR mode r)

theorem holRealToFp64R_ratCast (mode : HolRounding) (q : Rat) :
    holRealToFp64R mode (q : ℝ) = holRealToFp64 mode q := by
  unfold holRealToFp64R holRealToFp64
  rw [holRealToFloatR_ratCast]

/-- HOL `int_to_fp64 mode a = real_to_fp64 mode (real_of_int a)` holds for the
executed `holIntToFp64` with the arbitrary-real `real_to_fp64`, for every mode
and integer (no premise). -/
theorem holIntToFp64_eq_real (mode : HolRounding) (a : Int) :
    holIntToFp64 mode a = holRealToFp64R mode (a : ℝ) := by
  unfold holIntToFp64
  rw [← holRealToFp64R_ratCast]
  norm_cast

theorem holRealToFp32WithFlagsR_ratCast (mode : HolRounding) (q : Rat) :
    holRealToFp32WithFlagsR mode (q : ℝ) = holRealToFp32WithFlags mode q := by
  unfold holRealToFp32WithFlagsR holRealToFp32WithFlags
  rw [holRealToFloatWithFlagsR_ratCast]

theorem holRealToFp64WithFlagsR_ratCast (mode : HolRounding) (q : Rat) :
    holRealToFp64WithFlagsR mode (q : ℝ) = holRealToFp64WithFlags mode q := by
  unfold holRealToFp64WithFlagsR holRealToFp64WithFlags
  rw [holRealToFloatWithFlagsR_ratCast]

/-- The `Rat` convert equals the real convert whenever the supplied converters
agree at rationals, which is the only place `convert` evaluates them. -/
theorem holMachineConvert_eq_holMachineConvertR {a : Nat} {b : Nat} {c : Nat} {d : Nat} {e : Nat}
    {f : Nat} [NeZero a] [NeZero b] [NeZero c] [NeZero d] [NeZero e] [NeZero f]
    (toFloat : BitVec a → HolFloat b c) (fromFloat : HolFloat d e → BitVec f)
    (fromRealWithFlags : HolRounding → Rat → HolFloatFlags × BitVec f)
    (fromRealWithFlagsR : HolRounding → ℝ → HolFloatFlags × BitVec f)
    (hagree : ∀ m (q : Rat), fromRealWithFlagsR m (q : ℝ) = fromRealWithFlags m q)
    (mode : HolRounding) (word : BitVec a) :
    holMachineConvert toFloat fromFloat fromRealWithFlags mode word =
      holMachineConvertR toFloat fromFloat fromRealWithFlagsR mode word := by
  unfold holMachineConvert holMachineConvertR
  simp only [holFloatValueR_eq]
  cases holFloatValue (toFloat word) <;> simp [hagree]

/-- The tagged widening converter is the real-carrier `convert` with the
arbitrary-real `real_to_fp64_with_flags`, for every input (no premise). -/
theorem holFp32ToFp64WithFlags_eq_real (word : BitVec 32) :
    holFp32ToFp64WithFlags word =
      holMachineConvertR holFp32ToFloat holFloatToFp64 holRealToFp64WithFlagsR
        .roundTiesToEven word :=
  holMachineConvert_eq_holMachineConvertR _ _ _ _
    (fun m q => holRealToFp64WithFlagsR_ratCast m q) _ _

/-- The tagged narrowing converter is the real-carrier `convert` with the
arbitrary-real `real_to_fp32_with_flags`, for every mode and input. -/
theorem holFp64ToFp32WithFlags_eq_real (mode : HolRounding) (word : BitVec 64) :
    holFp64ToFp32WithFlags mode word =
      holMachineConvertR holFp64ToFloat holFloatToFp32 holRealToFp32WithFlagsR mode word :=
  holMachineConvert_eq_holMachineConvertR _ _ _ _
    (fun m q => holRealToFp32WithFlagsR_ratCast m q) _ _

end Flapjack
