import Flapjack.Misc.MachineIeee.Arith
import Flapjack.Misc.BinaryIeeeArith.RealCarrier

/-!
# `machine_ieee` fp64 arithmetic and comparison over Mathlib reals

The generated `fp64_add`/`fp64_sub`/`fp64_mul`/`fp64_div`/`fp64_mul_add` and
`fp64_lessThan`/`fp64_lessEqual`/`fp64_greaterThan`/`fp64_greaterEqual`/
`fp64_equal` (`machine_ieeeScript.sml:16`) transcribed over the literal
Mathlib-`ℝ` `binary_ieee` operations of `Flapjack.Misc.BinaryIeeeArith.RealCarrier`,
with premise-free proofs that each executed (tagged, `Rat`-computing) operation
equals its real transcription for every rounding mode and input. Untagged
Flapjack infrastructure; no HOL-to-Lean equivalence beyond Mathlib `ℝ` as HOL
`real` is claimed.
-/

namespace Flapjack

/-- `fp64_add` over the real-carrier `float_add`. -/
noncomputable def holFp64AddR (mode : HolRounding) (a b : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatAddR mode (holFp64ToFloat a) (holFp64ToFloat b)).2

/-- `fp64_sub` over the real-carrier `float_sub`. -/
noncomputable def holFp64SubR (mode : HolRounding) (a b : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatSubR mode (holFp64ToFloat a) (holFp64ToFloat b)).2

/-- `fp64_mul` over the real-carrier `float_mul`. -/
noncomputable def holFp64MulR (mode : HolRounding) (a b : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatMulR mode (holFp64ToFloat a) (holFp64ToFloat b)).2

/-- `fp64_div` over the real-carrier `float_div`. -/
noncomputable def holFp64DivR (mode : HolRounding) (a b : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (holFloatDivR mode (holFp64ToFloat a) (holFp64ToFloat b)).2

/-- `fp64_mul_add` over the real-carrier `float_mul_add`. -/
noncomputable def holFp64MulAddR (mode : HolRounding) (a b c : BitVec 64) : BitVec 64 :=
  holFloatToFp64
    (holFloatMulAddR mode (holFp64ToFloat a) (holFp64ToFloat b) (holFp64ToFloat c)).2

theorem holFp64Add_eq_real (mode : HolRounding) (a b : BitVec 64) :
    holFp64Add mode a b = holFp64AddR mode a b := by
  unfold holFp64Add holFp64AddR; rw [holFloatAdd_eq_real]

theorem holFp64Sub_eq_real (mode : HolRounding) (a b : BitVec 64) :
    holFp64Sub mode a b = holFp64SubR mode a b := by
  unfold holFp64Sub holFp64SubR; rw [holFloatSub_eq_real]

theorem holFp64Mul_eq_real (mode : HolRounding) (a b : BitVec 64) :
    holFp64Mul mode a b = holFp64MulR mode a b := by
  unfold holFp64Mul holFp64MulR; rw [holFloatMul_eq_real]

theorem holFp64Div_eq_real (mode : HolRounding) (a b : BitVec 64) :
    holFp64Div mode a b = holFp64DivR mode a b := by
  unfold holFp64Div holFp64DivR; rw [holFloatDiv_eq_real]

theorem holFp64MulAdd_eq_real (mode : HolRounding) (a b c : BitVec 64) :
    holFp64MulAdd mode a b c = holFp64MulAddR mode a b c := by
  unfold holFp64MulAdd holFp64MulAddR; rw [holFloatMulAdd_eq_real]

/-- Every fp64 comparison observes the real-carrier `float_compare`: the
executed comparison results equal those computed from `holFloatCompareR`. -/
theorem holFp64Compare_eq_real (a b : BitVec 64) :
    holFp64LessThan a b = (holFloatCompareR (holFp64ToFloat a) (holFp64ToFloat b) == .lt) ∧
    holFp64LessEqual a b = (match holFloatCompareR (holFp64ToFloat a) (holFp64ToFloat b) with
      | .lt => true | .eq => true | _ => false) ∧
    holFp64GreaterThan a b = (holFloatCompareR (holFp64ToFloat a) (holFp64ToFloat b) == .gt) ∧
    holFp64GreaterEqual a b = (match holFloatCompareR (holFp64ToFloat a) (holFp64ToFloat b) with
      | .gt => true | .eq => true | _ => false) ∧
    holFp64Equal a b = (holFloatCompareR (holFp64ToFloat a) (holFp64ToFloat b) == .eq) := by
  simp only [holFp64LessThan, holFp64LessEqual, holFp64GreaterThan, holFp64GreaterEqual,
    holFp64Equal, holFloatLessThan, holFloatLessEqual, holFloatGreaterThan,
    holFloatGreaterEqual, holFloatEqual, holFloatCompare_eq_real]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> trivial

end Flapjack
