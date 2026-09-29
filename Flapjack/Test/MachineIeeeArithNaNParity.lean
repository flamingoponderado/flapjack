import Flapjack.Misc.BinaryIeeeArithFp64

/-!
The probe fixture (`scripts/hol-probes/machine_ieee_fp64_arith_nan_probe.out`)
records exact HOL EVAL results for five qNaN-input and seven invalid-operation
branches from `binary_ieeeScript.sml:587-722`. The outputs retain a symbolic
`float_some_qnan`; the same fixture includes a HOL kernel theorem from
`some_nan_properties` proving every such value is NaN and non-signalling.
The Lean theorems below kernel-check the 12 classifications against the exact
fp64 operation through the value-refinement lemmas and the qNaN specification.
No payload or IEEE flags are claimed.
-/

namespace Flapjack.Test.MachineIeeeArithNaNParity

open Flapjack

private def one : BitVec 64 := 0x3FF0000000000000
private def pz : BitVec 64 := 0x0
private def pinf : BitVec 64 := 0x7FF0000000000000
private def ninf : BitVec 64 := 0xFFF0000000000000
private def qnan : BitVec 64 := 0x7FF8000000000000

private def nanClass (f : HolFloat 52 11) : Bool × Bool :=
  (holFloatIsNan f, holFloatIsSignalling f)

private def fp64NanClass (w : BitVec 64) : Bool × Bool :=
  nanClass (holFp64ToFloat w)

private theorem fp64DecodeEncode (f : HolFloat 52 11) :
    holFp64ToFloat (holFloatToFp64 f) = f := by
  cases f with
  | mk sign exponent significand =>
    dsimp [holFp64ToFloat, holFloatToFp64]
    congr 1
    · calc
        BitVec.extractLsb' 63 1 ((sign ++ exponent) ++ significand) =
            BitVec.extractLsb' 11 1 (sign ++ exponent) :=
          BitVec.extractLsb'_append_eq_of_le (by decide)
        _ = sign := BitVec.extractLsb'_append_eq_left
    · calc
        BitVec.extractLsb' 52 11 ((sign ++ exponent) ++ significand) =
            BitVec.extractLsb' 0 11 (sign ++ exponent) :=
          BitVec.extractLsb'_append_eq_of_le (by decide)
        _ = exponent := BitVec.extractLsb'_append_eq_right
    · exact BitVec.extractLsb'_append_eq_right

private theorem someQnanClass (op : HolFpOp 52 11) :
    nanClass (holFloatSomeQnan op) = (true, false) := by
  rcases holFloatSomeQnan_spec op with ⟨hn, hs⟩
  simp [nanClass, hn, hs]

private theorem qnanValue : holFloatValue (holFp64ToFloat qnan) = .nan := by
  decide +kernel

private theorem oneValue : holFloatValue (holFp64ToFloat one) = .float 1 := by
  decide +kernel

private theorem pzValue : holFloatValue (holFp64ToFloat pz) = .float 0 := by
  decide +kernel

private theorem pzSign : (holFp64ToFloat pz).sign = 0 := by
  decide +kernel

private theorem pinfValue : holFloatValue (holFp64ToFloat pinf) = .infinity := by
  decide +kernel

private theorem ninfValue : holFloatValue (holFp64ToFloat ninf) = .infinity := by
  decide +kernel

private theorem pinfSign : (holFp64ToFloat pinf).sign = 0 := by
  decide +kernel

private theorem ninfSign : (holFp64ToFloat ninf).sign = 1 := by
  decide +kernel

private theorem oneSign : (holFp64ToFloat one).sign = 0 := by
  decide +kernel

private theorem addNaNInputFloat :
    nanClass (holFloatAddRte64 (holFp64ToFloat qnan) (holFp64ToFloat one)) = (true, false) := by
  unfold holFloatAddRte64
  rw [qnanValue]
  exact someQnanClass _

private theorem subNaNInputFloat :
    nanClass (holFloatSubRte64 (holFp64ToFloat qnan) (holFp64ToFloat one)) = (true, false) := by
  unfold holFloatSubRte64
  rw [qnanValue]
  exact someQnanClass _

private theorem mulNaNInputFloat :
    nanClass (holFloatMulRte64 (holFp64ToFloat qnan) (holFp64ToFloat one)) = (true, false) := by
  unfold holFloatMulRte64
  rw [qnanValue]
  exact someQnanClass _

private theorem divNaNInputFloat :
    nanClass (holFloatDivRte64 (holFp64ToFloat qnan) (holFp64ToFloat one)) = (true, false) := by
  unfold holFloatDivRte64
  rw [qnanValue]
  exact someQnanClass _

private theorem mulAddNaNInputFloat :
    nanClass (holFloatMulAddRte64 (holFp64ToFloat one) (holFp64ToFloat one)
      (holFp64ToFloat qnan)) = (true, false) := by
  unfold holFloatMulAddRte64
  simp only [holFloatIsNan, qnanValue, Bool.or_true, if_true]
  exact someQnanClass _

private theorem addInvalidInfinitiesFloat :
    nanClass (holFloatAddRte64 (holFp64ToFloat pinf) (holFp64ToFloat ninf)) =
      (true, false) := by
  unfold holFloatAddRte64
  rw [pinfValue, ninfValue]
  rw [pinfSign, ninfSign]
  exact someQnanClass _

private theorem subInvalidInfinitiesFloat :
    nanClass (holFloatSubRte64 (holFp64ToFloat pinf) (holFp64ToFloat pinf)) =
      (true, false) := by
  simp [holFloatSubRte64, pinfValue, pinfSign, someQnanClass]

private theorem mulInvalidInfinityZeroFloat :
    nanClass (holFloatMulRte64 (holFp64ToFloat pinf) (holFp64ToFloat pz)) =
      (true, false) := by
  simp [holFloatMulRte64, pinfValue, pzValue, someQnanClass]

private theorem divInvalidZeroZeroFloat :
    nanClass (holFloatDivRte64 (holFp64ToFloat pz) (holFp64ToFloat pz)) =
      (true, false) := by
  simp [holFloatDivRte64, pzValue, someQnanClass]

private theorem divInvalidInfinityInfinityFloat :
    nanClass (holFloatDivRte64 (holFp64ToFloat pinf) (holFp64ToFloat ninf)) =
      (true, false) := by
  simp [holFloatDivRte64, pinfValue, ninfValue, someQnanClass]

private theorem mulAddInvalidInfinityZeroFloat :
    nanClass (holFloatMulAddRte64 (holFp64ToFloat pinf) (holFp64ToFloat pz)
      (holFp64ToFloat one)) = (true, false) := by
  simp [holFloatMulAddRte64, holFloatIsInfinite, holFloatIsZero,
    pinfValue, pzValue, oneValue, pinfSign, pzSign, oneSign, someQnanClass]

private theorem mulAddInvalidOpposedInfinitiesFloat :
    nanClass (holFloatMulAddRte64 (holFp64ToFloat pinf) (holFp64ToFloat one)
      (holFp64ToFloat ninf)) = (true, false) := by
  simp [holFloatMulAddRte64, holFloatIsInfinite, holFloatIsZero,
    pinfValue, oneValue, ninfValue, pinfSign, oneSign, ninfSign,
    someQnanClass]

theorem addQnanInput : fp64NanClass (holFp64Add .roundTiesToEven qnan one) = (true, false) := by
  rw [holFp64Add_rte]
  unfold fp64NanClass
  rw [fp64DecodeEncode]
  exact addNaNInputFloat

theorem subQnanInput : fp64NanClass (holFp64Sub .roundTiesToEven qnan one) = (true, false) := by
  rw [holFp64Sub_rte]
  unfold fp64NanClass
  rw [fp64DecodeEncode]
  exact subNaNInputFloat

theorem mulQnanInput : fp64NanClass (holFp64Mul .roundTiesToEven qnan one) = (true, false) := by
  rw [holFp64Mul_rte]
  unfold fp64NanClass
  rw [fp64DecodeEncode]
  exact mulNaNInputFloat

theorem divQnanInput : fp64NanClass (holFp64Div .roundTiesToEven qnan one) = (true, false) := by
  rw [holFp64Div_rte]
  unfold fp64NanClass
  rw [fp64DecodeEncode]
  exact divNaNInputFloat

theorem mulAddQnanInput :
    fp64NanClass (holFp64MulAdd .roundTiesToEven one one qnan) = (true, false) := by
  unfold holFp64MulAdd
  rw [holFloatMulAdd_rte64]
  unfold fp64NanClass
  rw [fp64DecodeEncode]
  exact mulAddNaNInputFloat

theorem addInvalidInfinities :
    fp64NanClass (holFp64Add .roundTiesToEven pinf ninf) = (true, false) := by
  rw [holFp64Add_rte]
  unfold fp64NanClass
  rw [fp64DecodeEncode]
  exact addInvalidInfinitiesFloat

theorem subInvalidInfinities :
    fp64NanClass (holFp64Sub .roundTiesToEven pinf pinf) = (true, false) := by
  rw [holFp64Sub_rte]
  unfold fp64NanClass
  rw [fp64DecodeEncode]
  exact subInvalidInfinitiesFloat

theorem mulInvalidInfinityZero :
    fp64NanClass (holFp64Mul .roundTiesToEven pinf pz) = (true, false) := by
  rw [holFp64Mul_rte]
  unfold fp64NanClass
  rw [fp64DecodeEncode]
  exact mulInvalidInfinityZeroFloat

theorem divInvalidZeroZero :
    fp64NanClass (holFp64Div .roundTiesToEven pz pz) = (true, false) := by
  rw [holFp64Div_rte]
  unfold fp64NanClass
  rw [fp64DecodeEncode]
  exact divInvalidZeroZeroFloat

theorem divInvalidInfinityInfinity :
    fp64NanClass (holFp64Div .roundTiesToEven pinf ninf) = (true, false) := by
  rw [holFp64Div_rte]
  unfold fp64NanClass
  rw [fp64DecodeEncode]
  exact divInvalidInfinityInfinityFloat

theorem mulAddInvalidInfinityZero :
    fp64NanClass (holFp64MulAdd .roundTiesToEven pinf pz one) = (true, false) := by
  unfold holFp64MulAdd
  rw [holFloatMulAdd_rte64]
  unfold fp64NanClass
  rw [fp64DecodeEncode]
  exact mulAddInvalidInfinityZeroFloat

theorem mulAddInvalidOpposedInfinities :
    fp64NanClass (holFp64MulAdd .roundTiesToEven pinf one ninf) = (true, false) := by
  unfold holFp64MulAdd
  rw [holFloatMulAdd_rte64]
  unfold fp64NanClass
  rw [fp64DecodeEncode]
  exact mulAddInvalidOpposedInfinitiesFloat

theorem allNaNObservations :
    fp64NanClass (holFp64Add .roundTiesToEven qnan one) = (true, false) ∧
    fp64NanClass (holFp64Sub .roundTiesToEven qnan one) = (true, false) ∧
    fp64NanClass (holFp64Mul .roundTiesToEven qnan one) = (true, false) ∧
    fp64NanClass (holFp64Div .roundTiesToEven qnan one) = (true, false) ∧
    fp64NanClass (holFp64MulAdd .roundTiesToEven one one qnan) = (true, false) ∧
    fp64NanClass (holFp64Add .roundTiesToEven pinf ninf) = (true, false) ∧
    fp64NanClass (holFp64Sub .roundTiesToEven pinf pinf) = (true, false) ∧
    fp64NanClass (holFp64Mul .roundTiesToEven pinf pz) = (true, false) ∧
    fp64NanClass (holFp64Div .roundTiesToEven pz pz) = (true, false) ∧
    fp64NanClass (holFp64Div .roundTiesToEven pinf ninf) = (true, false) ∧
    fp64NanClass (holFp64MulAdd .roundTiesToEven pinf pz one) = (true, false) ∧
    fp64NanClass (holFp64MulAdd .roundTiesToEven pinf one ninf) = (true, false) := by
  exact ⟨addQnanInput, subQnanInput, mulQnanInput, divQnanInput, mulAddQnanInput,
    addInvalidInfinities, subInvalidInfinities, mulInvalidInfinityZero,
    divInvalidZeroZero, divInvalidInfinityInfinity, mulAddInvalidInfinityZero,
    mulAddInvalidOpposedInfinities⟩

def runChecks : IO Bool := do
  let _checkedRows := allNaNObservations
  IO.println "PASS 12 kernel-checked fp64 NaN/invalid-operation classifications"
  pure true

end Flapjack.Test.MachineIeeeArithNaNParity
