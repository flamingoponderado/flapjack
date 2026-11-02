import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBasic

/-! Facts connecting the factored Boolean decoder to the original closure
primitive tests. These helper theorems have no separate HOL declaration. -/
namespace Flapjack.Compiler.Backend.ClosSem

/-- A value decodes as a Boolean exactly when it is the corresponding
closure-language Boolean block. -/
theorem asBool_eq_some (value : Value) (flag : Bool) :
    asBool value = some flag ↔ value = boolValue flag := by
  cases value with
  | block tag fields =>
    cases tag with
    | zero => cases fields <;> cases flag <;> simp [asBool, boolValue, BackendCommon.trueTag, BackendCommon.falseTag]
    | succ tag =>
      cases tag <;> cases fields <;> cases flag <;>
        simp [asBool, boolValue, BackendCommon.trueTag, BackendCommon.falseTag]
  | number _ | word64 _ | byteVector _ | refPtr _ _ | closure _ _ _ _ _ | recclosure _ _ _ _ _ =>
    cases flag <;> simp [asBool, boolValue]

end Flapjack.Compiler.Backend.ClosSem
