module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBasic

@[expose] public section

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

open Classical in
/-- Decoding a condition chooses exactly the same branch as HOL's two
successive Boolean-value equality checks. -/
theorem asBool_cases {α : Type} (value : Value) (yes no invalid : α) :
    (match asBool value with
      | some true => yes
      | some false => no
      | none => invalid) =
    (if value = boolValue true then yes else if value = boolValue false then no else invalid) := by
  classical
  by_cases isTrue : value = boolValue true
  · subst value
    simp [asBool, boolValue, BackendCommon.trueTag]
  · by_cases isFalse : value = boolValue false
    · subst value
      simp [asBool, boolValue, BackendCommon.trueTag, BackendCommon.falseTag]
    · have decoded : asBool value = none := by
        cases result : asBool value with
        | none => rfl
        | some flag =>
          cases flag with
          | false => exact False.elim (isFalse ((asBool_eq_some value false).mp result))
          | true => exact False.elim (isTrue ((asBool_eq_some value true).mp result))
      simp [decoded, isTrue, isFalse]

end Flapjack.Compiler.Backend.ClosSem
