import Flapjack.Compiler.Backend.Semantics.FlatSem.Apply

/-! Source-shaped equality and comparison cases of flat application. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Eight-bit shifts accept exactly one eight-bit word literal. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_shift8_source {C F : Type} (s : State C F) (shift : Shift) (n : Nat)
    (vs : List Value) :
    doApp s (.src (.shift .w8 shift n)) vs = match vs with
      | [.litv (.word8 w)] => some (s, .val (.litv (.word8 (shift8Lookup shift w n))))
      | _ => none := by
  cases vs with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil =>
      cases x <;> simp [doApp, doAppNumeric, applyNumericProjection,
        SemanticPrimitivesHOL.doApp, doAppNumericCore, doAppBasic, flatToValue, valueToFlat]
      all_goals split <;> simp_all
      all_goals repeat' first | split at * | simp_all [SemanticPrimitivesHOL.boolValue]
    | cons y ys =>
      cases x <;> simp [doApp, doAppNumeric, applyNumericProjection,
        SemanticPrimitivesHOL.doApp, doAppNumericCore, doAppBasic, flatToValue]
      all_goals repeat' first | split at * | simp_all [SemanticPrimitivesHOL.boolValue]

/-- Sixty-four-bit shifts accept exactly one sixty-four-bit word literal. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_shift64_source {C F : Type} (s : State C F) (shift : Shift) (n : Nat)
    (vs : List Value) :
    doApp s (.src (.shift .w64 shift n)) vs = match vs with
      | [.litv (.word64 w)] => some (s, .val (.litv (.word64 (shift64Lookup shift w n))))
      | _ => none := by
  cases vs with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil =>
      cases x <;> simp [doApp, doAppNumeric, applyNumericProjection,
        SemanticPrimitivesHOL.doApp, doAppNumericCore, doAppBasic, flatToValue, valueToFlat]
      all_goals split <;> simp_all
      all_goals repeat' first | split at * | simp_all [SemanticPrimitivesHOL.boolValue]
    | cons y ys =>
      cases x <;> simp [doApp, doAppNumeric, applyNumericProjection,
        SemanticPrimitivesHOL.doApp, doAppNumericCore, doAppBasic, flatToValue]
      all_goals repeat' first | split at * | simp_all [SemanticPrimitivesHOL.boolValue]

/-- Equality accepts exactly two values and propagates comparison type errors. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_equality_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .equality) vs = match vs with
      | [x, y] => match doEq x y with
        | .typeError => none
        | .val b => some (s, .val (boolValue b))
      | _ => none := by
  rfl

/-- Typed tests accept exactly two values and propagate comparison type errors. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_test_source {C F : Type} (s : State C F) (test : Test) (typ : PrimType)
    (vs : List Value) :
    doApp s (.src (.test test typ)) vs = match vs with
      | [x, y] => match doTest test typ x y with
        | .typeError => none
        | .val b => some (s, .val (boolValue b))
      | _ => none := by
  rfl

end Flapjack.Compiler.Backend.FlatSem
