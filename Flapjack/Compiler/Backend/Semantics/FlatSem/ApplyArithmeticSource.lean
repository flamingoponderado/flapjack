import Flapjack.Compiler.Backend.Semantics.FlatSem.Apply
import Flapjack.SemanticPrimitivesProps.Arithmetic

/-! Source-shaped numeric application cases for the flat evaluator. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Basis.Pure.MlString

/-- Integer arithmetic dispatches on the source projections of its operands. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_arithInt_source {C F : Type} (s : State C F)
    (op : Arith) (vs : List Value) :
    doApp s (.src (.arith op .intT)) vs =
      match vs.map flatToValue with
      | [.litv (.intLit x), .litv (.intLit y)] =>
        match op with
        | .add => some (s, .val (.litv (.intLit (x + y))))
        | .sub => some (s, .val (.litv (.intLit (x - y))))
        | .mul => some (s, .val (.litv (.intLit (x * y))))
        | .div => if y = 0 then some (s, .err (.raise divExnV))
            else some (s, .val (.litv (.intLit (x.fdiv y))))
        | .mod => if y = 0 then some (s, .err (.raise divExnV))
            else some (s, .val (.litv (.intLit (x.fmod y))))
        | _ => none
      | _ => none := by
  cases op <;> simp [doApp, doAppNumeric, applyNumericProjection,
    SemanticPrimitivesHOL.doApp_arith_core, doAppNumericCore]
  all_goals repeat' first | split at * | simp_all [valueToFlat]

/-- Eight-bit arithmetic checks both projected operands before applying the
word operation; unsupported operators fail. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_arithWord8_source {C F : Type} (s : State C F)
    (op : Arith) (vs : List Value) :
    doApp s (.src (.arith op (.wordT .w8))) vs =
      match vs.map flatToValue with
      | [.litv (.word8 x), .litv (.word8 y)] =>
        (wordArith op x y).map fun result => (s, .val (.litv (.word8 result)))
      | _ => none := by
  cases op <;> simp [doApp, doAppNumeric, applyNumericProjection,
    SemanticPrimitivesHOL.doApp_arith_core, doAppNumericCore, wordArith]
  all_goals repeat' first | split at * | simp_all [valueToFlat]

/-- Sixty-four-bit arithmetic checks both projected operands before applying
the word operation; unsupported operators fail. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_arithWord64_source {C F : Type} (s : State C F)
    (op : Arith) (vs : List Value) :
    doApp s (.src (.arith op (.wordT .w64))) vs =
      match vs.map flatToValue with
      | [.litv (.word64 x), .litv (.word64 y)] =>
        (wordArith op x y).map fun result => (s, .val (.litv (.word64 result)))
      | _ => none := by
  cases op <;> simp [doApp, doAppNumeric, applyNumericProjection,
    SemanticPrimitivesHOL.doApp_arith_core, doAppNumericCore, wordArith]
  all_goals repeat' first | split at * | simp_all [valueToFlat]

/-- Floating arithmetic checks operand types and arities before applying the
binary64 operation. The floating model inherits its rational-cut assumption. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_arithFloat64_source {C F : Type} (s : State C F)
    (op : Arith) (vs : List Value) :
    doApp s (.src (.arith op .float64T)) vs =
      match op, vs.map flatToValue with
      | .abs, [.litv (.float64 x)] => some (s, .val (.litv (.float64 (fpSemFpUopComp .abs x))))
      | .neg, [.litv (.float64 x)] => some (s, .val (.litv (.float64 (fpSemFpUopComp .neg x))))
      | .sqrt, [.litv (.float64 x)] => some (s, .val (.litv (.float64 (fpSemFpUopComp .sqrt x))))
      | .add, [.litv (.float64 x), .litv (.float64 y)] =>
        some (s, .val (.litv (.float64 (fpSemFpBopComp .add x y))))
      | .sub, [.litv (.float64 x), .litv (.float64 y)] =>
        some (s, .val (.litv (.float64 (fpSemFpBopComp .sub x y))))
      | .mul, [.litv (.float64 x), .litv (.float64 y)] =>
        some (s, .val (.litv (.float64 (fpSemFpBopComp .mul x y))))
      | .div, [.litv (.float64 x), .litv (.float64 y)] =>
        some (s, .val (.litv (.float64 (fpSemFpBopComp .div x y))))
      | .fma, [.litv (.float64 x), .litv (.float64 y), .litv (.float64 z)] =>
        some (s, .val (.litv (.float64 (fpSemFpfma x y z))))
      | _, _ => none := by
  generalize valuesEq : vs.map flatToValue = values
  simp only [doApp, doAppNumeric, applyNumericProjection,
    SemanticPrimitivesHOL.doApp_arith_core, valuesEq]
  clear valuesEq
  by_cases checked : values.all (SemanticPrimitivesHOL.checkType .float64T) = true
  · let bits := values.map theLitvFloat64
    have equal : values = bits.map (fun w => SemanticPrimitivesHOL.Value.litv (.float64 w)) := by
      simpa [bits, List.map_map, Function.comp_def] using
        (Flapjack.SemanticPrimitivesProps.checkedFloatValues_roundtrip values checked).symm
    rw [equal]
    cases op <;> cases bits with
      | nil => simp [doArith]
      | cons first rest =>
        cases rest with
        | nil => simp [doArith, SemanticPrimitivesHOL.checkType, theLitvFloat64, valueToFlat,
            fpSemFpUopComp]
        | cons second rest =>
          cases rest with
          | nil => simp [doArith, SemanticPrimitivesHOL.checkType, theLitvFloat64, valueToFlat,
              fpSemFpBopComp]
          | cons third rest =>
            cases rest <;> simp [doArith, SemanticPrimitivesHOL.checkType, theLitvFloat64, valueToFlat,
              fpSemFpfma]
  · have unchecked : values.all (SemanticPrimitivesHOL.checkType .float64T) = false := by
      cases h : values.all (SemanticPrimitivesHOL.checkType .float64T) <;> simp_all
    simp only [unchecked, Bool.false_eq_true, if_false]
    cases op
    all_goals repeat' first | (split <;> simp_all [SemanticPrimitivesHOL.checkType]) | contradiction
    all_goals simp_all

/-- Boolean negation accepts only the two source Boolean constructors. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_arithBool_source {C F : Type} (s : State C F)
    (op : Arith) (vs : List Value) :
    doApp s (.src (.arith op .boolT)) vs =
      match op, vs.map flatToValue with
      | .not, [.conv (some (.typeStamp name 0)) []] =>
        if name = ofString "True" then some (s, .val (boolValue false))
        else if name = ofString "False" then some (s, .val (boolValue true)) else none
      | _, _ => none := by
  generalize valuesEq : vs.map flatToValue = values
  simp only [doApp, doAppNumeric, applyNumericProjection,
    SemanticPrimitivesHOL.doApp_arith_core, doAppNumericCore, valuesEq]
  clear valuesEq
  cases op <;> simp
  all_goals have distinct : ofString "False" ≠ ofString "True" := by decide
  all_goals repeat' first | split at * | simp_all [SemanticPrimitivesHOL.checkType,
    SemanticPrimitivesHOL.boolValue, SemanticPrimitivesHOL.boolTypeNum, valueToFlat]

/-- Character arithmetic is not defined by the source primitive dispatcher. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_arithChar_source {C F : Type} (s : State C F)
    (op : Arith) (vs : List Value) :
    doApp s (.src (.arith op .charT)) vs = none := by
  cases op <;> simp [doApp, doAppNumeric, applyNumericProjection,
    SemanticPrimitivesHOL.doApp_arith_core, doAppNumericCore]

/-- String arithmetic is not defined by the source primitive dispatcher. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_arithString_source {C F : Type} (s : State C F)
    (op : Arith) (vs : List Value) :
    doApp s (.src (.arith op .strT)) vs = none := by
  cases op <;> simp [doApp, doAppNumeric, applyNumericProjection,
    SemanticPrimitivesHOL.doApp_arith_core, doAppNumericCore]

/-- Primitive conversions check the projected input type, preserve the word
bit patterns and raise the character exception for out-of-range integers. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_fromTo_source {C F : Type} (s : State C F)
    (source target : PrimType) (vs : List Value) :
    doApp s (.src (.fromTo source target)) vs =
      match source, target, vs.map flatToValue with
      | .wordT .w8, .intT, [.litv (.word8 w)] => some (s, .val (.litv (.intLit w.toNat)))
      | .wordT .w64, .intT, [.litv (.word64 w)] => some (s, .val (.litv (.intLit w.toNat)))
      | .intT, .wordT .w8, [.litv (.intLit i)] => some (s, .val (.litv (.word8 (BitVec.ofInt 8 i))))
      | .intT, .wordT .w64, [.litv (.intLit i)] => some (s, .val (.litv (.word64 (BitVec.ofInt 64 i))))
      | .charT, .intT, [.litv (.char c)] => some (s, .val (.litv (.intLit c.toNat)))
      | .intT, .charT, [.litv (.intLit i)] =>
        if i < 0 ∨ i > 255 then some (s, .err (.raise chrExnV))
        else some (s, .val (.litv (.char (BitVec.ofNat 8 i.toNat))))
      | .charT, .wordT .w8, [.litv (.char c)] => some (s, .val (.litv (.word8 c)))
      | .wordT .w8, .charT, [.litv (.word8 w)] => some (s, .val (.litv (.char w)))
      | .float64T, .wordT .w64, [.litv (.float64 w)] => some (s, .val (.litv (.word64 w)))
      | .wordT .w64, .float64T, [.litv (.word64 w)] => some (s, .val (.litv (.float64 w)))
      | _, _, _ => none := by
  generalize valuesEq : vs.map flatToValue = values
  simp only [doApp, doAppNumeric, applyNumericProjection,
    SemanticPrimitivesHOL.doApp_fromTo_core, doAppNumericCore, valuesEq]
  clear valuesEq
  all_goals cases source <;> cases target
  all_goals try (cases ‹WordSize›)
  all_goals try (cases ‹WordSize›)
  all_goals try (simp [valueToFlat])
  all_goals cases values <;> try (rename_i value rest; cases rest <;> cases value <;> try (cases ‹Lit›))
  all_goals try simp
  all_goals split <;> simp_all

end Flapjack.Compiler.Backend.FlatSem
