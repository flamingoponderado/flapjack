import Flapjack.SemanticPrimitivesHOL.Arithmetic
import Flapjack.SemanticPrimitivesHOL.FloatArithmetic

/-! Agreement of the computable arithmetic dispatchers with HOL's guard. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.AstHOL Flapjack.Basis.Pure.MlString

private theorem intRoundtrip (values : List Value) (checked : values.all (checkType .intT) = true) :
    values.map (fun v => Value.litv (.intLit (theLitvInt v))) = values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at checked
    cases value <;> simp_all [checkType]
    case litv lit =>
      cases lit <;> simp_all [theLitvInt]

private theorem intCase {σ : Type} (state : Store Value × HolFfiState σ)
    (action : Arith) (values : List Value) :
    (if values.all (checkType .intT) then
      (doArith action .intT values).map (fun result =>
        match result with
        | .inl error => (state, .err (.raise error))
        | .inr value => (state, .val value))
      else none) = (doAppNumericCore state (.arith action .intT) values).getD none := by
  by_cases checked : values.all (checkType .intT) = true
  · let ints := values.map theLitvInt
    have equal : values = ints.map (fun i => Value.litv (.intLit i)) := by
      simpa [ints, List.map_map, Function.comp_def] using (intRoundtrip values checked).symm
    rw [equal]
    cases action <;> cases ints with
      | nil => simp [doArith, doAppNumericCore]
      | cons first rest =>
        cases rest with
        | nil => simp [doArith, doAppNumericCore, checkType, theLitvInt]
        | cons second rest =>
          cases rest <;> by_cases h : second = 0 <;>
            simp [doArith, doAppNumericCore, checkType, theLitvInt, h]
  · have unchecked : values.all (checkType .intT) = false := by
      cases h : values.all (checkType .intT) <;> simp_all
    simp only [unchecked, Bool.false_eq_true, if_false]
    cases action <;> simp only [doAppNumericCore]
    all_goals repeat' first | (split <;> simp_all [checkType]) | contradiction


private theorem word8Roundtrip (values : List Value) (checked : values.all (checkType (.wordT .w8)) = true) :
    values.map (fun v => Value.litv (.word8 (theLitvWord8 v))) = values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at checked
    cases value <;> simp_all [checkType]
    case litv lit => cases lit <;> simp_all [theLitvWord8]

private theorem word8Case {σ : Type} (state : Store Value × HolFfiState σ)
    (action : Arith) (values : List Value) :
    (if values.all (checkType (.wordT .w8)) then
      (doArith action (.wordT .w8) values).map (fun result =>
        match result with
        | .inl error => (state, .err (.raise error))
        | .inr value => (state, .val value))
      else none) = (doAppNumericCore state (.arith action (.wordT .w8)) values).getD none := by
  by_cases checked : values.all (checkType (.wordT .w8)) = true
  · let words := values.map theLitvWord8
    have equal : values = words.map (fun w => Value.litv (.word8 w)) := by
      simpa [words, List.map_map, Function.comp_def] using (word8Roundtrip values checked).symm
    rw [equal]
    cases action <;> cases words with
      | nil => simp [doArith, doAppNumericCore]
      | cons first rest =>
        cases rest with
        | nil => simp [doArith, doAppNumericCore, checkType, theLitvWord8]
        | cons second rest =>
          cases rest <;> simp [doArith, doAppNumericCore, checkType, theLitvWord8, wordArith]
  · have unchecked : values.all (checkType (.wordT .w8)) = false := by
      cases h : values.all (checkType (.wordT .w8)) <;> simp_all
    simp only [unchecked, Bool.false_eq_true, if_false]
    cases action <;> simp only [doAppNumericCore]
    all_goals repeat' first | (split <;> simp_all [checkType]) | contradiction

private theorem word64Roundtrip (values : List Value) (checked : values.all (checkType (.wordT .w64)) = true) :
    values.map (fun v => Value.litv (.word64 (theLitvWord64 v))) = values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at checked
    cases value <;> simp_all [checkType]
    case litv lit => cases lit <;> simp_all [theLitvWord64]

private theorem word64Case {σ : Type} (state : Store Value × HolFfiState σ)
    (action : Arith) (values : List Value) :
    (if values.all (checkType (.wordT .w64)) then
      (doArith action (.wordT .w64) values).map (fun result =>
        match result with
        | .inl error => (state, .err (.raise error))
        | .inr value => (state, .val value))
      else none) = (doAppNumericCore state (.arith action (.wordT .w64)) values).getD none := by
  by_cases checked : values.all (checkType (.wordT .w64)) = true
  · let words := values.map theLitvWord64
    have equal : values = words.map (fun w => Value.litv (.word64 w)) := by
      simpa [words, List.map_map, Function.comp_def] using (word64Roundtrip values checked).symm
    rw [equal]
    cases action <;> cases words with
      | nil => simp [doArith, doAppNumericCore]
      | cons first rest =>
        cases rest with
        | nil => simp [doArith, doAppNumericCore, checkType, theLitvWord64]
        | cons second rest =>
          cases rest <;> simp [doArith, doAppNumericCore, checkType, theLitvWord64, wordArith]
  · have unchecked : values.all (checkType (.wordT .w64)) = false := by
      cases h : values.all (checkType (.wordT .w64)) <;> simp_all
    simp only [unchecked, Bool.false_eq_true, if_false]
    cases action <;> simp only [doAppNumericCore]
    all_goals repeat' first | (split <;> simp_all [checkType]) | contradiction

private theorem floatRoundtrip (values : List Value) (checked : values.all (checkType .float64T) = true) :
    values.map (fun v => Value.litv (.float64 (theLitvFloat64 v))) = values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at checked
    cases value <;> simp_all [checkType]
    case litv lit => cases lit <;> simp_all [theLitvFloat64]

private theorem floatCase {σ : Type} (state : Store Value × HolFfiState σ)
    (action : Arith) (values : List Value) :
    (if values.all (checkType .float64T) then
      (doArith action .float64T values).map (fun result =>
        match result with
        | .inl error => (state, (Result.err (.raise error) : Result Value Value))
        | .inr value => (state, (Result.val value : Result Value Value)))
      else none) = (floatArith action values).map (fun result => (state, (Result.val result : Result Value Value))) := by
  by_cases checked : values.all (checkType .float64T) = true
  · let floats := values.map theLitvFloat64
    have equal : values = floats.map (fun w => Value.litv (.float64 w)) := by
      simpa [floats, List.map_map, Function.comp_def] using (floatRoundtrip values checked).symm
    rw [equal]
    cases action <;> cases floats with
      | nil => simp [doArith, floatArith]
      | cons first rest =>
        cases rest with
        | nil => simp [doArith, floatArith, checkType, theLitvFloat64, fpSemFpUopComp]
        | cons second rest =>
          cases rest with
          | nil => simp [doArith, floatArith, checkType, theLitvFloat64, fpSemFpBopComp]
          | cons third rest =>
            cases rest <;> simp [doArith, floatArith, checkType, theLitvFloat64, fpSemFpfma]
  · have unchecked : values.all (checkType .float64T) = false := by
      cases h : values.all (checkType .float64T) <;> simp_all
    simp only [unchecked, Bool.false_eq_true, if_false]
    cases action <;> simp only [floatArith]
    all_goals repeat' first | (split <;> simp_all [checkType]) | contradiction
    all_goals simp_all

private theorem boolCase {σ : Type} (state : Store Value × HolFfiState σ)
    (action : Arith) (values : List Value) :
    (if values.all (checkType .boolT) then
      (doArith action .boolT values).map (fun result =>
        match result with
        | .inl error => (state, .err (.raise error))
        | .inr value => (state, .val value))
      else none) = (doAppNumericCore state (.arith action .boolT) values).getD none := by
  cases action <;> try (simp [doArith, doAppNumericCore])
  case not =>
    cases values with
    | nil => rfl
    | cons value rest =>
      cases rest with
      | cons second rest => simp
      | nil =>
        cases value with
        | conv stamp fields =>
          cases fields with
          | cons head tail => simp [checkType]
          | nil =>
            cases stamp with
            | none => simp [checkType]
            | some stamp =>
              cases stamp with
              | exnStamp n => simp [checkType]
              | typeStamp name n =>
                cases n with
                | succ n => simp [checkType]
                | zero =>
                  simp [checkType, theBoolv, boolValue, boolTypeNum]
        | _ => simp [checkType]

/-- The computable arithmetic dispatchers agree with the guarded HOL
arithmetic operation for every argument list. This Flapjack correspondence
lemma has no separate HOL declaration. -/
theorem doAppArithCore {σ : Type} (state : Store Value × HolFfiState σ)
    (action : Arith) (typ : PrimType) (values : List Value) :
    (if values.all (checkType typ) then
      (doArith action typ values).map (fun result =>
        match result with
        | .inl error => (state, .err (.raise error))
        | .inr value => (state, .val value))
      else none) =
      (match typ with
       | .float64T => (floatArith action values).map (fun result => (state, .val result))
       | _ => (doAppNumericCore state (.arith action typ) values).getD none) := by
  cases typ with
  | boolT => exact boolCase state action values
  | intT => exact intCase state action values
  | wordT width => cases width with
    | w8 => exact word8Case state action values
    | w64 => exact word64Case state action values
  | float64T => exact floatCase state action values
  | charT => cases action <;> simp [doArith, doAppNumericCore]
  | strT => cases action <;> simp [doArith, doAppNumericCore]

end Flapjack.SemanticPrimitivesHOL
