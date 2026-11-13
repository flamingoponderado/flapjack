module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.Apply

@[expose] public section

/-! Source-shaped numeric application cases for the flat evaluator. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Basis.Pure.MlString

/-- The original flat arithmetic clause, including its type guard and
translation of source results. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_arith_source {C F : Type} (s : State C F)
    (action : Arith) (typ : PrimType) (values : List Value) :
    doApp s (.src (.arith action typ)) values =
      let sourceValues := values.map flatToValue
      if sourceValues.all (SemanticPrimitivesHOL.checkType typ) then
        match SemanticPrimitivesHOL.doArith action typ sourceValues with
        | none => none
        | some (.inl _) => some (s, .err (.raise divExnV))
        | some (.inr result) => some (s, .val (valueToFlat result))
      else none := by
  simp only [doApp, doAppNumeric, applyNumericProjection, SemanticPrimitivesHOL.doApp]
  split <;> simp_all
  split <;> simp_all

/-- The conversion clause accepts one value and rejects other arities. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_conversion_source {C F : Type} (s : State C F)
    (source target : PrimType) (values : List Value) :
    doApp s (.src (.fromTo source target)) values =
      match values with
      | [value] =>
        let sourceValue := flatToValue value
        if SemanticPrimitivesHOL.checkType source sourceValue then
          match SemanticPrimitivesHOL.doConversion sourceValue source target with
          | none => none
          | some (.inl _) => some (s, .err (.raise chrExnV))
          | some (.inr result) => some (s, .val (valueToFlat result))
        else none
      | _ => none := by
  cases values with
  | nil => simp [doApp, doAppNumeric, applyNumericProjection, SemanticPrimitivesHOL.doApp]
  | cons value rest =>
    cases rest with
    | nil =>
      simp only [doApp, doAppNumeric, applyNumericProjection, SemanticPrimitivesHOL.doApp, List.map_cons, List.map_nil]
      split <;> simp_all
      split <;> simp_all
    | cons _ _ => simp [doApp, doAppNumeric, applyNumericProjection, SemanticPrimitivesHOL.doApp]

end Flapjack.Compiler.Backend.FlatSem
