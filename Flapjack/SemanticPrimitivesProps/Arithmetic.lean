import Flapjack.SemanticPrimitivesHOL.Arithmetic

/-! Type preservation for source primitive arithmetic. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Mapping a checked float list through the HOL selector and constructor
recovers the list. This Flapjack helper has no separate HOL declaration. -/
theorem checkedFloatValues_roundtrip (values : List Value)
    (checked : values.all (checkType .float64T) = true) :
    values.map (fun v => Value.litv (.float64 (theLitvFloat64 v))) = values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at checked
    cases value <;> simp_all [checkType]
    case litv lit => cases lit <;> simp_all [theLitvFloat64]

/-- A successful primitive arithmetic operation has the requested type. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "do_arith_check_type"]
theorem doArith_checkType (action : Arith) (typ : PrimType) (values : List Value) (result : Value)
    (evaluated : doArith action typ values = some (.inr result)) : checkType typ result = true := by
  cases typ <;> try (rename_i width; cases width)
  all_goals cases action <;> simp [doArith, wordArith] at evaluated
  all_goals repeat' first | split at evaluated | contradiction
  all_goals simp_all only [Option.some.injEq, Sum.inr.injEq]
  all_goals try contradiction
  all_goals subst result
  all_goals simp [checkType, boolValue, boolTypeNum]
  all_goals split <;> simp_all

/-- An arithmetic exception is the division exception. This Flapjack helper
has no separate HOL declaration; it supports primitive simulation. -/
theorem doArith_exception (action : Arith) (typ : PrimType) (values : List Value) (exn : Value)
    (evaluated : doArith action typ values = some (.inl exn)) : exn = divExnV := by
  cases typ <;> try (rename_i width; cases width)
  all_goals cases action <;> simp [doArith, wordArith] at evaluated
  all_goals repeat' first | split at evaluated | contradiction
  all_goals simp_all

end Flapjack.SemanticPrimitivesProps
