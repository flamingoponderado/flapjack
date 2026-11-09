import Flapjack.SemanticPrimitivesHOL.Arithmetic

/-! Type preservation for source primitive arithmetic. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

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
