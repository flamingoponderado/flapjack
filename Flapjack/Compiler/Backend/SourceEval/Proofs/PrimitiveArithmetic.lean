import Flapjack.Compiler.Backend.SourceEval.Proofs.SimulationPrerequisites
import Flapjack.SemanticPrimitivesHOL.ApplyNumeric
import Flapjack.SemanticPrimitivesProps.ResultRelation

/-! Arithmetic operand preservation for source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.AstHOL

private theorem checkTypeConcrete (typ : PrimType) (v : Value) (checked : checkType typ v = true) :
    concreteValue v = true := by
  cases typ <;> cases v <;> simp_all [checkType, concreteValue]
  case boolT.conv stamp fields =>
    cases fields with
    | nil => simp [concreteValues]
    | cons head rest =>
      cases stamp <;> simp at checked


/-- Related lists whose source elements pass a primitive type check are equal.
HOL uses this fact inside `do_app_sim`; it is not a separate HOL declaration. -/
theorem checkedOperands_eq (es : EvalOracleState) (typ : PrimType) (xs ys : List Value)
    (checked : xs.all (checkType typ) = true) (related : List.Forall₂ (ValueRel es) xs ys) :
    ys = xs := by
  induction related with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.all_cons, Bool.and_eq_true] at checked
    have same := concreteValue_rel es _ _ head (checkTypeConcrete typ _ checked.1)
    simp only [same, ih checked.2]


set_option maxHeartbeats 3000000 in
private theorem arithmeticResult_transport {F : Type} (es : EvalOracleState) (state target : Store Value × HolFfiState F)
    (action : Arith) (typ : PrimType) (xs : List Value) (refs : Store Value)
    (ffi : HolFfiState F) (result : Result Value Value)
    (run : doApp state (.arith action typ) xs = some ((refs, ffi), result)) :
    xs.all (checkType typ) = true ∧ refs = state.1 ∧ ffi = state.2 ∧
    doApp target (.arith action typ) xs = some (target, result) ∧
    resultRel (ValueRel es) (ValueRel es) result result := by
  rw [doApp_arith_core] at run ⊢
  cases typ <;> cases action <;>
    simp only [doAppNumericCore, floatArith, Option.getD_some] at run ⊢ <;>
    repeat' first | split at run | contradiction
  all_goals simp_all [wordArith, checkType]
  all_goals obtain ⟨_, rfl⟩ := run
  all_goals simp only [resultRel, excRel]
  all_goals apply (valueRel_concrete es).1
  all_goals simp [concreteValue, concreteValues, divExnV, boolValue]

/-- A successful arithmetic application transports to related operands and a
new state while preserving the result relation. HOL proves this step inside
`do_app_sim`; it is not a separate HOL declaration. -/
theorem arithmeticApp_transport {F : Type} (es : EvalOracleState)
    (state target : Store Value × HolFfiState F) (action : Arith) (typ : PrimType)
    (xs ys : List Value) (refs : Store Value) (ffi : HolFfiState F) (result : Result Value Value)
    (run : doApp state (.arith action typ) xs = some ((refs, ffi), result))
    (related : List.Forall₂ (ValueRel es) xs ys) :
    refs = state.1 ∧ ffi = state.2 ∧
    doApp target (.arith action typ) ys = some (target, result) ∧
    resultRel (ValueRel es) (ValueRel es) result result := by
  obtain ⟨checked, refEq, ffiEq, targetRun, resultRelated⟩ :=
    arithmeticResult_transport es state target action typ xs refs ffi result run
  have same := checkedOperands_eq es typ xs ys checked related
  subst ys
  exact ⟨refEq, ffiEq, targetRun, resultRelated⟩

end Flapjack.Compiler.Backend.SourceEval.Proofs
