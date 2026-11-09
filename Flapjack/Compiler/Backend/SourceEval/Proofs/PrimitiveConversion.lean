module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.PrimitiveArithmetic

@[expose] public section
/-! Source primitive conversion transport for evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.AstHOL

set_option maxHeartbeats 3000000 in
private theorem conversionResult_transport {F : Type} (es : EvalOracleState) (state target : Store Value × HolFfiState F)
    (sourceType targetType : PrimType) (xs : List Value) (refs : Store Value)
    (ffi : HolFfiState F) (result : Result Value Value)
    (run : doApp state (.fromTo sourceType targetType) xs = some ((refs, ffi), result)) :
    xs.all (checkType sourceType) = true ∧ refs = state.1 ∧ ffi = state.2 ∧
    doApp target (.fromTo sourceType targetType) xs = some (target, result) ∧
    resultRel (ValueRel es) (ValueRel es) result result := by
  rw [doApp_fromTo_core] at run ⊢
  cases sourceType <;> cases targetType <;>
    simp only [doAppNumericCore, Option.getD_some] at run ⊢ <;>
    repeat' first | split at run | contradiction
  all_goals simp_all [checkType]
  all_goals obtain ⟨_, rfl⟩ := run
  all_goals simp_all [resultRel, excRel]
  all_goals apply (valueRel_concrete es).1
  all_goals simp [concreteValue, concreteValues, chrExnV]
/-- A successful conversion transports to related operands and an arbitrary
state, preserving its result relation. HOL proves this inside the
`do_app_sim` conversion case; it is not a separate HOL declaration. -/
theorem conversionApp_transport {F : Type} (es : EvalOracleState)
    (state target : Store Value × HolFfiState F) (sourceType targetType : PrimType)
    (xs ys : List Value) (refs : Store Value) (ffi : HolFfiState F) (result : Result Value Value)
    (run : doApp state (.fromTo sourceType targetType) xs = some ((refs, ffi), result))
    (related : List.Forall₂ (ValueRel es) xs ys) :
    refs = state.1 ∧ ffi = state.2 ∧
    doApp target (.fromTo sourceType targetType) ys = some (target, result) ∧
    resultRel (ValueRel es) (ValueRel es) result result := by
  obtain ⟨checked, refEq, ffiEq, targetRun, resultRelated⟩ :=
    conversionResult_transport es state target sourceType targetType xs refs ffi result run
  have same := checkedOperands_eq es sourceType xs ys checked related
  subst ys
  exact ⟨refEq, ffiEq, targetRun, resultRelated⟩

end Flapjack.Compiler.Backend.SourceEval.Proofs
