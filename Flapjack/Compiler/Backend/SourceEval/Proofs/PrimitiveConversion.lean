module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.PrimitiveArithmetic

@[expose] public section
/-! Source primitive conversion transport for evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.AstHOL

set_option maxHeartbeats 3000000 in
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
  rw [doApp_fromTo_core] at run
  cases sourceType <;> cases targetType <;>
    simp only [doAppNumericCore, Option.getD_some] at run <;>
    repeat' first | split at run | contradiction
  all_goals cases related
  all_goals rename_i head tail
  all_goals cases tail
  all_goals have same := concreteValue_rel es _ _ head (by simp [concreteValue])
  all_goals cases same
  all_goals rw [doApp_fromTo_core]
  all_goals simp_all [doAppNumericCore, Option.getD_some]
  all_goals obtain ⟨_, rfl⟩ := run
  all_goals simp_all [resultRel, excRel]
  all_goals apply (valueRel_concrete es).1
  all_goals simp [concreteValue, concreteValues, chrExnV]

end Flapjack.Compiler.Backend.SourceEval.Proofs
