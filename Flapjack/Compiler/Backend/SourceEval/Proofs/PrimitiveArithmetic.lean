module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.SimulationPrerequisites
public import Flapjack.SemanticPrimitivesHOL.ApplyNumeric
public import Flapjack.SemanticPrimitivesProps.ResultRelation
public import Flapjack.SemanticPrimitivesProps.Arithmetic

@[expose] public section

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
  simp only [doApp] at run
  split at run
  · rename_i checked
    have same := checkedOperands_eq es typ xs ys checked related
    subst ys
    simp only [Option.map_eq_some_iff] at run
    obtain ⟨out, evaluated, equal⟩ := run
    cases out with
    | inl exn =>
      have exception := doArith_exception action typ xs exn evaluated
      subst exn
      simp only [Prod.mk.injEq] at equal
      obtain ⟨same, rfl⟩ := equal
      cases same
      refine ⟨rfl, rfl, ?_, ?_⟩
      · simp [doApp, checked, evaluated]
      · simp only [resultRel, excRel]
        exact (valueRel_concrete es).1 divExnV (by simp [concreteValue, concreteValues, divExnV])
    | inr value =>
      have valueType := doArith_checkType action typ xs value evaluated
      simp only [Prod.mk.injEq] at equal
      obtain ⟨same, rfl⟩ := equal
      cases same
      refine ⟨rfl, rfl, ?_, ?_⟩
      · simp [doApp, checked, evaluated]
      · simp only [resultRel]
        exact (valueRel_concrete es).1 value (checkTypeConcrete typ value valueType)
  · simp at run

end Flapjack.Compiler.Backend.SourceEval.Proofs
