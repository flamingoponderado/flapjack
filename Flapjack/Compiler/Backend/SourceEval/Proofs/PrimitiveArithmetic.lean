import Flapjack.Compiler.Backend.SourceEval.Proofs.SimulationPrerequisites
import Flapjack.SemanticPrimitivesHOL.ApplyNumeric

/-! Arithmetic operand preservation for source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

private theorem checkTypeConcrete (typ : PrimType) (v : Value) (checked : checkType typ v = true) :
    concreteValue v = true := by
  cases typ <;> cases v <;> simp_all [checkType, concreteValue]
  case boolT.conv stamp fields =>
    cases fields with
    | nil => simp [concreteValues]
    | cons head rest =>
      cases stamp <;> simp at checked


set_option maxHeartbeats 1200000 in
/-- A successful arithmetic operation has concrete operands, so related
operands are identical. HOL uses the primitive type checks inline in the
`do_app_sim` arithmetic case; this is not a separate HOL declaration. -/
theorem arithmeticOperands_eq {F : Type} (es : EvalOracleState) (state : Store Value × HolFfiState F)
    (action : Arith) (typ : PrimType) (xs ys : List Value) (output : BasicAppResult F)
    (run : doApp state (.arith action typ) xs = some output)
    (related : List.Forall₂ (ValueRel es) xs ys) : ys = xs := by
  have checked : xs.all (checkType typ) = true := by
    cases typ <;> cases action <;>
      simp only [doApp, doAppNumericCore, floatArith] at run <;>
      repeat' first | split at run | contradiction
    all_goals simp_all [checkType]
  clear run
  induction related with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.all_cons, Bool.and_eq_true] at checked
    have same := concreteValue_rel es _ _ head (checkTypeConcrete typ _ checked.1)
    simp only [same, ih checked.2]

end Flapjack.Compiler.Backend.SourceEval.Proofs
