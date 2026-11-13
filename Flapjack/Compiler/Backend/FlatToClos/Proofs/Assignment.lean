module

public import Flapjack.Compiler.Backend.FlatToClos.Proofs.Memory
public import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate

@[expose] public section

/-! Scalar assignment in the proof-side flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- After the assignment value is evaluated, the inserted zero index
precedes the reference expression and does not alter its result or state. -/
theorem evaluate_assignment_args {C F : Type} (valueExpr refExpr : ClosLang.Exp)
    (env : List ClosSem.Value) (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.evaluate [valueExpr] env state = (.val [value], next)) :
    ClosSem.evaluate [valueExpr, .op .none (.intOp (.const 0)) [], refExpr] env state =
      match ClosSem.evaluate [refExpr] env next with
      | (.err error, last) => (.err error, last)
      | (.val values, last) => (.val (value :: .number 0 :: values), last) := by
  rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ run]
  rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ (by
    simpa only [ClosSem.makeConst] using
      (destConstant_evaluate (.op .none (.intOp (.const 0)) []) (.constInt 0) env next rfl))]
  cases result : ClosSem.evaluate [refExpr] env next with
  | mk outcome last => cases outcome <;> rfl

end Flapjack.Compiler.Backend.FlatToClos
