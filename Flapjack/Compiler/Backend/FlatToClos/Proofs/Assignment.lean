module

public import Flapjack.Compiler.Backend.FlatToClos.Proofs.Memory
public import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate

@[expose] public section

/-! Scalar assignment in the proof-side flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- The inserted zero index is evaluated without changing state. -/
theorem evaluate_zero_index {C F : Type} (env : List ClosSem.Value) (state : ClosSem.State C F) :
    ClosSem.evaluate [.op .none (.intOp (.const 0)) []] env state = (.val [.number 0], state) := by
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric, ClosSem.doIntApp]

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
  rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ (evaluate_zero_index env next)]
  cases result : ClosSem.evaluate [refExpr] env next with
  | mk outcome last => cases outcome <;> rfl

end Flapjack.Compiler.Backend.FlatToClos
