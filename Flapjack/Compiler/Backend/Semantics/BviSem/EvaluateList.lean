import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateClockFull

/-! List evaluation facts for the source-shaped BVI evaluator. -/
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value unitValue)

/-- The source-shaped tuple interface for BVI evaluation. This remains
untagged until the evaluator and its primitive dispatcher are reviewed. -/
noncomputable def evaluateTuple {C F : Type}
    (input : List Bvi.Exp × List Value × BviState C F) : EvalResult C F :=
  evaluate input.1 input.2.1 input.2.2

/-- The non-singleton case of sequential list evaluation. The singleton case
also needs the successful-result length invariant and remains open. This is
untagged until the underlying BVI evaluator is reviewed. -/
theorem evaluateConsCons {C F : Type} (first second : Bvi.Exp)
    (rest : List Bvi.Exp) (env : List Value) (state : BviState C F) :
    evaluateTuple (first :: second :: rest, env, state) =
      match evaluateTuple ([first], env, state) with
      | (.val values, next) =>
        match evaluateTuple (second :: rest, env, next) with
        | (.val tail, last) => (.val (@Flapjack.holHd Value ⟨unitValue⟩ values :: tail), last)
        | other => other
      | other => other := by
  simp only [evaluateTuple]
  rw [evaluate, fixClock_evaluate]
  cases evaluate [first] env state with
  | mk result next =>
    cases result with
    | err error => rfl
    | val values =>
      dsimp only
      cases evaluate (second :: rest) env next with
      | mk result last => cases result <;> rfl

end Flapjack.Compiler.Backend.BviSem
