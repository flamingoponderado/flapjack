import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateLength

/-! List evaluation facts for the source-shaped BVI evaluator. -/
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value unitValue)

/-- The source-shaped tuple interface for BVI evaluation. This remains
untagged until the evaluator and its primitive dispatcher are reviewed. -/
noncomputable def evaluateTuple {C F : Type}
    (input : List Bvi.Exp × List Value × BviState C F) : EvalResult C F :=
  evaluate input.1 input.2.1 input.2.2

/-- Successful evaluation returns one value per expression. -/
theorem evaluateImpLength {C F : Type} (expressions : List Bvi.Exp)
    (env : List Value) (state next : BviState C F) (values : List Value)
    (run : evaluateTuple (expressions, env, state) = (.val values, next)) :
    expressions.length = values.length :=
  (evaluate_length expressions env state next values run).symm

/-- Successful singleton evaluation returns one value. -/
theorem evaluateSing {C F : Type} (expression : Bvi.Exp) (env : List Value)
    (state next : BviState C F) (values : List Value)
    (run : evaluateTuple ([expression], env, state) = (.val values, next)) :
    ∃ value, values = [value] :=
  evaluate_singleton expression env state next values run

/-- The non-singleton case of sequential list evaluation. This is untagged
until the underlying BVI evaluator is reviewed. -/
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

/-- Evaluating a nonempty list evaluates its head and tail in sequence. -/
theorem evaluateCons {C F : Type} (expression : Bvi.Exp) (expressions : List Bvi.Exp)
    (env : List Value) (state : BviState C F) :
    evaluateTuple (expression :: expressions, env, state) =
      match evaluateTuple ([expression], env, state) with
      | (.val values, next) =>
        match evaluateTuple (expressions, env, next) with
        | (.val tail, last) => (.val (@Flapjack.holHd Value ⟨unitValue⟩ values :: tail), last)
        | other => other
      | other => other := by
  cases expressions with
  | nil =>
    cases run : evaluateTuple ([expression], env, state) with
    | mk result next =>
      cases result with
      | err error => simp
      | val values =>
        have run' : evaluate [expression] env state = (.val values, next) := run
        obtain ⟨value, rfl⟩ := evaluate_singleton expression env state next values run'
        simp [evaluateTuple, evaluate, Flapjack.holHd]
  | cons second rest => exact evaluateConsCons expression second rest env state

/-- Evaluating an append evaluates its two parts in order. -/
theorem evaluateAppend {C F : Type} (first : List Bvi.Exp) (env : List Value)
    (state : BviState C F) (second : List Bvi.Exp) :
    evaluateTuple (first ++ second, env, state) =
      match evaluateTuple (first, env, state) with
      | (.val values, next) =>
        match evaluateTuple (second, env, next) with
        | (.val tail, last) => (.val (values ++ tail), last)
        | other => other
      | other => other := by
  induction first generalizing state with
  | nil =>
    simp only [List.nil_append, evaluateTuple]
    rw [evaluate]
    dsimp only
    cases evaluate second env state with
    | mk result next => cases result <;> rfl
  | cons expression rest ih =>
    rw [List.cons_append, evaluateCons expression (rest ++ second) env state,
      evaluateCons expression rest env state]
    cases headRun : evaluateTuple ([expression], env, state) with
    | mk headResult next =>
      cases headResult with
      | err error => rfl
      | val values =>
        dsimp only
        rw [ih]
        cases tailRun : evaluateTuple (rest, env, next) with
        | mk tailResult last =>
          cases tailResult with
          | err error => rfl
          | val tail =>
            dsimp only
            cases evaluateTuple (second, env, last) with
            | mk result final => cases result <;> simp

/-- Evaluating a list with one final expression. -/
theorem evaluateSnoc {C F : Type} (expressions : List Bvi.Exp) (env : List Value)
    (state : BviState C F) (expression : Bvi.Exp) :
    evaluateTuple (expressions ++ [expression], env, state) =
      match evaluateTuple (expressions, env, state) with
      | (.val values, next) =>
        match evaluateTuple ([expression], env, next) with
        | (.val tail, last) => (.val (values ++ tail), last)
        | other => other
      | other => other :=
  evaluateAppend expressions env state [expression]

end Flapjack.Compiler.Backend.BviSem
