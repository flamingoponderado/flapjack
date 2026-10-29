import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyClock

/-! Clock bounds for the proof-side unbounded closure evaluator. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- Clamping an evaluation result bounds its clock by the input clock. -/
theorem fixClock_clock_le {C F : Type} (state : State C F) (result : EvalResult C F) :
    (fixClock state result).2.clock ≤ state.clock := by
  exact Nat.min_le_left _ _

/-- A primitive result retains the input clock on success. -/
theorem doApp_success_clock {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : State C F) (value : Value) (next : State C F)
    (run : doApp op args state = .val (value, next)) : next.clock ≤ state.clock := by
  rw [doApp_clock op args state next value run]

/-- Evaluating a multi-expression list respects the clock bound when the
tail does after the first expression's clock clamp. -/
theorem evaluate_list_clock_step {C F : Type} (env : List Value) (state : State C F)
    (first second : ClosLang.Exp) (rest : List ClosLang.Exp)
    (tailClock : ∀ next : State C F, next.clock ≤ state.clock →
      (evaluate (second :: rest) env next).2.clock ≤ next.clock) :
    (evaluate (first :: second :: rest) env state).2.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate [first] env state)
  rw [evaluate]
  generalize h : fixClock state (evaluate [first] env state) = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    have tailBound := Nat.le_trans (tailClock next bound) bound
    generalize tailRun : evaluate (second :: rest) env next = evaluatedTail at *
    obtain ⟨tailResult, last⟩ := evaluatedTail
    cases tailResult <;> exact tailBound

/-- A raise preserves the clock bound if its operand does. -/
theorem evaluate_raise_clock_step {C F : Type} (env : List Value) (state : State C F)
    (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (operandClock : (evaluate [body] env state).2.clock ≤ state.clock) :
    (evaluate [.raise trace body] env state).2.clock ≤ state.clock := by
  rw [evaluate]
  generalize h : evaluate [body] env state = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  cases result <;> exact operandClock

/-- A let-expression respects the bound when its body does for every
environment and every clock reached after evaluating the bindings. -/
theorem evaluate_let_clock_step {C F : Type} (env : List Value) (state : State C F)
    (trace : BackendCommon.Tra) (bindings : List ClosLang.Exp) (body : ClosLang.Exp)
    (bodyClock : ∀ (newEnv : List Value) (next : State C F), next.clock ≤ state.clock →
      (evaluate [body] newEnv next).2.clock ≤ next.clock) :
    (evaluate [.let trace bindings body] env state).2.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate bindings env state)
  rw [evaluate]
  generalize h : fixClock state (evaluate bindings env state) = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values => exact Nat.le_trans (bodyClock (values ++ env) next bound) bound

/-- A handler respects the bound when its handler expression does for each
raised value at the clamped intermediate state. -/
theorem evaluate_handle_clock_step {C F : Type} (env : List Value) (state : State C F)
    (trace : BackendCommon.Tra) (body handler : ClosLang.Exp)
    (handlerClock : ∀ (value : Value) (next : State C F), next.clock ≤ state.clock →
      (evaluate [handler] (value :: env) next).2.clock ≤ next.clock) :
    (evaluate [.handle trace body handler] env state).2.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate [body] env state)
  rw [evaluate]
  generalize h : fixClock state (evaluate [body] env state) = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | val values => exact bound
  | err error =>
    cases error with
    | abort reason => exact bound
    | raise value => exact Nat.le_trans (handlerClock value next bound) bound

end Flapjack.Compiler.Backend.ClosSem
