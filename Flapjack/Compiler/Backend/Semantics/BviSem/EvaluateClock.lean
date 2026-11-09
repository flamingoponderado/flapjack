import Flapjack.Compiler.Backend.Semantics.BviSem.Evaluate
import Flapjack.Compiler.Backend.Semantics.BviSem.ApplyClock

/-! Clock-bound building blocks for BVI evaluation. -/
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Evaluating a multi-expression list respects the clock bound when the
tail does after the first expression's clock clamp. -/
theorem evaluate_list_clock_step {C F : Type} (env : List Value) (state : BviState C F)
    (first second : Bvi.Exp) (rest : List Bvi.Exp)
    (tailClock : ∀ next : BviState C F, next.clock ≤ state.clock →
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
theorem evaluate_raise_clock_step {C F : Type} (env : List Value) (state : BviState C F)
    (body : Bvi.Exp)
    (operandClock : (evaluate [body] env state).2.clock ≤ state.clock) :
    (evaluate [.raise body] env state).2.clock ≤ state.clock := by
  rw [evaluate]
  generalize h : evaluate [body] env state = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  cases result <;> exact operandClock

/-- A let-expression respects the bound when its body does for every
environment and every clock reached after evaluating the bindings. -/
theorem evaluate_let_clock_step {C F : Type} (env : List Value) (state : BviState C F)
    (bindings : List Bvi.Exp) (body : Bvi.Exp)
    (bodyClock : ∀ (newEnv : List Value) (next : BviState C F), next.clock ≤ state.clock →
      (evaluate [body] newEnv next).2.clock ≤ next.clock) :
    (evaluate [.let bindings body] env state).2.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate bindings env state)
  rw [evaluate]
  generalize h : fixClock state (evaluate bindings env state) = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values => exact Nat.le_trans (bodyClock (values ++ env) next bound) bound

/-- A conditional respects the bound when both branches do at the clamped
condition state. -/
theorem evaluate_if_clock_step {C F : Type} (env : List Value) (state : BviState C F)
    (condition yes no : Bvi.Exp)
    (yesClock : ∀ next : BviState C F, next.clock ≤ state.clock →
      (evaluate [yes] env next).2.clock ≤ next.clock)
    (noClock : ∀ next : BviState C F, next.clock ≤ state.clock →
      (evaluate [no] env next).2.clock ≤ next.clock) :
    (evaluate [.ifThenElse condition yes no] env state).2.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate [condition] env state)
  rw [evaluate]
  generalize h : fixClock state (evaluate [condition] env state) = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    dsimp only
    split
    · simpa using bound
    · exact Nat.le_trans (yesClock next bound) bound
    · exact Nat.le_trans (noClock next bound) bound


/-- Ticking reduces the clock or times out. -/
theorem evaluate_tick_clock_step {C F : Type} (env : List Value) (state : BviState C F)
    (body : Bvi.Exp)
    (bodyClock : (evaluate [body] env (decClock 1 state)).2.clock ≤ (decClock 1 state).clock) :
    (evaluate [.tick body] env state).2.clock ≤ state.clock := by
  rw [evaluate]
  split
  · simp
  · exact Nat.le_trans bodyClock (Nat.sub_le _ _)

/-- Primitive application preserves the clock bound after argument evaluation. -/
theorem evaluate_op_clock {C F : Type} (env : List Value) (state : BviState C F)
    (op : ClosLang.Op) (args : List Bvi.Exp) :
    (evaluate [.op op args] env state).2.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate args env state)
  rw [evaluate]
  generalize h : fixClock state (evaluate args env state) = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    cases run : doApp op values.reverse next with
    | err error => simpa [run] using bound
    | val pair =>
      obtain ⟨value, last⟩ := pair
      have preserved := doApp_clock op values.reverse next last value run
      simpa [run, preserved] using bound

/-- A return preserves the bound if evaluation of its argument list does. -/
theorem evaluate_return_clock_step {C F : Type} (env : List Value) (state : BviState C F)
    (args : List Bvi.Exp)
    (argsClock : (evaluate args env state).2.clock ≤ state.clock) :
    (evaluate [.return args] env state).2.clock ≤ state.clock := by
  rw [evaluate]
  generalize h : evaluate args env state = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  cases result <;> exact argsClock

end Flapjack.Compiler.Backend.BviSem
