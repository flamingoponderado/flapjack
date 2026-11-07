import Flapjack.Compiler.Backend.Semantics.BvlSem.Evaluate
import Flapjack.Compiler.Backend.Semantics.BvlSem.ApplyClock

/-! Clock invariants for the source-shaped BVL evaluator. -/
namespace Flapjack.Compiler.Backend.BvlSem
open Flapjack.SemanticPrimitivesHOL

/-- Evaluating a multi-expression list respects the clock bound when the
tail does after the first expression's clock clamp. -/
theorem evaluate_list_clock_step {C F : Type} (env : List Value) (state : State C F)
    (first second : Bvl.Exp) (rest : List Bvl.Exp)
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
    (body : Bvl.Exp)
    (operandClock : (evaluate [body] env state).2.clock ≤ state.clock) :
    (evaluate [.raise body] env state).2.clock ≤ state.clock := by
  rw [evaluate]
  generalize h : evaluate [body] env state = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  cases result <;> exact operandClock

/-- A let-expression respects the bound when its body does for every
environment and every clock reached after evaluating the bindings. -/
theorem evaluate_let_clock_step {C F : Type} (env : List Value) (state : State C F)
    (bindings : List Bvl.Exp) (body : Bvl.Exp)
    (bodyClock : ∀ (newEnv : List Value) (next : State C F), next.clock ≤ state.clock →
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

/-- A handler respects the bound when its handler expression does for each
raised value at the clamped intermediate state. -/
theorem evaluate_handle_clock_step {C F : Type} (env : List Value) (state : State C F)
    (body handler : Bvl.Exp)
    (handlerClock : ∀ (value : Value) (next : State C F), next.clock ≤ state.clock →
      (evaluate [handler] (value :: env) next).2.clock ≤ next.clock) :
    (evaluate [.handle body handler] env state).2.clock ≤ state.clock := by
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

/-- A conditional respects the bound when both branches do at the clamped
condition state. -/
theorem evaluate_if_clock_step {C F : Type} (env : List Value) (state : State C F)
    (condition yes no : Bvl.Exp)
    (yesClock : ∀ next : State C F, next.clock ≤ state.clock →
      (evaluate [yes] env next).2.clock ≤ next.clock)
    (noClock : ∀ next : State C F, next.clock ≤ state.clock →
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
theorem evaluate_tick_clock_step {C F : Type} (env : List Value) (state : State C F)
    (body : Bvl.Exp)
    (bodyClock : (evaluate [body] env (decClock 1 state)).2.clock ≤ (decClock 1 state).clock) :
    (evaluate [.tick body] env state).2.clock ≤ state.clock := by
  rw [evaluate]
  split
  · simp
  · exact Nat.le_trans bodyClock (Nat.sub_le _ _)

/-- Primitive application preserves the clock bound after argument evaluation. -/
theorem evaluate_op_clock {C F : Type} (env : List Value) (state : State C F)
    (op : ClosLang.Op) (args : List Bvl.Exp) :
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

/-- Calls use strictly less clock before entering arbitrary code. -/
theorem evaluate_call_clock_step {C F : Type} (env : List Value) (state : State C F)
    (ticks : Nat) (location : Option Nat) (args : List Bvl.Exp)
    (bodyClock : ∀ (body : Bvl.Exp) (values : List Value) (next : State C F),
      next.clock < state.clock → (evaluate [body] values next).2.clock ≤ next.clock) :
    (evaluate [.call ticks location args] env state).2.clock ≤ state.clock := by
  have bound := fixClock_clock_le state (evaluate args env state)
  rw [evaluate]
  generalize h : fixClock state (evaluate args env state) = evaluated at *
  obtain ⟨result, next⟩ := evaluated
  change next.clock ≤ state.clock at bound
  cases result with
  | err error => exact bound
  | val values =>
    dsimp only
    split
    · simpa using bound
    · rename_i selected body found
      split
      · simp
      · have smaller : (decClock (ticks + 1) next).clock < state.clock := by
          simp only [decClock]
          omega
        exact Nat.le_trans (bodyClock body selected _ smaller) (Nat.le_of_lt smaller)

/-- Forcing an unevaluated thunk consumes one clock tick before entering code. -/
theorem evaluate_force_clock_step {C F : Type} (env : List Value) (state : State C F)
    (location index : Nat)
    (bodyClock : ∀ (body : Bvl.Exp) (values : List Value) (next : State C F),
      next.clock < state.clock → (evaluate [body] values next).2.clock ≤ next.clock) :
    (evaluate [.force location index] env state).2.clock ≤ state.clock := by
  rw [evaluate]
  split
  · simp
  · split
    · simp
    · simp
    · simp
    · split
      · simp
      · rename_i args body found
        split
        · simp
        · have smaller : (decClock 1 state).clock < state.clock := by
            simp only [decClock]
            omega
          exact Nat.le_trans (bodyClock body args _ smaller) (Nat.le_of_lt smaller)

/-- The source-shaped BVL evaluator does not increase its input clock. This
is a Flapjack invariant; the evaluator itself has not yet been reviewed as an
exact HOL port. -/
theorem evaluate_clock_le {C F : Type} (expressions : List Bvl.Exp) (env : List Value) (state : State C F) :
    (evaluate expressions env state).2.clock ≤ state.clock := by
  have allRanks : ∀ clock weight : Nat, ∀ (expressions : List Bvl.Exp)
      (env : List Value) (state : State C F), state.clock = clock → expsWeight expressions = weight →
      (evaluate expressions env state).2.clock ≤ state.clock := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (expressions : List Bvl.Exp) (env : List Value) (state : State C F),
            state.clock ≤ clock → expsWeight expressions < weight →
            (evaluate expressions env state).2.clock ≤ state.clock := by
          intro expressions env state clockLe weightLt
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact clockIH state.clock clockLt (expsWeight expressions) expressions env state rfl rfl
          · exact weightIH (expsWeight expressions) weightLt expressions env state clockEq rfl
        have smaller : ∀ (expressions : List Bvl.Exp) (env : List Value) (state : State C F),
            state.clock < clock → (evaluate expressions env state).2.clock ≤ state.clock := by
          intro expressions env state clockLt
          exact clockIH state.clock clockLt (expsWeight expressions) expressions env state rfl rfl
        intro expressions env state stateClock measure
        cases expressions with
        | nil => simp [evaluate]
        | cons first rest =>
          cases rest with
          | cons second tail =>
            apply evaluate_list_clock_step
            intro next nextBound
            apply exprIH (second :: tail) env next (by omega)
            simp only [expsWeight] at measure ⊢
            omega
          | nil =>
            cases first with
            | var index => simp [evaluate]; split <;> simp
            | raise body =>
              apply evaluate_raise_clock_step
              apply exprIH [body] env state (by omega)
              simp only [expsWeight, expWeight] at measure ⊢
              omega
            | handle body handler =>
              apply evaluate_handle_clock_step
              intro value next nextBound
              apply exprIH [handler] (value :: env) next (by omega)
              simp only [expsWeight, expWeight] at measure ⊢
              omega
            | «let» bindings body =>
              apply evaluate_let_clock_step
              intro newEnv next nextBound
              apply exprIH [body] newEnv next (by omega)
              simp only [expsWeight, expWeight] at measure ⊢
              omega
            | ifThenElse condition yes no =>
              apply evaluate_if_clock_step
              · intro next nextBound
                apply exprIH [yes] env next (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro next nextBound
                apply exprIH [no] env next (by omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
            | tick body =>
              apply evaluate_tick_clock_step
              by_cases zero : state.clock = 0
              · apply exprIH [body] env (decClock 1 state) (by simp [decClock]; omega)
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · apply smaller [body] env (decClock 1 state)
                simp [decClock]
                omega
            | call ticks location args =>
              apply evaluate_call_clock_step
              intro body values next nextLt
              exact smaller [body] values next (by omega)
            | force location index =>
              apply evaluate_force_clock_step
              intro body values next nextLt
              exact smaller [body] values next (by omega)
            | op op args => exact evaluate_op_clock env state op args
  exact allRanks state.clock (expsWeight expressions) expressions env state rfl rfl

/-- The termination-only clamp is inert on BVL evaluation results. -/
theorem fixClock_evaluate {C F : Type} (expressions : List Bvl.Exp)
    (env : List Value) (state : State C F) :
    fixClock state (evaluate expressions env state) = evaluate expressions env state := by
  have bound := evaluate_clock_le expressions env state
  cases run : evaluate expressions env state with
  | mk result next =>
    simp only [run] at bound
    simp [fixClock, Nat.min_eq_right bound]

end Flapjack.Compiler.Backend.BvlSem
