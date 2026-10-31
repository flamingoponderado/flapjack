import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateCallEventsClock

/-! Cross-clock trace monotonicity for the complete BVI evaluator. -/
namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.Compiler.Backend.BviSem

/-- Increasing the evaluation clock extends its I/O trace. This is untagged
until the evaluator and dispatcher have been reviewed against HOL. -/
theorem evaluate_addClock_ioEvents_prefix {C F : Type} (expressions : List Bvi.Exp)
    (env : List Value) (state : BviState C F) (extra : Nat) :
    (evaluate expressions env state).2.ffi.ioEvents <+:
      (evaluate expressions env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  have allRanks : ∀ clock weight : Nat, ∀ (expressions : List Bvi.Exp)
      (env : List Value) (state : BviState C F), state.clock = clock → expsWeight expressions = weight →
      ∀ extra, (evaluate expressions env state).2.ffi.ioEvents <+:
        (evaluate expressions env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (expressions : List Bvi.Exp) (env : List Value) (state : BviState C F),
            state.clock ≤ clock → expsWeight expressions < weight → ∀ extra,
            (evaluate expressions env state).2.ffi.ioEvents <+:
              (evaluate expressions env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
          intro expressions env state clockLe weightLt extra
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact clockIH state.clock clockLt (expsWeight expressions) expressions env state rfl rfl extra
          · exact weightIH (expsWeight expressions) weightLt expressions env state clockEq rfl extra
        have smaller : ∀ (expressions : List Bvi.Exp) (env : List Value) (state : BviState C F),
            state.clock < clock → ∀ extra, (evaluate expressions env state).2.ffi.ioEvents <+:
              (evaluate expressions env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
          intro expressions env state clockLt extra
          exact clockIH state.clock clockLt (expsWeight expressions) expressions env state rfl rfl extra
        intro expressions env state stateClock measure extra
        cases expressions with
        | nil => simp [evaluate]
        | cons first rest =>
          cases rest with
          | cons second tail =>
            apply evaluate_list_addClock_ioEvents_step first second tail env state extra ?_ ?_
            · apply exprIH [first] env state (by omega) ?_ extra
              simp only [expsWeight] at measure ⊢; have := expWeight_pos second; omega
            · intro start bound
              apply exprIH (second :: tail) env start (by omega) ?_ extra
              simp only [expsWeight] at measure ⊢; omega
          | nil =>
            cases first with
            | var index =>
              rw [evaluate, evaluate]
              split <;> simp
            | raise body =>
              apply evaluate_raise_addClock_ioEvents_step body env state extra
              apply exprIH [body] env state (by omega) ?_ extra
              simp only [expsWeight, expWeight] at measure ⊢; omega
            | tick body =>
              apply evaluate_tick_addClock_ioEvents_step body env state extra
              intro start bound
              exact smaller [body] env start (by omega) extra
            | «let» bindings body =>
              apply evaluate_let_addClock_ioEvents_step bindings body env state extra ?_ ?_
              · apply exprIH bindings env state (by omega) ?_ extra
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro bodyEnv start bound
                apply exprIH [body] bodyEnv start (by omega) ?_ extra
                simp only [expsWeight, expWeight] at measure ⊢; omega
            | «return» args =>
              apply evaluate_return_addClock_ioEvents_step args env state extra
              apply exprIH args env state (by omega) ?_ extra
              simp only [expsWeight, expWeight] at measure ⊢; omega
            | ifThenElse condition yes no =>
              apply evaluate_if_addClock_ioEvents_step condition yes no env state extra ?_ ?_
              · apply exprIH [condition] env state (by omega) ?_ extra
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro choice start bound
                apply exprIH [if choice then yes else no] env start (by omega) ?_ extra
                cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte, expsWeight, expWeight] at measure ⊢ <;> omega
            | op op args =>
              apply evaluate_op_addClock_ioEvents_step op args env state extra
              apply exprIH args env state (by omega) ?_ extra
              simp only [expsWeight, expWeight] at measure ⊢; omega
            | call ticks location args handler =>
              cases handler with
              | none =>
                apply evaluate_directCall_addClock_ioEvents_step ticks location args env state extra ?_ ?_
                · apply exprIH args env state (by omega) ?_ extra
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro body bodyEnv start bound
                  exact smaller [body] bodyEnv start (by omega) extra
              | some handler =>
                cases location with
                | none => simp [evaluate]
                | some dest =>
                  apply evaluate_handledCall_addClock_ioEvents_step ticks dest args handler env state extra ?_ ?_ ?_
                  · apply exprIH args env state (by omega) ?_ extra
                    simp only [expsWeight, expWeight] at measure ⊢; omega
                  · intro body bodyEnv start bound
                    exact smaller [body] bodyEnv start (by omega) extra
                  · intro bodyEnv start bound
                    exact smaller [handler] bodyEnv start (by omega) extra
            | letCall rets ticks dest args body =>
              apply evaluate_letCall_addClock_ioEvents_step rets ticks dest args body env state extra ?_ ?_ ?_
              · apply exprIH args env state (by omega) ?_ extra
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro callee calleeEnv start bound
                exact smaller [callee] calleeEnv start (by omega) extra
              · intro bodyEnv start bound
                exact smaller [body] bodyEnv start (by omega) extra
            | force location index =>
              apply evaluate_force_addClock_ioEvents_step location index env state extra
              intro body bodyEnv start bound
              exact smaller [body] bodyEnv start (by omega) extra
  exact allRanks state.clock (expsWeight expressions) expressions env state rfl rfl extra

end Flapjack.Compiler.Backend.BviProps
