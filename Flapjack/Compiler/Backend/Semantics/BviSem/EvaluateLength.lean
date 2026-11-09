import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateClockFull
import Flapjack.Misc.ClockWeightInduction

/-! Successful-result length for the proof-side BVI evaluator. -/
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value unitValue)

/-- Every successful BVI evaluation returns one value per expression. The
evaluator remains untagged pending HOL correspondence review. -/
theorem evaluate_length {C F : Type} (expressions : List Bvi.Exp) (env : List Value)
    (state next : BviState C F) (values : List Value)
    (run : evaluate expressions env state = (.val values, next)) :
    values.length = expressions.length := by
  refine clockWeightInduction (α := List Bvi.Exp) (σ := BviState C F) (·.clock) expsWeight
    (motive := fun expressions state => ∀ env next values,
      evaluate expressions env state = (.val values, next) → values.length = expressions.length) ?_
    expressions state env next values run
  intro expressions state exprIH₀ smaller₀
  have exprIH := fun (es : List Bvi.Exp) (env' : List Value) (s next : BviState C F)
      (values' : List Value) h1 h2 run =>
    exprIH₀ es s h1 h2 env' next values' run
  have smaller := fun (es : List Bvi.Exp) (env' : List Value) (s next : BviState C F)
      (values' : List Value) h1 run =>
    smaller₀ es s h1 env' next values' run
  intro env next values run
  cases expressions with
  | nil => simp [evaluate] at run; rcases run with ⟨rfl, _⟩; rfl
  | cons first rest =>
    cases rest with
    | cons second tail =>
      have headBound := evaluate_clock_le [first] env state
      rw [evaluate, fixClock_evaluate] at run
      cases headRun : evaluate [first] env state with
      | mk headResult headNext =>
        simp only [headRun] at run headBound
        cases headResult with
        | err error => simp at run
        | val headValues =>
          cases tailRun : evaluate (second :: tail) env headNext with
          | mk tailResult tailNext =>
            simp only [tailRun] at run
            cases tailResult with
            | err error => simp at run
            | val tailValues =>
              simp at run
              rcases run with ⟨rfl, _⟩
              have tailLength := exprIH (second :: tail) env headNext tailNext tailValues (by omega)
                (by
                simp only [expsWeight] at ⊢; omega) tailRun
              simpa using congrArg Nat.succ tailLength
    | nil =>
      cases first with
      | var index =>
        simp [evaluate] at run
        split at run <;> simp_all
        rcases run with ⟨rfl, _⟩
        rfl
      | raise body =>
        rw [evaluate] at run
        cases bodyRun : evaluate [body] env state with
        | mk bodyResult bodyNext =>
          rw [bodyRun] at run
          cases bodyResult <;> simp at run
      | tick body =>
        rw [evaluate] at run
        split at run
        · simp at run
        · have bodyRun : evaluate [body] env (decClock 1 state) = (.val values, next) := run
          have one := smaller [body] env (decClock 1 state) next values (by simp [decClock]; omega)
            bodyRun
          simpa using one
      | «let» bindings body =>
        have bound := evaluate_clock_le bindings env state
        rw [evaluate, fixClock_evaluate] at run
        cases bindingRun : evaluate bindings env state with
        | mk result last =>
          simp only [bindingRun] at run bound
          cases result with
          | err error => simp at run
          | val bindingValues =>
            have one := exprIH [body] (bindingValues ++ env) last next values (by omega) (by
              simp only [expsWeight, expWeight] at ⊢; omega) run
            simpa using one
      | ifThenElse condition yes no =>
        have bound := evaluate_clock_le [condition] env state
        rw [evaluate, fixClock_evaluate] at run
        cases conditionRun : evaluate [condition] env state with
        | mk result last =>
          simp only [conditionRun] at run bound
          cases result with
          | err error => simp at run
          | val conditionValues =>
            dsimp only at run
            split at run
            · simp at run
            · have one := exprIH [yes] env last next values (by omega) (by
                simp only [expsWeight, expWeight] at ⊢; omega) run
              simpa using one
            · have one := exprIH [no] env last next values (by omega) (by
                simp only [expsWeight, expWeight] at ⊢; omega) run
              simpa using one
      | «return» args =>
        rw [evaluate] at run
        cases argsRun : evaluate args env state with
        | mk result last =>
          rw [argsRun] at run
          cases result <;> simp at run
      | call ticks location args handler =>
        have bound := evaluate_clock_le args env state
        rw [evaluate] at run
        split at run
        · simp at run
        · rw [fixClock_evaluate] at run
          cases argsRun : evaluate args env state with
          | mk result last =>
            simp only [argsRun] at run bound
            cases result with
            | err error => simp at run
            | val arguments =>
              dsimp only at run
              split at run
              · simp at run
              · rename_i selected body found
                split at run
                · simp at run
                · rw [fixClock_evaluate] at run
                  have callLt : (decClock (ticks + 1) last).clock < state.clock := by
                    simp only [decClock]; omega
                  have callBound := evaluate_clock_le [body] selected (decClock (ticks + 1) last)
                  cases bodyRun : evaluate [body] selected (decClock (ticks + 1) last) with
                  | mk result called =>
                    simp only [bodyRun] at run callBound
                    have calledLt : called.clock < state.clock := by omega
                    cases result with
                    | val returned =>
                      simp at run
                      rcases run with ⟨rfl, rfl⟩
                      simpa using smaller [body] selected (decClock (ticks + 1) last) called
                        returned callLt bodyRun
                    | err error =>
                      cases error with
                      | abort reason => simp at run
                      | raise result =>
                        cases result with
                        | ret returned => simp at run
                        | exn value =>
                          cases handler with
                          | none => simp at run
                          | some handler =>
                            dsimp only at run
                            cases handlerRun : evaluate [handler] (value :: env) called with
                            | mk result final =>
                              rw [handlerRun] at run
                              cases result with
                              | val returned =>
                                simp at run
                                rcases run with ⟨rfl, rfl⟩
                                simpa using smaller [handler] (value :: env) called final returned
                                  calledLt handlerRun
                              | err error =>
                                cases error with
                                | abort reason => simp at run
                                | raise result => cases result <;> simp at run
      | letCall rets ticks dest args body =>
        have bound := evaluate_clock_le args env state
        rw [evaluate, fixClock_evaluate] at run
        cases argsRun : evaluate args env state with
        | mk result last =>
          simp only [argsRun] at run bound
          cases result with
          | err error => simp at run
          | val arguments =>
            dsimp only at run
            split at run
            · simp at run
            · rename_i selected callee found
              split at run
              · simp at run
              · rw [fixClock_evaluate] at run
                have callLt : (decClock (ticks + 1) last).clock < state.clock := by
                  simp only [decClock]; omega
                have callBound := evaluate_clock_le [callee] selected (decClock (ticks + 1) last)
                cases bodyRun : evaluate [callee] selected (decClock (ticks + 1) last) with
                | mk result called =>
                  simp only [bodyRun] at run callBound
                  have calledLt : called.clock < state.clock := by omega
                  cases result with
                  | val returned => simp at run
                  | err error =>
                    cases error with
                    | abort reason => simp at run
                    | raise result =>
                      cases result with
                      | exn value => simp at run
                      | ret returned =>
                        dsimp only at run
                        split at run
                        · have one := smaller [body] (returned ++ env) called next values calledLt
                            run
                          simpa using one
                        · simp at run
      | op op args =>
        rw [evaluate, fixClock_evaluate] at run
        cases argsRun : evaluate args env state with
        | mk result last =>
          rw [argsRun] at run
          cases result with
          | err error => simp at run
          | val arguments =>
            cases appRun : doApp op arguments.reverse last with
            | err error => simp [appRun] at run
            | val pair =>
              rcases pair with ⟨value, final⟩
              simp [appRun] at run
              rcases run with ⟨rfl, _⟩
              rfl
      | force location index =>
        rw [evaluate] at run
        split at run
        · simp at run
        · split at run
          · simp at run
          · simp at run
          · simp at run; rcases run with ⟨rfl, _⟩; rfl
          · split at run
            · simp at run
            · rename_i arguments body found
              split at run
              · simp at run
              · have bodyLength := smaller [body] arguments (decClock 1 state) next values (by
                  simp only [decClock]; omega)
                cases bodyRun : evaluate [body] arguments (decClock 1 state) with
                | mk result last =>
                  rw [bodyRun] at run
                  cases result with
                  | val bodyValues =>
                    simp at run
                    rcases run with ⟨rfl, rfl⟩
                    simpa using bodyLength bodyRun
                  | err error =>
                    cases error with
                    | abort reason => simp at run
                    | raise result => cases result <;> simp at run

/-- A successful singleton evaluation produces exactly one value. -/
theorem evaluate_singleton {C F : Type} (expression : Bvi.Exp) (env : List Value)
    (state next : BviState C F) (values : List Value)
    (run : evaluate [expression] env state = (.val values, next)) :
    ∃ value, values = [value] := by
  have length := evaluate_length [expression] env state next values run
  cases values with
  | nil => simp at length
  | cons value tail =>
    cases tail with
    | nil => exact ⟨value, rfl⟩
    | cons other tail => simp at length

end Flapjack.Compiler.Backend.BviSem
