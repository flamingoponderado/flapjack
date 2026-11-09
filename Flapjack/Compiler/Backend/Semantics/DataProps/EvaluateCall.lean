module

public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateForce

@[expose] public section

/-! Control restoration for calls and their handlers. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- A continuing call restores the caller's stack and handler. The recursive
premises are the value, exception and continuing cases of the general
evaluator invariant, which remains an open proof obligation. -/
theorem evaluate_call_stack_handler {C F : Type} (ret : Option (List Nat × NumSet)) (dest : Option Nat)
    (names : List Nat) (handler : Option (Nat × DataLang.Prog)) (state next : State C F)
    (valueControl : ∀ (body : DataLang.Prog) (entered finished : State C F) (values : List Value),
      entered.clock < state.clock → evaluate body entered = (some (.val values), finished) →
      finished.stack = entered.stack ∧ finished.handler = entered.handler)
    (raiseControl : ∀ (body : DataLang.Prog) (entered finished : State C F) (value : Value),
      entered.clock < state.clock → evaluate body entered = (some (.err (.raise value)), finished) →
      ∃ jumped, jumpExc entered = some jumped ∧ finished.stack = jumped.stack ∧ finished.handler = jumped.handler)
    (normalControl : ∀ (body : DataLang.Prog) (entered finished : State C F),
      entered.clock < state.clock → evaluate body entered = (none, finished) →
      finished.stack = entered.stack ∧ finished.handler = entered.handler)
    (run : evaluate (.call ret dest names handler) state = (none, next)) :
    next.stack = state.stack ∧ next.handler = state.handler := by
  cases read : getVars names state.locals with
  | none => simp [evaluate, read] at run
  | some values =>
    cases found : findCode dest values state.code state.stackFrameSizes with
    | none => simp [evaluate, read, found] at run
    | some triple =>
      obtain ⟨args, body, size⟩ := triple
      cases ret with
      | none =>
        cases handler with
        | some h => simp [evaluate, read, found] at run
        | none =>
          by_cases zero : state.clock = 0
          · simp [evaluate, read, found, zero] at run
          · cases called : evaluate body (callEnv args size (decClock state)) with
            | mk result last => cases result <;> simp [evaluate, read, found, zero, called] at run
      | some pair =>
        obtain ⟨returns, live⟩ := pair
        by_cases nodup : returns.Nodup
        · cases cut : cutEnv live state.locals with
          | none => simp [evaluate, read, found, nodup, cut] at run
          | some env =>
            by_cases zero : state.clock = 0
            · simp [evaluate, read, found, nodup, cut, zero] at run
            · let entered := callEnv args size (pushEnv env handler.isSome (decClock state))
              have smaller : entered.clock < state.clock := by
                simp [entered, callEnv, pushEnv, decClock]
                omega
              cases called : fixClock entered (evaluate body entered) with
              | mk result last =>
                have bodyRun : evaluate body entered = (result, last) := by
                  simpa [fixClock_evaluate] using called
                have lastClock : last.clock < state.clock := by
                  have bound := evaluate_clock_le body entered
                  rw [bodyRun] at bound
                  exact Nat.lt_of_le_of_lt bound smaller
                simp only [entered] at called
                cases result with
                | none => simp [evaluate, read, found, nodup, cut, zero, called] at run
                | some outcome =>
                  cases outcome with
                  | val returned =>
                    by_cases length : returned.length = returns.length
                    · cases popped : popEnv last with
                      | none => simp [evaluate, read, found, nodup, cut, zero, called, length, popped] at run
                      | some final =>
                        have control := valueControl body entered last returned smaller bodyRun
                        have restored := popEnv_call_preserves_control state last final args size env handler.isSome
                          control.1 control.2 popped
                        simp [evaluate, read, found, nodup, cut, zero, called, length, popped] at run
                        subst next
                        exact restored
                    · simp [evaluate, read, found, nodup, cut, zero, called, length] at run
                  | err error =>
                    cases error with
                    | abort reason => simp [evaluate, read, found, nodup, cut, zero, called] at run
                    | raise value =>
                      cases handler with
                      | none =>
                        simp only [Option.isSome] at called
                        simp [evaluate, read, found, nodup, cut, zero, called] at run
                      | some pair =>
                        obtain ⟨name, handlerBody⟩ := pair
                        simp only [Option.isSome] at called
                        have raised := raiseControl body entered last value smaller bodyRun
                        obtain ⟨jumped, jumpRun, jumpStack, jumpHandler⟩ := raised
                        have expected := jumpExc_callEnv_push_handler state args size env
                        have jumpEq : jumped = { entered with stack := state.stack, handler := state.handler, locals := env, localsSize := state.localsSize } := by
                          apply Option.some.inj
                          rw [← jumpRun]
                          simpa [entered] using expected
                        have handlerRun : evaluate handlerBody (setVar name value last) = (none, next) := by
                          simpa [evaluate, read, found, nodup, cut, zero, called] using run
                        have finalControl := normalControl handlerBody (setVar name value last) next (by simpa [setVar] using lastClock) handlerRun
                        constructor
                        · simpa [setVar, jumpEq] using finalControl.1.trans jumpStack
                        · simpa [setVar, jumpEq] using finalControl.2.trans jumpHandler
        · simp [evaluate, read, found, nodup] at run

end Flapjack.Compiler.Backend.DataSem
