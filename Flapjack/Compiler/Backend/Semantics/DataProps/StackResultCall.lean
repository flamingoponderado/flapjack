import Flapjack.Compiler.Backend.Semantics.DataProps.StackResultForce

/-! Result-sensitive control for calls and exception handlers. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- The result invariant for a call follows from the invariant for callee
and handler evaluations at smaller clocks. This is auxiliary induction
infrastructure, not yet the general HOL evaluator theorem. -/
theorem evaluate_call_stackResult {C F : Type} (ret : Option (List Nat × NumSet)) (dest : Option Nat)
    (names : List Nat) (handler : Option (Nat × DataLang.Prog)) (state next : State C F)
    (result : Option (Result (List Value) Value))
    (bodyIH : ∀ (body : DataLang.Prog) (entered finished : State C F) (outcome : Option (Result (List Value) Value)),
      entered.clock < state.clock → evaluate body entered = (outcome, finished) → stackResult entered outcome finished)
    (run : evaluate (.call ret dest names handler) state = (result, next)) : stackResult state result next := by
  cases result with
  | none =>
    apply evaluate_call_stack_handler ret dest names handler state next
    · intro body entered finished values smaller called
      exact bodyIH body entered finished (some (.val values)) smaller called
    · intro body entered finished value smaller called
      exact bodyIH body entered finished (some (.err (.raise value))) smaller called
    · intro body entered finished smaller called
      exact bodyIH body entered finished none smaller called
    · exact run
  | some result =>
    cases read : getVars names state.locals with
    | none =>
      simp [evaluate, read] at run
      obtain ⟨rfl, rfl⟩ := run
      trivial
    | some values =>
      cases found : findCode dest values state.code state.stackFrameSizes with
      | none =>
        simp [evaluate, read, found] at run
        obtain ⟨rfl, rfl⟩ := run
        trivial
      | some triple =>
        obtain ⟨args, body, size⟩ := triple
        cases ret with
        | none =>
          cases handler with
          | some h =>
            simp [evaluate, read, found] at run
            obtain ⟨rfl, rfl⟩ := run
            trivial
          | none =>
            by_cases zero : state.clock = 0
            · simp [evaluate, read, found, zero] at run
              obtain ⟨rfl, rfl⟩ := run
              trivial
            · let entered := callEnv args size (decClock state)
              have smaller : entered.clock < state.clock := by simp [entered, callEnv, decClock]; omega
              cases called : evaluate body entered with
              | mk outcome last =>
                have bodyControl := bodyIH body entered last outcome smaller called
                simp only [entered] at called
                cases outcome with
                | none =>
                  simp [evaluate, read, found, zero, called] at run
                  obtain ⟨rfl, rfl⟩ := run
                  trivial
                | some value =>
                  simp [evaluate, read, found, zero, called] at run
                  obtain ⟨rfl, rfl⟩ := run
                  exact stackResult_transport state entered last (some value) rfl rfl bodyControl
        | some pair =>
          obtain ⟨returns, live⟩ := pair
          by_cases nodup : returns.Nodup
          · cases cut : cutEnv live state.locals with
            | none =>
              simp [evaluate, read, found, nodup, cut] at run
              obtain ⟨rfl, rfl⟩ := run
              trivial
            | some env =>
              by_cases zero : state.clock = 0
              · simp [evaluate, read, found, nodup, cut, zero] at run
                obtain ⟨rfl, rfl⟩ := run
                trivial
              · let entered := callEnv args size (pushEnv env handler.isSome (decClock state))
                have smaller : entered.clock < state.clock := by simp [entered, callEnv, pushEnv, decClock]; omega
                cases called : fixClock entered (evaluate body entered) with
                | mk outcome last =>
                  have bodyRun : evaluate body entered = (outcome, last) := by simpa [fixClock_evaluate] using called
                  have bodyControl := bodyIH body entered last outcome smaller bodyRun
                  have lastClock : last.clock < state.clock := by
                    have bound := evaluate_clock_le body entered
                    rw [bodyRun] at bound
                    exact Nat.lt_of_le_of_lt bound smaller
                  simp only [entered] at called
                  cases outcome with
                  | none =>
                    simp [evaluate, read, found, nodup, cut, zero, called] at run
                    obtain ⟨rfl, rfl⟩ := run
                    trivial
                  | some outcome =>
                    cases outcome with
                    | val returned =>
                      by_cases length : returned.length = returns.length
                      · cases popped : popEnv last with
                        | none =>
                          simp [evaluate, read, found, nodup, cut, zero, called, length, popped] at run
                          obtain ⟨rfl, rfl⟩ := run
                          trivial
                        | some final => simp [evaluate, read, found, nodup, cut, zero, called, length, popped] at run
                      · simp [evaluate, read, found, nodup, cut, zero, called, length] at run
                        obtain ⟨rfl, rfl⟩ := run
                        trivial
                    | err error =>
                      cases error with
                      | abort reason =>
                        simp [evaluate, read, found, nodup, cut, zero, called] at run
                        obtain ⟨rfl, rfl⟩ := run
                        trivial
                      | raise raised =>
                        cases handler with
                        | none =>
                          simp only [Option.isSome] at called
                          simp [evaluate, read, found, nodup, cut, zero, called] at run
                          obtain ⟨rfl, rfl⟩ := run
                          obtain ⟨jumped, jumpRun, afterStack, afterHandler⟩ := bodyControl
                          obtain ⟨original, originalRun, jumpedStack, jumpedHandler⟩ :=
                            jumpExc_callEnv_push_noHandler_inv state jumped env args size jumpRun
                          exact ⟨original, originalRun, afterStack.trans jumpedStack, afterHandler.trans jumpedHandler⟩
                        | some pair =>
                          obtain ⟨name, handlerBody⟩ := pair
                          simp only [Option.isSome] at called
                          obtain ⟨jumped, jumpRun, afterStack, afterHandler⟩ := bodyControl
                          have expected := jumpExc_callEnv_push_handler state args size env
                          have jumpEq : jumped = { entered with stack := state.stack, handler := state.handler, locals := env, localsSize := state.localsSize } := by
                            apply Option.some.inj
                            rw [← jumpRun]
                            simpa [entered] using expected
                          have handlerRun : evaluate handlerBody (setVar name raised last) = (some result, next) := by
                            simpa [evaluate, read, found, nodup, cut, zero, called] using run
                          have handlerControl := bodyIH handlerBody (setVar name raised last) next (some result)
                            (by simpa [setVar] using lastClock) handlerRun
                          apply stackResult_transport state (setVar name raised last) next (some result)
                          · simpa [setVar, jumpEq] using afterStack
                          · simpa [setVar, jumpEq] using afterHandler
                          · exact handlerControl
          · simp [evaluate, read, found, nodup] at run
            obtain ⟨rfl, rfl⟩ := run
            trivial

end Flapjack.Compiler.Backend.DataSem
