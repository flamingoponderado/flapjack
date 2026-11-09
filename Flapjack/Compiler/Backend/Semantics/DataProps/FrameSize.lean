module

public import Flapjack.Compiler.Backend.Semantics.DataProps.StackResultAll

@[expose] public section

/-! Restoration of the caller's local frame size. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Popping the saved call frame restores its caller's local frame size. -/
theorem popEnv_call_preserves_localsSize {C F : Type} (state bodyNext next : State C F)
    (args : List Value) (size : Option Nat) (env : Spt Value) (hasHandler : Bool)
    (stack : bodyNext.stack = (callEnv args size (pushEnv env hasHandler (decClock state))).stack)
    (handler : bodyNext.handler = (callEnv args size (pushEnv env hasHandler (decClock state))).handler)
    (pop : popEnv bodyNext = some next) : next.localsSize = state.localsSize := by
  cases hasHandler <;> simp [popEnv, stack, handler, callEnv, pushEnv, decClock] at pop
  all_goals subst next
  all_goals rfl

/-- A normally continuing force restores the caller's local frame size. -/
theorem evaluate_force_normal_localsSize {C F : Type} (ret : Option (Nat × NumSet)) (label src : Nat)
    (state next : State C F) (run : evaluate (.force ret label src) state = (none, next)) :
    next.localsSize = state.localsSize := by
  cases read : getVar src state.locals with
  | none => simp [evaluate, read] at run
  | some thunk =>
    cases inspect : destThunk thunk state.refs with
    | badRef => simp [evaluate, read, inspect] at run
    | notThunk => simp [evaluate, read, inspect] at run
    | isThunk mode value =>
      cases mode with
      | evaluated =>
        cases ret with
        | none => simp [evaluate, read, inspect] at run
        | some pair =>
          obtain ⟨dest, names⟩ := pair
          cases cut : cutEnv names state.locals with
          | none => simp [evaluate, read, inspect, cut] at run
          | some env => simp [evaluate, read, inspect, cut, setVar] at run; subst next; rfl
      | notEvaluated =>
        cases found : findCode (some label) [thunk, value] state.code state.stackFrameSizes with
        | none => simp [evaluate, read, inspect, found] at run
        | some triple =>
          obtain ⟨args, body, size⟩ := triple
          cases ret with
          | none =>
            by_cases zero : state.clock = 0
            · simp [evaluate, read, inspect, found, zero] at run
            · cases called : evaluate body (callEnv args size (decClock state)) with
              | mk outcome last => cases outcome <;> simp [evaluate, read, inspect, found, zero, called] at run
          | some pair =>
            obtain ⟨dest, names⟩ := pair
            cases cut : cutEnv names state.locals with
            | none => simp [evaluate, read, inspect, found, cut] at run
            | some env =>
              by_cases zero : state.clock = 0
              · simp [evaluate, read, inspect, found, cut, zero] at run
              · let entered := callEnv args size (pushEnv env false (decClock state))
                cases called : fixClock entered (evaluate body entered) with
                | mk outcome last =>
                  have bodyRun : evaluate body entered = (outcome, last) := by simpa [fixClock_evaluate] using called
                  simp only [entered] at called
                  cases outcome with
                  | none => simp [evaluate, read, inspect, found, cut, zero, called] at run
                  | some result =>
                    cases result with
                    | err error => simp [evaluate, read, inspect, found, cut, zero, called] at run
                    | val values =>
                      cases values with
                      | nil => simp [evaluate, read, inspect, found, cut, zero, called] at run
                      | cons result rest =>
                        cases rest with
                        | cons other rest => simp [evaluate, read, inspect, found, cut, zero, called] at run
                        | nil =>
                          cases popped : popEnv last with
                          | none => simp [evaluate, read, inspect, found, cut, zero, called, popped] at run
                          | some final =>
                            have control := evaluate_stackResult body entered last (some (.val [result])) bodyRun
                            have restored := popEnv_call_preserves_localsSize state last final args size env false
                              control.1 control.2 popped
                            simp [evaluate, read, inspect, found, cut, zero, called, popped, setVar] at run
                            subst next
                            exact restored

/-- A normally continuing call with no exception handler restores the
caller's local frame size. -/
theorem evaluate_call_noHandler_normal_localsSize {C F : Type} (ret : Option (List Nat × NumSet))
    (dest : Option Nat) (names : List Nat) (state next : State C F)
    (run : evaluate (.call ret dest names none) state = (none, next)) :
    next.localsSize = state.localsSize := by
  cases read : getVars names state.locals with
  | none => simp [evaluate, read] at run
  | some values =>
    cases found : findCode dest values state.code state.stackFrameSizes with
    | none => simp [evaluate, read, found] at run
    | some triple =>
      obtain ⟨args, body, size⟩ := triple
      cases ret with
      | none =>
        by_cases zero : state.clock = 0
        · simp [evaluate, read, found, zero] at run
        · cases called : evaluate body (callEnv args size (decClock state)) with
          | mk outcome last => cases outcome <;> simp [evaluate, read, found, zero, called] at run
      | some pair =>
        obtain ⟨returns, live⟩ := pair
        by_cases nodup : returns.Nodup
        · cases cut : cutEnv live state.locals with
          | none => simp [evaluate, read, found, nodup, cut] at run
          | some env =>
            by_cases zero : state.clock = 0
            · simp [evaluate, read, found, nodup, cut, zero] at run
            · let entered := callEnv args size (pushEnv env false (decClock state))
              cases called : fixClock entered (evaluate body entered) with
              | mk outcome last =>
                have bodyRun : evaluate body entered = (outcome, last) := by simpa [fixClock_evaluate] using called
                simp only [entered] at called
                cases outcome with
                | none => simp [evaluate, read, found, nodup, cut, zero, called] at run
                | some result =>
                  cases result with
                  | err error => cases error <;> simp [evaluate, read, found, nodup, cut, zero, called] at run
                  | val returned =>
                    by_cases length : returned.length = returns.length
                    · cases popped : popEnv last with
                      | none => simp [evaluate, read, found, nodup, cut, zero, called, length, popped] at run
                      | some final =>
                        have control := evaluate_stackResult body entered last (some (.val returned)) bodyRun
                        have restored := popEnv_call_preserves_localsSize state last final args size env false
                          control.1 control.2 popped
                        simp [evaluate, read, found, nodup, cut, zero, called, length, popped, setVars] at run
                        subst next
                        exact restored
                    · simp [evaluate, read, found, nodup, cut, zero, called, length] at run
        · simp [evaluate, read, found, nodup] at run

/-- For a call with a handler, the normal result restores the caller's frame
size if raised callee results have the frame size selected by the exception
jump and the handler preserves its entry frame size. These two premises are
the remaining induction cases of the general frame-size invariant. -/
theorem evaluate_call_handler_normal_localsSize {C F : Type} (ret : Option (List Nat × NumSet))
    (dest : Option Nat) (names : List Nat) (name : Nat) (handlerBody : DataLang.Prog)
    (state next : State C F)
    (raiseSize : ∀ (body : DataLang.Prog) (entered finished : State C F) (value : Value),
      entered.clock < state.clock → evaluate body entered = (some (.err (.raise value)), finished) →
      ∃ jumped, jumpExc entered = some jumped ∧ finished.localsSize = jumped.localsSize)
    (normalSize : ∀ (body : DataLang.Prog) (entered finished : State C F),
      entered.clock < state.clock → evaluate body entered = (none, finished) →
      finished.localsSize = entered.localsSize)
    (run : evaluate (.call ret dest names (some (name, handlerBody))) state = (none, next)) :
    next.localsSize = state.localsSize := by
  cases read : getVars names state.locals with
  | none => simp [evaluate, read] at run
  | some values =>
    cases found : findCode dest values state.code state.stackFrameSizes with
    | none => simp [evaluate, read, found] at run
    | some triple =>
      obtain ⟨args, body, size⟩ := triple
      cases ret with
      | none => simp [evaluate, read, found] at run
      | some pair =>
        obtain ⟨returns, live⟩ := pair
        by_cases nodup : returns.Nodup
        · cases cut : cutEnv live state.locals with
          | none => simp [evaluate, read, found, nodup, cut] at run
          | some env =>
            by_cases zero : state.clock = 0
            · simp [evaluate, read, found, nodup, cut, zero] at run
            · let entered := callEnv args size (pushEnv env true (decClock state))
              have smaller : entered.clock < state.clock := by simp [entered, callEnv, pushEnv, decClock]; omega
              cases called : fixClock entered (evaluate body entered) with
              | mk outcome last =>
                have bodyRun : evaluate body entered = (outcome, last) := by simpa [fixClock_evaluate] using called
                have lastClock : last.clock < state.clock := by
                  have bound := evaluate_clock_le body entered
                  rw [bodyRun] at bound
                  exact Nat.lt_of_le_of_lt bound smaller
                simp only [entered] at called
                cases outcome with
                | none => simp [evaluate, read, found, nodup, cut, zero, called] at run
                | some result =>
                  cases result with
                  | val returned =>
                    by_cases length : returned.length = returns.length
                    · cases popped : popEnv last with
                      | none => simp [evaluate, read, found, nodup, cut, zero, called, length, popped] at run
                      | some final =>
                        have control := evaluate_stackResult body entered last (some (.val returned)) bodyRun
                        have restored := popEnv_call_preserves_localsSize state last final args size env true
                          control.1 control.2 popped
                        simp [evaluate, read, found, nodup, cut, zero, called, length, popped, setVars] at run
                        subst next
                        exact restored
                    · simp [evaluate, read, found, nodup, cut, zero, called, length] at run
                  | err error =>
                    cases error with
                    | abort reason => simp [evaluate, read, found, nodup, cut, zero, called] at run
                    | raise value =>
                      obtain ⟨jumped, jumpRun, lastSize⟩ := raiseSize body entered last value smaller bodyRun
                      have expected := jumpExc_callEnv_push_handler state args size env
                      have jumpEq : jumped = { entered with stack := state.stack, handler := state.handler, locals := env, localsSize := state.localsSize } := by
                        apply Option.some.inj
                        rw [← jumpRun]
                        simpa [entered] using expected
                      have handlerRun : evaluate handlerBody (setVar name value last) = (none, next) := by
                        simpa [evaluate, read, found, nodup, cut, zero, called] using run
                      have finalSize := normalSize handlerBody (setVar name value last) next (by simpa [setVar] using lastClock) handlerRun
                      simpa [setVar, jumpEq] using finalSize.trans lastSize
        · simp [evaluate, read, found, nodup] at run

end Flapjack.Compiler.Backend.DataSem
