module

public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateControl

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
@[expose] public section

/-! Control restoration after evaluating a forced thunk. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- A callee that returns with its entry stack and handler intact can pop the
saved caller frame to restore both fields. This is auxiliary infrastructure. -/
theorem popEnv_call_preserves_control {C F : Type} (state bodyNext next : State C F)
    (args : List Value) (size : Option Nat) (env : Spt Value) (hasHandler : Bool)
    (stack : bodyNext.stack = (callEnv args size (pushEnv env hasHandler (decClock state))).stack)
    (handler : bodyNext.handler = (callEnv args size (pushEnv env hasHandler (decClock state))).handler)
    (pop : popEnv bodyNext = some next) :
    next.stack = state.stack ∧ next.handler = state.handler := by
  cases hasHandler <;> simp [popEnv, stack, handler, callEnv, pushEnv, decClock] at pop
  all_goals subst next
  all_goals simp

/-- Jumping from a call entry with a fresh handler selects the frame just
pushed for that call. This is auxiliary infrastructure for handled calls. -/
theorem jumpExc_callEnv_push_handler {C F : Type} (state : State C F)
    (args : List Value) (size : Option Nat) (env : Spt Value) :
    jumpExc (callEnv args size (pushEnv env true (decClock state))) =
      some { (callEnv args size (pushEnv env true (decClock state))) with
        stack := state.stack, handler := state.handler, locals := env, localsSize := state.localsSize } := by
  simp [jumpExc, callEnv, pushEnv, decClock]

/-- A continuing force restores its caller's control state, provided that
the invoked body preserves control when it returns values. The premise is the
still-open returned-value part of the general evaluator theorem. -/
theorem evaluate_force_stack_handler {C F : Type} (ret : Option (Nat × NumSet)) (label src : Nat)
    (state next : State C F)
    (bodyControl : ∀ (body : DataLang.Prog) (entered finished : State C F) (values : List Value),
      entered.clock < state.clock → evaluate body entered = (some (.val values), finished) →
      finished.stack = entered.stack ∧ finished.handler = entered.handler)
    (run : evaluate (.force ret label src) state = (none, next)) :
    next.stack = state.stack ∧ next.handler = state.handler := by
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
          | some env =>
            simp [evaluate, read, inspect, cut] at run
            subst next
            exact ⟨rfl, rfl⟩
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
              | mk outcome last =>
                cases outcome <;> simp [evaluate, read, inspect, found, zero, called] at run
          | some pair =>
            obtain ⟨dest, names⟩ := pair
            cases cut : cutEnv names state.locals with
            | none => simp [evaluate, read, inspect, found, cut] at run
            | some env =>
              by_cases zero : state.clock = 0
              · simp [evaluate, read, inspect, found, cut, zero] at run
              · let entered := callEnv args size (pushEnv env false (decClock state))
                have smaller : entered.clock < state.clock := by
                  simp [entered, callEnv, pushEnv, decClock]
                  omega
                cases called : fixClock entered (evaluate body entered) with
                | mk outcome last =>
                  have bodyRun : evaluate body entered = (outcome, last) := by
                    simpa [fixClock_evaluate] using called
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
                            have control := bodyControl body entered last [result] smaller bodyRun
                            have restored := popEnv_call_preserves_control state last final args size env false
                              control.1 control.2 popped
                            simp [evaluate, read, inspect, found, cut, zero, called, popped] at run
                            subst next
                            exact restored

end Flapjack.Compiler.Backend.DataSem
