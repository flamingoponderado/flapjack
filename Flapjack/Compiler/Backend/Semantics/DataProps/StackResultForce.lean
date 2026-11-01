import Flapjack.Compiler.Backend.Semantics.DataProps.StackResultPrimitive
import Flapjack.Compiler.Backend.Semantics.DataProps.JumpPush

/-! Result-sensitive control for forced thunk execution. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- The result invariant transfers between entry states with identical stack
and handler. This auxiliary lemma has no direct HOL counterpart. -/
theorem stackResult_transport {C F : Type} (source entered next : State C F)
    (result : Option (Result (List Value) Value))
    (stack : entered.stack = source.stack) (handler : entered.handler = source.handler)
    (control : stackResult entered result next) : stackResult source result next := by
  cases result with
  | none => exact ⟨control.1.trans stack, control.2.trans handler⟩
  | some result =>
    cases result with
    | val values => exact ⟨control.1.trans stack, control.2.trans handler⟩
    | err error =>
      cases error with
      | abort reason => trivial
      | raise value =>
        obtain ⟨jumped, run, afterStack, afterHandler⟩ := control
        let oldJump := { source with stack := jumped.stack, handler := jumped.handler, locals := jumped.locals, localsSize := jumped.localsSize }
        refine ⟨oldJump, jumpExc_transport entered source jumped stack.symm handler.symm run, ?_, ?_⟩
        · simpa [oldJump] using afterStack
        · simpa [oldJump] using afterHandler

/-- The full result invariant for a force follows from the invariant for
thunk bodies at smaller clocks. This is auxiliary induction infrastructure,
not yet a port of the general HOL evaluator theorem. -/
theorem evaluate_force_stackResult {C F : Type} (ret : Option (Nat × NumSet)) (label src : Nat)
    (state next : State C F) (result : Option (Result (List Value) Value))
    (bodyIH : ∀ (body : DataLang.Prog) (entered finished : State C F) (outcome : Option (Result (List Value) Value)),
      entered.clock < state.clock → evaluate body entered = (outcome, finished) → stackResult entered outcome finished)
    (run : evaluate (.force ret label src) state = (result, next)) : stackResult state result next := by
  cases result with
  | none =>
    apply evaluate_force_stack_handler ret label src state next
    · intro body entered finished values smaller called
      exact bodyIH body entered finished (some (.val values)) smaller called
    · exact run
  | some result =>
    cases read : getVar src state.locals with
    | none =>
      simp [evaluate, read] at run
      obtain ⟨rfl, rfl⟩ := run
      trivial
    | some thunk =>
      cases inspect : destThunk thunk state.refs with
      | badRef =>
        simp [evaluate, read, inspect] at run
        obtain ⟨rfl, rfl⟩ := run
        trivial
      | notThunk =>
        simp [evaluate, read, inspect] at run
        obtain ⟨rfl, rfl⟩ := run
        trivial
      | isThunk mode value =>
        cases mode with
        | evaluated =>
          cases ret with
          | none =>
            simp [evaluate, read, inspect] at run
            obtain ⟨rfl, rfl⟩ := run
            exact ⟨rfl, rfl⟩
          | some pair =>
            obtain ⟨dest, names⟩ := pair
            cases cut : cutEnv names state.locals with
            | none =>
              simp [evaluate, read, inspect, cut] at run
              obtain ⟨rfl, rfl⟩ := run
              trivial
            | some env => simp [evaluate, read, inspect, cut] at run
        | notEvaluated =>
          cases found : findCode (some label) [thunk, value] state.code state.stackFrameSizes with
          | none =>
            simp [evaluate, read, inspect, found] at run
            obtain ⟨rfl, rfl⟩ := run
            trivial
          | some triple =>
            obtain ⟨args, body, size⟩ := triple
            cases ret with
            | none =>
              by_cases zero : state.clock = 0
              · simp [evaluate, read, inspect, found, zero] at run
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
                    simp [evaluate, read, inspect, found, zero, called] at run
                    obtain ⟨rfl, rfl⟩ := run
                    trivial
                  | some value =>
                    simp [evaluate, read, inspect, found, zero, called] at run
                    obtain ⟨rfl, rfl⟩ := run
                    exact stackResult_transport state entered last (some value) rfl rfl bodyControl
            | some pair =>
              obtain ⟨dest, names⟩ := pair
              cases cut : cutEnv names state.locals with
              | none =>
                simp [evaluate, read, inspect, found, cut] at run
                obtain ⟨rfl, rfl⟩ := run
                trivial
              | some env =>
                by_cases zero : state.clock = 0
                · simp [evaluate, read, inspect, found, cut, zero] at run
                  obtain ⟨rfl, rfl⟩ := run
                  trivial
                · let entered := callEnv args size (pushEnv env false (decClock state))
                  have smaller : entered.clock < state.clock := by simp [entered, callEnv, pushEnv, decClock]; omega
                  cases called : fixClock entered (evaluate body entered) with
                  | mk outcome last =>
                    have bodyRun : evaluate body entered = (outcome, last) := by simpa [fixClock_evaluate] using called
                    have bodyControl := bodyIH body entered last outcome smaller bodyRun
                    simp only [entered] at called
                    cases outcome with
                    | none =>
                      simp [evaluate, read, inspect, found, cut, zero, called] at run
                      obtain ⟨rfl, rfl⟩ := run
                      trivial
                    | some outcome =>
                      cases outcome with
                      | val values =>
                        cases values with
                        | nil =>
                          simp [evaluate, read, inspect, found, cut, zero, called] at run
                          obtain ⟨rfl, rfl⟩ := run
                          trivial
                        | cons first rest =>
                          cases rest with
                          | cons second rest =>
                            simp [evaluate, read, inspect, found, cut, zero, called] at run
                            obtain ⟨rfl, rfl⟩ := run
                            trivial
                          | nil =>
                            cases popped : popEnv last with
                            | none =>
                              simp [evaluate, read, inspect, found, cut, zero, called, popped] at run
                              obtain ⟨rfl, rfl⟩ := run
                              trivial
                            | some final => simp [evaluate, read, inspect, found, cut, zero, called, popped] at run
                      | err error =>
                        cases error with
                        | abort reason =>
                          simp [evaluate, read, inspect, found, cut, zero, called] at run
                          obtain ⟨rfl, rfl⟩ := run
                          trivial
                        | raise raised =>
                          simp [evaluate, read, inspect, found, cut, zero, called] at run
                          obtain ⟨rfl, rfl⟩ := run
                          obtain ⟨jumped, jumpRun, afterStack, afterHandler⟩ := bodyControl
                          obtain ⟨original, originalRun, jumpedStack, jumpedHandler⟩ :=
                            jumpExc_callEnv_push_noHandler_inv state jumped env args size jumpRun
                          exact ⟨original, originalRun, afterStack.trans jumpedStack, afterHandler.trans jumpedHandler⟩

end Flapjack.Compiler.Backend.DataSem
