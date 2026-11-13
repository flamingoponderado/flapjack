module

public import Flapjack.Compiler.Backend.Semantics.DataProps.StackResultAll

@[expose] public section

/-! Local-frame-size invariant for value-returning data evaluations. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- A value-returning evaluation clears its local frame size. This is an
auxiliary specialization of the source's stopped-evaluation invariant. -/
theorem evaluate_value_localsSize {C F : Type} (program : DataLang.Prog) (state next : State C F)
    (values : List Value) (run : evaluate program state = (some (.val values), next)) : next.localsSize = some 0 := by
  cases program with
  | skip => simp [evaluate] at run
  | move dest src => simp only [evaluate] at run; split at run <;> simp_all
  | assign dest op names live =>
    simp only [evaluate] at run
    repeat' (split at run <;> try simp_all)
  | tick => simp only [evaluate] at run; split at run <;> simp_all
  | makeSpace amount names => simp only [evaluate] at run; split at run <;> simp_all
  | raise name => simp only [evaluate] at run; repeat' (split at run <;> try simp_all)
  | «return» names =>
    simp only [evaluate] at run
    split at run <;> simp_all [flushState]
    obtain ⟨_, rfl⟩ := run
    rfl
  | seq first second =>
    rw [evaluate, fixClock_evaluate] at run
    cases firstRun : evaluate first state with
    | mk outcome mid =>
      rw [firstRun] at run
      cases outcome with
      | none =>
        have bound := evaluate_clock_le first state
        rw [firstRun] at bound
        change mid.clock ≤ state.clock at bound
        exact evaluate_value_localsSize second mid next values run
      | some outcome =>
        cases outcome with
        | err error => simp at run
        | val returned =>
          simp only [Prod.mk.injEq, Option.some.injEq, Result.val.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          exact evaluate_value_localsSize first state _ _ firstRun
  | ifThenElse name yes no =>
    simp only [evaluate] at run
    split at run
    · simp_all
    · split at run
      · exact evaluate_value_localsSize yes state next values run
      · split at run
        · exact evaluate_value_localsSize no state next values run
        · simp_all
  | force ret label src =>
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
          | none =>
            simp [evaluate, read, inspect] at run
            obtain ⟨_, rfl⟩ := run
            rfl
          | some pair =>
            obtain ⟨dest, names⟩ := pair
            cases cut : cutEnv names state.locals <;> simp [evaluate, read, inspect, cut] at run
        | notEvaluated =>
          cases found : findCode (some label) [thunk, value] state.code state.stackFrameSizes with
          | none => simp [evaluate, read, inspect, found] at run
          | some triple =>
            obtain ⟨args, body, size⟩ := triple
            cases ret with
            | none =>
              by_cases zero : state.clock = 0
              · simp [evaluate, read, inspect, found, zero] at run
              · cases bodyRun : evaluate body (callEnv args size (decClock state)) with
                | mk outcome last =>
                  simp [evaluate, read, inspect, found, zero, bodyRun] at run
                  cases outcome with
                  | none => simp at run
                  | some outcome =>
                    cases outcome with
                    | err error => simp at run
                    | val returned =>
                      simp at run
                      obtain ⟨rfl, rfl⟩ := run
                      exact evaluate_value_localsSize body (callEnv args size (decClock state)) _ _ bodyRun
            | some pair =>
              obtain ⟨dest, names⟩ := pair
              cases cut : cutEnv names state.locals with
              | none => simp [evaluate, read, inspect, found, cut] at run
              | some env =>
                by_cases zero : state.clock = 0
                · simp [evaluate, read, inspect, found, cut, zero] at run
                · simp only [evaluate, read, inspect, found, cut, ite_eq_right zero] at run
                  repeat' (split at run <;> try simp_all)
  | call ret dest names handler =>
    cases read : getVars names state.locals with
    | none => simp [evaluate, read] at run
    | some args =>
      cases found : findCode dest args state.code state.stackFrameSizes with
      | none => simp [evaluate, read, found] at run
      | some triple =>
        obtain ⟨params, body, size⟩ := triple
        cases ret with
        | none =>
          cases handler with
          | some pair => simp [evaluate, read, found] at run
          | none =>
            by_cases zero : state.clock = 0
            · simp [evaluate, read, found, zero] at run
            · cases bodyRun : evaluate body (callEnv params size (decClock state)) with
              | mk outcome last =>
                simp [evaluate, read, found, zero, bodyRun] at run
                cases outcome with
                | none => simp at run
                | some outcome =>
                  cases outcome with
                  | err error => simp at run
                  | val returned =>
                    simp at run
                    obtain ⟨rfl, rfl⟩ := run
                    exact evaluate_value_localsSize body (callEnv params size (decClock state)) _ _ bodyRun
        | some pair =>
          obtain ⟨returns, live⟩ := pair
          by_cases unique : returns.Nodup
          · cases cut : cutEnv live state.locals with
            | none => simp [evaluate, read, found, unique, cut] at run
            | some env =>
              by_cases zero : state.clock = 0
              · simp [evaluate, read, found, unique, cut, zero] at run
              · let entered := callEnv params size (pushEnv env handler.isSome (decClock state))
                cases bodyRun : evaluate body entered with
                | mk outcome last =>
                  have clamped : fixClock entered (evaluate body entered) = (outcome, last) := by rw [fixClock_evaluate, bodyRun]
                  have bound := evaluate_clock_le body entered
                  rw [bodyRun] at bound
                  change last.clock ≤ entered.clock at bound
                  have enteredClock : entered.clock = state.clock - 1 := by
                    cases handler <;> rfl
                  have clockLess : last.clock < state.clock := by omega
                  simp only [entered] at clamped
                  cases outcome with
                  | none => simp [evaluate, read, found, unique, cut, zero, clamped] at run
                  | some outcome =>
                    cases outcome with
                    | val returned =>
                      simp only [evaluate, read, found, unique, cut, zero, clamped] at run
                      repeat' (split at run <;> try simp_all)
                    | err error =>
                      cases error with
                      | abort reason => simp [evaluate, read, found, unique, cut, zero, clamped] at run
                      | raise value =>
                        cases handler with
                        | none =>
                          simp only [Option.isSome] at clamped
                          simp [evaluate, read, found, unique, cut, zero, clamped] at run
                        | some pair =>
                          obtain ⟨name, handlerBody⟩ := pair
                          simp only [Option.isSome] at clamped
                          have handlerRun : evaluate handlerBody (setVar name value last) = (some (.val values), next) := by
                            simpa [evaluate, read, found, unique, cut, zero, clamped] using run
                          exact evaluate_value_localsSize handlerBody (setVar name value last) next values handlerRun
          · simp [evaluate, read, found, unique] at run
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals try subst program
  all_goals simp_wf
  all_goals simp_all [callEnv, decClock, pushEnv, setVar]
  all_goals try (apply Prod.Lex.left; omega)
  all_goals try (apply Prod.Lex.right; omega)
  all_goals try omega

end Flapjack.Compiler.Backend.DataSem
