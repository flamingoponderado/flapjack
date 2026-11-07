import Flapjack.Compiler.Backend.Semantics.DataProps.ValueLocals

/-! Control-state invariant for non-type-error aborts. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- A non-type-error abort clears both locals and stack. This auxiliary
invariant is not the full HOL evaluator stack theorem. -/
theorem evaluate_abort_control {C F : Type} (program : DataLang.Prog) (state next : State C F)
    (reason : Abort) (notType : reason ≠ .typeError)
    (run : evaluate program state = (some (.err (.abort reason)), next)) :
    next.locals = .ln ∧ next.stack = [] := by
  cases program with
  | skip => simp [evaluate] at run
  | move dest src => simp only [evaluate] at run; split at run <;> simp_all
  | assign dest op names live =>
    simp only [evaluate] at run
    repeat' (split at run <;> try simp_all [flushState, installSfs])
    all_goals obtain ⟨_, rfl⟩ := run; exact ⟨rfl, rfl⟩
  | tick =>
    simp only [evaluate] at run
    split at run <;> simp_all [flushState]
    obtain ⟨_, rfl⟩ := run
    exact ⟨rfl, rfl⟩
  | makeSpace amount names => simp only [evaluate] at run; split at run <;> simp_all
  | raise name => simp only [evaluate] at run; repeat' (split at run <;> try simp_all)
  | «return» names => simp only [evaluate] at run; split at run <;> simp_all
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
        exact evaluate_abort_control second mid next reason notType run
      | some outcome =>
        cases outcome with
        | val returned => simp at run
        | err error =>
          cases error with
          | raise value => simp at run
          | abort r =>
            simp at run
            obtain ⟨rfl, rfl⟩ := run
            exact evaluate_abort_control first state _ _ notType firstRun
  | ifThenElse name yes no =>
    simp only [evaluate] at run
    split at run
    · simp_all
    · split at run
      · exact evaluate_abort_control yes state next reason notType run
      · split at run
        · exact evaluate_abort_control no state next reason notType run
        · simp_all
  | force ret label src =>
    cases read : getVar src state.locals with
    | none => simp [evaluate, read] at run; exact False.elim (notType run.1.symm)
    | some thunk =>
      cases inspect : destThunk thunk state.refs with
      | badRef => simp [evaluate, read, inspect] at run; exact False.elim (notType run.1.symm)
      | notThunk => simp [evaluate, read, inspect] at run; exact False.elim (notType run.1.symm)
      | isThunk mode value =>
        cases mode with
        | evaluated =>
          cases ret with
          | none => simp [evaluate, read, inspect] at run
          | some pair =>
            obtain ⟨dest, names⟩ := pair
            cases cut : cutEnv names state.locals <;> simp [evaluate, read, inspect, cut] at run
            exact False.elim (notType run.1.symm)
        | notEvaluated =>
          cases found : findCode (some label) [thunk, value] state.code state.stackFrameSizes with
          | none => simp [evaluate, read, inspect, found] at run; exact False.elim (notType run.1.symm)
          | some triple =>
            obtain ⟨args, body, size⟩ := triple
            cases ret with
            | none =>
              by_cases zero : state.clock = 0
              · simp [evaluate, read, inspect, found, zero] at run
                obtain ⟨_, rfl⟩ := run
                exact ⟨rfl, rfl⟩
              · cases bodyRun : evaluate body (callEnv args size (decClock state)) with
                | mk outcome last =>
                  simp [evaluate, read, inspect, found, zero, bodyRun] at run
                  cases outcome with
                  | none => simp at run; exact False.elim (notType run.1.symm)
                  | some outcome =>
                    cases outcome with
                    | val returned => simp at run
                    | err error =>
                      cases error with
                      | raise raised => simp at run
                      | abort r =>
                        simp at run
                        obtain ⟨rfl, rfl⟩ := run
                        exact evaluate_abort_control body (callEnv args size (decClock state)) _ _ notType bodyRun
            | some pair =>
              obtain ⟨dest, names⟩ := pair
              cases cut : cutEnv names state.locals with
              | none => simp [evaluate, read, inspect, found, cut] at run; exact False.elim (notType run.1.symm)
              | some env =>
                by_cases zero : state.clock = 0
                · simp [evaluate, read, inspect, found, cut, zero] at run
                  obtain ⟨_, rfl⟩ := run
                  exact ⟨rfl, rfl⟩
                · let entered := callEnv args size (pushEnv env false (decClock state))
                  cases bodyRun : evaluate body entered with
                  | mk outcome last =>
                    have clamped : fixClock entered (evaluate body entered) = (outcome, last) := by rw [fixClock_evaluate, bodyRun]
                    simp only [entered] at clamped
                    cases outcome with
                    | none => simp [evaluate, read, inspect, found, cut, zero, clamped] at run; exact False.elim (notType run.1.symm)
                    | some outcome =>
                      cases outcome with
                      | val returned =>
                        simp only [evaluate, read, inspect, found, cut, zero, clamped] at run
                        repeat' (split at run <;> try simp_all)
                      | err error =>
                        cases error with
                        | raise raised => simp [evaluate, read, inspect, found, cut, zero, clamped] at run
                        | abort r =>
                          simp [evaluate, read, inspect, found, cut, zero, clamped] at run
                          obtain ⟨rfl, rfl⟩ := run
                          exact evaluate_abort_control body entered _ _ notType bodyRun
  | call ret dest names handler =>
    cases read : getVars names state.locals with
    | none => simp [evaluate, read] at run; exact False.elim (notType run.1.symm)
    | some args =>
      cases found : findCode dest args state.code state.stackFrameSizes with
      | none => simp [evaluate, read, found] at run; exact False.elim (notType run.1.symm)
      | some triple =>
        obtain ⟨params, body, size⟩ := triple
        cases ret with
        | none =>
          cases handler with
          | some pair => simp [evaluate, read, found] at run; exact False.elim (notType run.1.symm)
          | none =>
            by_cases zero : state.clock = 0
            · simp [evaluate, read, found, zero, flushState] at run
              obtain ⟨_, rfl⟩ := run
              exact ⟨rfl, rfl⟩
            · cases bodyRun : evaluate body (callEnv params size (decClock state)) with
              | mk outcome last =>
                simp [evaluate, read, found, zero, bodyRun] at run
                cases outcome with
                | none => simp at run; exact False.elim (notType run.1.symm)
                | some outcome =>
                  cases outcome with
                  | val returned => simp at run
                  | err error =>
                    cases error with
                    | raise raised => simp at run
                    | abort r =>
                      simp at run
                      obtain ⟨rfl, rfl⟩ := run
                      exact evaluate_abort_control body (callEnv params size (decClock state)) _ _ notType bodyRun
        | some pair =>
          obtain ⟨returns, live⟩ := pair
          by_cases unique : returns.Nodup
          · cases cut : cutEnv live state.locals with
            | none => simp [evaluate, read, found, unique, cut] at run; exact False.elim (notType run.1.symm)
            | some env =>
              by_cases zero : state.clock = 0
              · simp [evaluate, read, found, unique, cut, zero] at run
                obtain ⟨_, rfl⟩ := run
                exact ⟨rfl, rfl⟩
              · let entered := callEnv params size (pushEnv env handler.isSome (decClock state))
                cases bodyRun : evaluate body entered with
                | mk outcome last =>
                  have clamped : fixClock entered (evaluate body entered) = (outcome, last) := by rw [fixClock_evaluate, bodyRun]
                  have bound := evaluate_clock_le body entered
                  rw [bodyRun] at bound
                  change last.clock ≤ entered.clock at bound
                  have enteredClock : entered.clock = state.clock - 1 := by cases handler <;> rfl
                  have clockLess : last.clock < state.clock := by omega
                  simp only [entered] at clamped
                  cases outcome with
                  | none => simp [evaluate, read, found, unique, cut, zero, clamped] at run; exact False.elim (notType run.1.symm)
                  | some outcome =>
                    cases outcome with
                    | val returned =>
                      simp only [evaluate, read, found, unique, cut, zero, clamped] at run
                      repeat' (split at run <;> try simp_all)
                    | err error =>
                      cases error with
                      | abort r =>
                        simp [evaluate, read, found, unique, cut, zero, clamped] at run
                        obtain ⟨rfl, rfl⟩ := run
                        exact evaluate_abort_control body entered _ _ notType bodyRun
                      | raise value =>
                        cases handler with
                        | none =>
                          simp only [Option.isSome] at clamped
                          simp [evaluate, read, found, unique, cut, zero, clamped] at run
                        | some pair =>
                          obtain ⟨name, handlerBody⟩ := pair
                          simp only [Option.isSome] at clamped
                          have handlerRun : evaluate handlerBody (setVar name value last) = (some (.err (.abort reason)), next) := by
                            simpa [evaluate, read, found, unique, cut, zero, clamped] using run
                          exact evaluate_abort_control handlerBody (setVar name value last) next reason notType handlerRun
          · simp [evaluate, read, found, unique] at run; exact False.elim (notType run.1.symm)
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals try subst program
  all_goals simp_wf
  all_goals simp_all [callEnv, decClock, pushEnv, setVar]
  all_goals try (apply Prod.Lex.left; omega)
  all_goals try (apply Prod.Lex.right; omega)
  all_goals try omega

end Flapjack.Compiler.Backend.DataSem
