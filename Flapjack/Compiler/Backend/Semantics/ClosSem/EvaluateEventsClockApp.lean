import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateEventsClockControl

/-! Cross-clock application trace comparisons for the proof-side evaluator. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- A full closure application evaluates its body before remaining arguments. -/
theorem evaluateApp_full_step {C F : Type} (location : Option Nat) (function first : Value)
    (rest : List Value) (state : State C F) (body : ClosLang.Exp) (bodyEnv remaining : List Value)
    (found : destClosure state.maxApp location function (first :: rest) = some (.fullApp body bodyEnv remaining))
    (enough : (first :: rest).length - remaining.length ≤ state.clock) :
    evaluateApp location function (first :: rest) state =
      match evaluate [body] bodyEnv (decClock ((first :: rest).length - remaining.length) state) with
      | (.val [value], next) => evaluateApp location value remaining next
      | (other, next) => (other, next) := by
  rw [evaluateApp, found]
  simp only [not_lt.mpr enough, ↓reduceIte, fixClock_evaluate]
  cases run : evaluate [body] bodyEnv (decClock ((first :: rest).length - remaining.length) state) with
  | mk result next =>
    cases result with
    | err error => rfl
    | val values =>
      cases values with
      | nil => rfl
      | cons first tail => cases tail <;> rfl

/-- A full closure application extends the trace produced by its body. -/
theorem evaluateApp_full_body_ioEvents_prefix {C F : Type} (location : Option Nat) (function first : Value)
    (rest : List Value) (state : State C F) (body : ClosLang.Exp) (bodyEnv remaining : List Value)
    (found : destClosure state.maxApp location function (first :: rest) = some (.fullApp body bodyEnv remaining))
    (enough : (first :: rest).length - remaining.length ≤ state.clock) :
    (evaluate [body] bodyEnv (decClock ((first :: rest).length - remaining.length) state)).2.ffi.ioEvents <+:
      (evaluateApp location function (first :: rest) state).2.ffi.ioEvents := by
  rw [evaluateApp_full_step location function first rest state body bodyEnv remaining found enough]
  cases bodyRun : evaluate [body] bodyEnv (decClock ((first :: rest).length - remaining.length) state) with
  | mk bodyResult last =>
    cases bodyResult with
    | err error => simp
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value body bodyEnv
        (decClock ((first :: rest).length - remaining.length) state) last values bodyRun
      cases appRun : evaluateApp location value remaining last with
      | mk appResult final =>
        simpa [appRun] using evaluate_ioEvents_prefix.2 location value remaining last final appResult appRun

/-- Closure application is trace-monotone in clock when its body and
remaining applications are. -/
theorem evaluateApp_addClock_ioEvents_step {C F : Type} (location : Option Nat) (function : Value)
    (args : List Value) (state : State C F) (extra : Nat)
    (bodyIH : ∀ (body : ClosLang.Exp) (env : List Value) (start : State C F), start.clock < state.clock →
      (evaluate [body] env start).2.ffi.ioEvents <+:
        (evaluate [body] env { start with clock := start.clock + extra }).2.ffi.ioEvents)
    (appIH : ∀ (value : Value) (remaining : List Value) (start : State C F), start.clock < state.clock →
      (evaluateApp location value remaining start).2.ffi.ioEvents <+:
        (evaluateApp location value remaining { start with clock := start.clock + extra }).2.ffi.ioEvents) :
    (evaluateApp location function args state).2.ffi.ioEvents <+:
      (evaluateApp location function args { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  cases run : evaluateApp location function args state with
  | mk result final =>
    by_cases timeout : result = .err (.abort .timeoutError)
    · subst result
      cases args with
      | nil => simp [evaluateApp] at run
      | cons first rest =>
        have sourceRun := run
        rw [evaluateApp] at sourceRun
        cases found : destClosure state.maxApp location function (first :: rest) with
        | none => rw [found] at sourceRun; simp at sourceRun
        | some kind =>
          rw [found] at sourceRun
          dsimp only at sourceRun
          cases kind with
          | partialApp value =>
            dsimp only at sourceRun
            split at sourceRun <;> simp at sourceRun
            rcases sourceRun with ⟨_, rfl⟩
            cases targetRun : evaluateApp location function (first :: rest) { state with clock := state.clock + extra } with
            | mk targetResult targetFinal =>
              simpa using evaluate_ioEvents_prefix.2 location function (first :: rest)
                { state with clock := state.clock + extra } targetFinal targetResult targetRun
          | fullApp body bodyEnv remaining =>
            dsimp only at sourceRun
            have remainingLt := destClosure_full_remaining_lt state.maxApp location function (first :: rest)
              bodyEnv remaining body found
            let cost := (first :: rest).length - remaining.length
            have positive : 0 < cost := Nat.sub_pos_of_lt remainingLt
            by_cases short : state.clock < cost
            · rw [if_pos short] at sourceRun
              simp at sourceRun
              rcases sourceRun with ⟨_, rfl⟩
              cases targetRun : evaluateApp location function (first :: rest) { state with clock := state.clock + extra } with
              | mk targetResult targetFinal =>
                simpa using evaluate_ioEvents_prefix.2 location function (first :: rest)
                  { state with clock := state.clock + extra } targetFinal targetResult targetRun
            · rw [if_neg short, fixClock_evaluate] at sourceRun
              have smaller : (decClock cost state).clock < state.clock := by simp [decClock]; omega
              have shifted : decClock cost { state with clock := state.clock + extra } =
                  { decClock cost state with clock := (decClock cost state).clock + extra } := by
                simp only [decClock]
                congr 1
                omega
              have foundTarget : destClosure { state with clock := state.clock + extra }.maxApp location function (first :: rest) =
                  some (.fullApp body bodyEnv remaining) := by simpa using found
              have enoughTarget : (first :: rest).length - remaining.length ≤
                  ({ state with clock := state.clock + extra } : State C F).clock := by simp only [cost] at short; simp only; omega
              have targetStep := evaluateApp_full_step location function first rest { state with clock := state.clock + extra }
                body bodyEnv remaining foundTarget enoughTarget
              rw [show (first :: rest).length - remaining.length = cost from rfl, shifted] at targetStep
              cases bodyRun : evaluate [body] bodyEnv (decClock cost state) with
              | mk bodyResult last =>
                have bound : last.clock ≤ (decClock cost state).clock := by
                  have clock := evaluate_clock_le [body] bodyEnv (decClock cost state)
                  simpa [bodyRun] using clock
                rw [bodyRun] at sourceRun
                by_cases bodyTimeout : bodyResult = .err (.abort .timeoutError)
                · subst bodyResult
                  simp at sourceRun
                  rcases sourceRun with ⟨_, rfl⟩
                  have bodyPrefix := bodyIH body bodyEnv (decClock cost state) smaller
                  have targetPrefix := evaluateApp_full_body_ioEvents_prefix location function first rest
                    { state with clock := state.clock + extra } body bodyEnv remaining foundTarget enoughTarget
                  rw [show (first :: rest).length - remaining.length = cost from rfl, shifted] at targetPrefix
                  simpa [bodyRun] using bodyPrefix.trans targetPrefix
                · have shiftedBody := evaluate_addClock.1 [body] bodyEnv (decClock cost state) last bodyResult extra bodyRun bodyTimeout
                  cases bodyResult with
                  | err error =>
                    simp at sourceRun
                    rcases sourceRun with ⟨rfl, _⟩
                    exact (bodyTimeout rfl).elim
                  | val values =>
                    obtain ⟨value, rfl⟩ := evaluate_singleton_value body bodyEnv (decClock cost state) last values bodyRun
                    dsimp only at sourceRun
                    have compare := appIH value remaining last (by omega)
                    rw [sourceRun] at compare
                    rw [targetStep, shiftedBody]
                    exact compare
    · have equal := evaluateApp_addClock_ioEvents_of_notTimeout location function args state final result extra run timeout
      simp only [run] at equal
      rw [equal]
      exact List.prefix_refl _

/-- A force operation that starts evaluating a thunk has the same final
trace as that evaluation; the subsequent reference update adds no events. -/
theorem evaluate_force_body_ioEvents_eq {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List Value) (state last : State C F) (arguments : List Value) (value : Value)
    (argsRun : evaluate args env state = (.val arguments, last))
    (inspected : destThunk arguments last.refs = .isThunk .notEvaluated value) :
    (evaluate [.op trace (.thunkOp .forceThunk) args] env state).2.ffi.ioEvents =
      (evaluate [appUnit (.var .none 0)] [value] last).2.ffi.ioEvents := by
  rw [evaluate, fixClock_evaluate, argsRun]
  dsimp only
  rw [inspected]
  cases forceRun : evaluate [appUnit (.var .none 0)] [value] last with
  | mk forceResult final =>
    dsimp only
    rw [forceRun]
    cases forceResult with
    | err error => rfl
    | val forced =>
      dsimp only
      cases updated : updateThunk arguments final.refs forced <;> simp

/-- Forcing a thunk extends the trace produced by its arguments. -/
theorem evaluate_force_args_ioEvents_prefix {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List Value) (state : State C F) :
    (evaluate args env state).2.ffi.ioEvents <+:
      (evaluate [.op trace (.thunkOp .forceThunk) args] env state).2.ffi.ioEvents := by
  cases argsRun : evaluate args env state with
  | mk argResult last =>
    cases argResult with
    | err error => rw [evaluate, fixClock_evaluate, argsRun]; simp
    | val arguments =>
      cases inspected : destThunk arguments last.refs with
      | badRef | notThunk => rw [evaluate, fixClock_evaluate, argsRun]; simp [inspected]
      | isThunk mode value =>
        cases mode with
        | evaluated => rw [evaluate, fixClock_evaluate, argsRun]; simp [inspected]
        | notEvaluated =>
          rw [evaluate_force_body_ioEvents_eq trace args env state last arguments value argsRun inspected]
          cases forceRun : evaluate [appUnit (.var .none 0)] [value] last with
          | mk forceResult final =>
            simpa [forceRun] using evaluate_ioEvents_prefix.1 [appUnit (.var .none 0)] [value] last final forceResult forceRun

/-- Force-thunk evaluation is trace-monotone when its argument and forced
computations are. -/
theorem evaluate_force_addClock_ioEvents_step {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List Value) (state : State C F) (extra : Nat)
    (argsIH : (evaluate args env state).2.ffi.ioEvents <+:
      (evaluate args env { state with clock := state.clock + extra }).2.ffi.ioEvents)
    (forceIH : ∀ (value : Value) (start : State C F), start.clock ≤ state.clock →
      (evaluate [appUnit (.var .none 0)] [value] start).2.ffi.ioEvents <+:
        (evaluate [appUnit (.var .none 0)] [value] { start with clock := start.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.op trace (.thunkOp .forceThunk) args] env state).2.ffi.ioEvents <+:
      (evaluate [.op trace (.thunkOp .forceThunk) args] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  cases run : evaluate [.op trace (.thunkOp .forceThunk) args] env state with
  | mk result final =>
    by_cases timeout : result = .err (.abort .timeoutError)
    · subst result
      have sourceRun := run
      rw [evaluate, fixClock_evaluate] at sourceRun
      cases argsRun : evaluate args env state with
      | mk argResult last =>
        have bound : last.clock ≤ state.clock := by
          have clock := evaluate_clock_le args env state
          simpa [argsRun] using clock
        rw [argsRun] at sourceRun
        cases argResult with
        | err error =>
          simp at sourceRun
          rcases sourceRun with ⟨_, rfl⟩
          have argsPrefix : last.ffi.ioEvents <+:
              (evaluate args env { state with clock := state.clock + extra }).2.ffi.ioEvents := by simpa [argsRun] using argsIH
          exact argsPrefix.trans (evaluate_force_args_ioEvents_prefix trace args env { state with clock := state.clock + extra })
        | val arguments =>
          have shiftedArgs := evaluate_addClock.1 args env state last (.val arguments) extra argsRun (by simp)
          dsimp only at sourceRun
          cases inspected : destThunk arguments last.refs with
          | badRef | notThunk => simp [inspected] at sourceRun
          | isThunk mode value =>
            cases mode with
            | evaluated => simp [inspected] at sourceRun
            | notEvaluated =>
              rw [inspected] at sourceRun
              dsimp only at sourceRun
              cases forceRun : evaluate [appUnit (.var .none 0)] [value] last with
              | mk forceResult forceFinal =>
                rw [forceRun] at sourceRun
                cases forceResult with
                | err error =>
                  simp at sourceRun
                  rcases sourceRun with ⟨_, rfl⟩
                  have compare := forceIH value last bound
                  have targetTrace := evaluate_force_body_ioEvents_eq trace args env
                    { state with clock := state.clock + extra } { last with clock := last.clock + extra }
                    arguments value shiftedArgs (by simpa using inspected)
                  rw [targetTrace]
                  simpa [forceRun] using compare
                | val forced =>
                  cases updated : updateThunk arguments forceFinal.refs forced <;> simp [updated] at sourceRun
    · have equal := evaluate_addClock_ioEvents_of_notTimeout [.op trace (.thunkOp .forceThunk) args] env state final result extra run timeout
      simp only [run] at equal
      rw [equal]
      exact List.prefix_refl _

/-- The function trace is a prefix of a nonempty application after its
arguments have successfully evaluated. -/
theorem evaluate_app_function_ioEvents_prefix {C F : Type} (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (env : List Value) (state last : State C F)
    (arguments : List Value) (notEmpty : args.isEmpty = false) (argsRun : evaluate args env state = (.val arguments, last)) :
    (evaluate [function] env last).2.ffi.ioEvents <+:
      (evaluate [.app trace location function args] env state).2.ffi.ioEvents := by
  rw [evaluate]
  simp only [notEmpty, Bool.false_eq_true, ↓reduceIte]
  rw [fixClock_evaluate, argsRun]
  dsimp only
  rw [fixClock_evaluate]
  cases functionRun : evaluate [function] env last with
  | mk functionResult mid =>
    cases functionResult with
    | err error => simp
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value function env last mid values functionRun
      cases appRun : evaluateApp location value arguments mid with
      | mk appResult final =>
        simpa [appRun] using evaluate_ioEvents_prefix.2 location value arguments mid final appResult appRun

/-- A nonempty application extends the trace produced by its arguments. -/
theorem evaluate_app_args_ioEvents_prefix {C F : Type} (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (env : List Value) (state : State C F)
    (notEmpty : args.isEmpty = false) :
    (evaluate args env state).2.ffi.ioEvents <+:
      (evaluate [.app trace location function args] env state).2.ffi.ioEvents := by
  cases argsRun : evaluate args env state with
  | mk argResult last =>
    cases argResult with
    | err error =>
      rw [evaluate]
      simp only [notEmpty, Bool.false_eq_true, ↓reduceIte]
      rw [fixClock_evaluate, argsRun]
      simp
    | val arguments =>
      have continuation := evaluate_app_function_ioEvents_prefix trace location function args env state last arguments notEmpty argsRun
      cases functionRun : evaluate [function] env last with
      | mk functionResult mid =>
        have functionPrefix := evaluate_ioEvents_prefix.1 [function] env last mid functionResult functionRun
        have restPrefix : mid.ffi.ioEvents <+:
            (evaluate [.app trace location function args] env state).2.ffi.ioEvents := by simpa [functionRun] using continuation
        exact functionPrefix.trans restPrefix

/-- Application expressions are trace-monotone when their arguments,
function, and closure application are. -/
theorem evaluate_app_addClock_ioEvents_step {C F : Type} (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (env : List Value) (state : State C F) (extra : Nat)
    (argsIH : (evaluate args env state).2.ffi.ioEvents <+:
      (evaluate args env { state with clock := state.clock + extra }).2.ffi.ioEvents)
    (functionIH : ∀ (start : State C F), start.clock ≤ state.clock →
      (evaluate [function] env start).2.ffi.ioEvents <+:
        (evaluate [function] env { start with clock := start.clock + extra }).2.ffi.ioEvents)
    (appIH : ∀ (value : Value) (arguments : List Value) (start : State C F), start.clock ≤ state.clock →
      (evaluateApp location value arguments start).2.ffi.ioEvents <+:
        (evaluateApp location value arguments { start with clock := start.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.app trace location function args] env state).2.ffi.ioEvents <+:
      (evaluate [.app trace location function args] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  cases run : evaluate [.app trace location function args] env state with
  | mk result final =>
    by_cases timeout : result = .err (.abort .timeoutError)
    · subst result
      cases args with
      | nil => simp [evaluate] at run
      | cons first rest =>
        have sourceRun := run
        rw [evaluate, fixClock_evaluate] at sourceRun
        cases argsRun : evaluate (first :: rest) env state with
        | mk argResult last =>
          have bound : last.clock ≤ state.clock := by
            have clock := evaluate_clock_le (first :: rest) env state
            simpa [argsRun] using clock
          rw [argsRun] at sourceRun
          cases argResult with
          | err error =>
            simp at sourceRun
            rcases sourceRun with ⟨_, rfl⟩
            have argsPrefix : last.ffi.ioEvents <+:
                (evaluate (first :: rest) env { state with clock := state.clock + extra }).2.ffi.ioEvents := by simpa [argsRun] using argsIH
            exact argsPrefix.trans (evaluate_app_args_ioEvents_prefix trace location function (first :: rest) env
              { state with clock := state.clock + extra } rfl)
          | val arguments =>
            have shiftedArgs := evaluate_addClock.1 (first :: rest) env state last (.val arguments) extra argsRun (by simp)
            dsimp only at sourceRun
            rw [fixClock_evaluate] at sourceRun
            cases functionRun : evaluate [function] env last with
            | mk functionResult mid =>
              have functionBound : mid.clock ≤ last.clock := by
                have clock := evaluate_clock_le [function] env last
                simpa [functionRun] using clock
              rw [functionRun] at sourceRun
              cases functionResult with
              | err error =>
                simp at sourceRun
                rcases sourceRun with ⟨_, rfl⟩
                have functionPrefix : mid.ffi.ioEvents <+:
                    (evaluate [function] env { last with clock := last.clock + extra }).2.ffi.ioEvents := by
                  simpa [functionRun] using functionIH last bound
                exact functionPrefix.trans (evaluate_app_function_ioEvents_prefix trace location function (first :: rest) env
                  { state with clock := state.clock + extra } { last with clock := last.clock + extra } arguments rfl shiftedArgs)
              | val values =>
                obtain ⟨value, rfl⟩ := evaluate_singleton_value function env last mid values functionRun
                have shiftedFunction := evaluate_addClock.1 [function] env last mid (.val [value]) extra functionRun (by simp)
                simp at sourceRun
                have compare := appIH value arguments mid (by omega)
                rw [sourceRun] at compare
                rw [evaluate, fixClock_evaluate, shiftedArgs]
                dsimp only
                rw [fixClock_evaluate, shiftedFunction]
                exact compare
    · have equal := evaluate_addClock_ioEvents_of_notTimeout [.app trace location function args] env state final result extra run timeout
      simp only [run] at equal
      rw [equal]
      exact List.prefix_refl _

/-- Installation extends the trace produced by evaluation of its arguments. -/
theorem evaluate_install_args_ioEvents_prefix {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List Value) (state : State C F) :
    (evaluate args env state).2.ffi.ioEvents <+:
      (evaluate [.op trace .install args] env state).2.ffi.ioEvents := by
  rw [evaluate, fixClock_evaluate]
  cases argsRun : evaluate args env state with
  | mk argResult last =>
    cases argResult with
    | err error => simp
    | val arguments =>
      dsimp only
      cases installRun : doInstall arguments.reverse last with
      | mk installResult installed =>
        have ffiEq := doInstall_ffi arguments.reverse last installed installResult installRun
        cases installResult with
        | err error => simp [ffiEq]
        | val program =>
          cases programRun : evaluate program [] installed with
          | mk programResult final =>
            have programPrefix := evaluate_ioEvents_prefix.1 program [] installed final programResult programRun
            cases programResult <;> simpa [programRun, ffiEq] using programPrefix

/-- Installation is trace-monotone when its arguments and installed program
are, including timeout before the installed program starts. -/
theorem evaluate_install_addClock_ioEvents_step {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List Value) (state : State C F) (extra : Nat)
    (argsIH : (evaluate args env state).2.ffi.ioEvents <+:
      (evaluate args env { state with clock := state.clock + extra }).2.ffi.ioEvents)
    (programIH : ∀ (program : List ClosLang.Exp) (start : State C F), start.clock < state.clock →
      (evaluate program [] start).2.ffi.ioEvents <+:
        (evaluate program [] { start with clock := start.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.op trace .install args] env state).2.ffi.ioEvents <+:
      (evaluate [.op trace .install args] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  cases run : evaluate [.op trace .install args] env state with
  | mk result final =>
    by_cases timeout : result = .err (.abort .timeoutError)
    · subst result
      have sourceRun := run
      rw [evaluate, fixClock_evaluate] at sourceRun
      cases argsRun : evaluate args env state with
      | mk argResult last =>
        have bound : last.clock ≤ state.clock := by
          have clock := evaluate_clock_le args env state
          simpa [argsRun] using clock
        rw [argsRun] at sourceRun
        cases argResult with
        | err error =>
          simp at sourceRun
          rcases sourceRun with ⟨_, rfl⟩
          have argsPrefix : last.ffi.ioEvents <+:
              (evaluate args env { state with clock := state.clock + extra }).2.ffi.ioEvents := by simpa [argsRun] using argsIH
          exact argsPrefix.trans (evaluate_install_args_ioEvents_prefix trace args env { state with clock := state.clock + extra })
        | val arguments =>
          have shiftedArgs := evaluate_addClock.1 args env state last (.val arguments) extra argsRun (by simp)
          dsimp only at sourceRun
          cases installRun : doInstall arguments.reverse last with
          | mk installResult installed =>
            rw [installRun] at sourceRun
            have ffiEq := doInstall_ffi arguments.reverse last installed installResult installRun
            cases installResult with
            | err error =>
              simp at sourceRun
              rcases sourceRun with ⟨_, rfl⟩
              have argsPrefix : installed.ffi.ioEvents <+:
                  (evaluate args env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
                simpa [argsRun, ffiEq] using argsIH
              exact argsPrefix.trans (evaluate_install_args_ioEvents_prefix trace args env { state with clock := state.clock + extra })
            | val program =>
              dsimp only at sourceRun
              have consumed := doInstall_success_clock arguments.reverse last installed program installRun
              have smaller : installed.clock < state.clock := by omega
              have compare := programIH program installed smaller
              have shiftedInstall := doInstall_success_addClock arguments.reverse last installed program extra installRun
              cases programRun : evaluate program [] installed with
              | mk programResult programFinal =>
                rw [programRun] at sourceRun
                cases programResult <;> simp at sourceRun
                all_goals rcases sourceRun with ⟨_, rfl⟩
                all_goals rw [evaluate, fixClock_evaluate, shiftedArgs]
                all_goals dsimp only
                all_goals rw [shiftedInstall]
                all_goals dsimp only
                all_goals cases targetRun : evaluate program [] { installed with clock := installed.clock + extra } with
                | mk targetResult targetFinal =>
                  cases targetResult <;> simpa [programRun, targetRun] using compare
    · have equal := evaluate_addClock_ioEvents_of_notTimeout [.op trace .install args] env state final result extra run timeout
      simp only [run] at equal
      rw [equal]
      exact List.prefix_refl _

end Flapjack.Compiler.Backend.ClosSem
