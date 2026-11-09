import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateEvents

/-! Control-flow event-prefix steps for the proof-side closure evaluator. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- Raising a value preserves the event prefix of its evaluation. -/
theorem evaluate_raise_ioEvents_step {C F : Type} (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (env : List Value) (state final : State C F) (result : Result (List Value) Value)
    (bodyIH : ∀ (last : State C F) (bodyResult : Result (List Value) Value),
      evaluate [body] env state = (bodyResult, last) → state.ffi.ioEvents <+: last.ffi.ioEvents)
    (run : evaluate [.raise trace body] env state = (result, final)) : state.ffi.ioEvents <+: final.ffi.ioEvents := by
  cases bodyRun : evaluate [body] env state with
  | mk bodyResult last =>
    rw [evaluate, bodyRun] at run
    have eventsPrefix := bodyIH last bodyResult bodyRun
    cases bodyResult <;> simp at run
    all_goals rcases run with ⟨rfl, rfl⟩
    all_goals exact eventsPrefix

/-- A let evaluates its bindings and then its body, extending the trace at
each successful stage. -/
theorem evaluate_let_ioEvents_step {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (env : List Value)
    (state final : State C F) (result : Result (List Value) Value)
    (bindingsIH : ∀ (last : State C F) (bindingResult : Result (List Value) Value),
      evaluate bindings env state = (bindingResult, last) → state.ffi.ioEvents <+: last.ffi.ioEvents)
    (bodyIH : ∀ (bodyEnv : List Value) (start last : State C F) (bodyResult : Result (List Value) Value),
      start.clock ≤ state.clock → evaluate [body] bodyEnv start = (bodyResult, last) → start.ffi.ioEvents <+: last.ffi.ioEvents)
    (run : evaluate [.let trace bindings body] env state = (result, final)) : state.ffi.ioEvents <+: final.ffi.ioEvents := by
  rw [evaluate, fixClock_evaluate] at run
  cases bindingsRun : evaluate bindings env state with
  | mk bindingResult last =>
    have bound : last.clock ≤ state.clock := by
      have clock := evaluate_clock_le bindings env state
      simpa [bindingsRun] using clock
    rw [bindingsRun] at run
    have eventsPrefix := bindingsIH last bindingResult bindingsRun
    cases bindingResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact eventsPrefix
    | val values =>
      dsimp only at run
      exact eventsPrefix.trans (bodyIH (values ++ env) last final result bound run)

/-- A conditional extends its event trace through its test and branch. -/
theorem evaluate_if_ioEvents_step {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (env : List Value) (state final : State C F) (result : Result (List Value) Value)
    (conditionIH : ∀ (last : State C F) (testResult : Result (List Value) Value),
      evaluate [condition] env state = (testResult, last) → state.ffi.ioEvents <+: last.ffi.ioEvents)
    (branchIH : ∀ (choice : Bool) (start last : State C F) (branchResult : Result (List Value) Value),
      start.clock ≤ state.clock → evaluate [if choice then yes else no] env start = (branchResult, last) →
      start.ffi.ioEvents <+: last.ffi.ioEvents)
    (run : evaluate [.ifThenElse trace condition yes no] env state = (result, final)) : state.ffi.ioEvents <+: final.ffi.ioEvents := by
  rw [evaluate, fixClock_evaluate] at run
  cases conditionRun : evaluate [condition] env state with
  | mk testResult last =>
    have bound : last.clock ≤ state.clock := by
      have clock := evaluate_clock_le [condition] env state
      simpa [conditionRun] using clock
    rw [conditionRun] at run
    have eventsPrefix := conditionIH last testResult conditionRun
    cases testResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact eventsPrefix
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value condition env state last values conditionRun
      dsimp only at run
      cases boolRun : asBool value with
      | none =>
        simp [boolRun] at run
        rcases run with ⟨rfl, rfl⟩
        exact eventsPrefix
      | some choice =>
        cases choice <;> simp [boolRun] at run
        · exact eventsPrefix.trans (branchIH false last final result bound run)
        · exact eventsPrefix.trans (branchIH true last final result bound run)

/-- A handler extends the trace through its body and, if raised, its handler. -/
theorem evaluate_handle_ioEvents_step {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (env : List Value) (state final : State C F) (result : Result (List Value) Value)
    (bodyIH : ∀ (last : State C F) (bodyResult : Result (List Value) Value),
      evaluate [body] env state = (bodyResult, last) → state.ffi.ioEvents <+: last.ffi.ioEvents)
    (handlerIH : ∀ (value : Value) (start last : State C F) (handlerResult : Result (List Value) Value),
      start.clock ≤ state.clock → evaluate [handler] (value :: env) start = (handlerResult, last) →
      start.ffi.ioEvents <+: last.ffi.ioEvents)
    (run : evaluate [.handle trace body handler] env state = (result, final)) : state.ffi.ioEvents <+: final.ffi.ioEvents := by
  rw [evaluate, fixClock_evaluate] at run
  cases bodyRun : evaluate [body] env state with
  | mk bodyResult last =>
    have bound : last.clock ≤ state.clock := by
      have clock := evaluate_clock_le [body] env state
      simpa [bodyRun] using clock
    rw [bodyRun] at run
    have eventsPrefix := bodyIH last bodyResult bodyRun
    cases bodyResult with
    | val values =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact eventsPrefix
    | err error =>
      cases error with
      | abort reason =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact eventsPrefix
      | raise value =>
        dsimp only at run
        exact eventsPrefix.trans (handlerIH value last final result bound run)

/-- Ticks either time out without an event or continue at a smaller clock. -/
theorem evaluate_tick_ioEvents_step {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (env : List Value) (state final : State C F) (result : Result (List Value) Value)
    (bodyIH : ∀ (start last : State C F) (bodyResult : Result (List Value) Value),
      start.clock < state.clock → evaluate [body] env start = (bodyResult, last) → start.ffi.ioEvents <+: last.ffi.ioEvents)
    (run : evaluate [.tick trace body] env state = (result, final)) : state.ffi.ioEvents <+: final.ffi.ioEvents := by
  rw [evaluate] at run
  split at run
  · simp at run
    rcases run with ⟨rfl, rfl⟩
    exact List.prefix_refl _
  · have smaller : (decClock 1 state).clock < state.clock := by simp [decClock]; omega
    simpa [decClock] using bodyIH (decClock 1 state) final result smaller run

/-- Recursive closure binding itself does not add events. -/
theorem evaluate_letrec_ioEvents_step {C F : Type} (names : List Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat)) (functions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (env : List Value) (state final : State C F) (result : Result (List Value) Value)
    (bodyIH : ∀ (bodyEnv : List Value), evaluate [body] bodyEnv state = (result, final) →
      state.ffi.ioEvents <+: final.ffi.ioEvents)
    (run : evaluate [.letrec names location selected functions body] env state = (result, final)) :
    state.ffi.ioEvents <+: final.ffi.ioEvents := by
  rw [evaluate.eq_def] at run
  dsimp only at run
  repeat' split at run
  all_goals try (solve | simp_all)
  all_goals exact bodyIH _ run

/-- A direct call extends the argument trace by that of its selected body. -/
theorem evaluate_call_ioEvents_step {C F : Type} (trace : BackendCommon.Tra)
    (ticks location : Nat) (args : List ClosLang.Exp) (env : List Value)
    (state final : State C F) (result : Result (List Value) Value)
    (argsIH : ∀ (last : State C F) (argResult : Result (List Value) Value),
      evaluate args env state = (argResult, last) → state.ffi.ioEvents <+: last.ffi.ioEvents)
    (bodyIH : ∀ (body : ClosLang.Exp) (bodyEnv : List Value) (start last : State C F)
      (bodyResult : Result (List Value) Value), start.clock < state.clock →
      evaluate [body] bodyEnv start = (bodyResult, last) → start.ffi.ioEvents <+: last.ffi.ioEvents)
    (run : evaluate [.call trace ticks location args] env state = (result, final)) :
    state.ffi.ioEvents <+: final.ffi.ioEvents := by
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate args env state with
  | mk argResult last =>
    have bound : last.clock ≤ state.clock := by
      have clock := evaluate_clock_le args env state
      simpa [argsRun] using clock
    rw [argsRun] at run
    have argsPrefix := argsIH last argResult argsRun
    cases argResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact argsPrefix
    | val arguments =>
      dsimp only at run
      cases found : findCode location arguments last.code with
      | none =>
        simp [found] at run
        rcases run with ⟨rfl, rfl⟩
        exact argsPrefix
      | some entry =>
        rcases entry with ⟨bodyEnv, body⟩
        rw [found] at run
        dsimp only at run
        split at run
        · simp at run
          rcases run with ⟨rfl, rfl⟩
          exact argsPrefix
        · have smaller : (decClock (ticks + 1) last).clock < state.clock := by simp [decClock]; omega
          have bodyPrefix := bodyIH body bodyEnv (decClock (ticks + 1) last) final result smaller run
          exact argsPrefix.trans (by simpa [decClock] using bodyPrefix)

/-- Applying a closure extends the trace through its body and any subsequent
application at smaller clocks. -/
theorem evaluateApp_ioEvents_step {C F : Type} (location : Option Nat) (function : Value)
    (args : List Value) (state final : State C F) (result : Result (List Value) Value)
    (bodyIH : ∀ (body : ClosLang.Exp) (env : List Value) (start last : State C F)
      (bodyResult : Result (List Value) Value), start.clock < state.clock →
      evaluate [body] env start = (bodyResult, last) → start.ffi.ioEvents <+: last.ffi.ioEvents)
    (appIH : ∀ (value : Value) (remaining : List Value) (start last : State C F)
      (appResult : Result (List Value) Value), start.clock < state.clock →
      evaluateApp location value remaining start = (appResult, last) → start.ffi.ioEvents <+: last.ffi.ioEvents)
    (run : evaluateApp location function args state = (result, final)) : state.ffi.ioEvents <+: final.ffi.ioEvents := by
  cases args with
  | nil =>
    simp [evaluateApp] at run
    rcases run with ⟨rfl, rfl⟩
    exact List.prefix_refl _
  | cons first rest =>
    rw [evaluateApp] at run
    cases found : destClosure state.maxApp location function (first :: rest) with
    | none =>
      rw [found] at run
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact List.prefix_refl _
    | some kind =>
      rw [found] at run
      dsimp only at run
      cases kind with
      | partialApp value =>
        dsimp only at run
        split at run <;> simp at run
        all_goals rcases run with ⟨rfl, rfl⟩
        all_goals exact List.prefix_refl _
      | fullApp body bodyEnv remaining =>
        dsimp only at run
        have remainingLt := destClosure_full_remaining_lt state.maxApp location function (first :: rest)
          bodyEnv remaining body found
        let cost := (first :: rest).length - remaining.length
        have positive : 0 < cost := Nat.sub_pos_of_lt remainingLt
        split at run
        · simp at run
          rcases run with ⟨rfl, rfl⟩
          exact List.prefix_refl _
        · rw [fixClock_evaluate] at run
          cases bodyRun : evaluate [body] bodyEnv (decClock cost state) with
          | mk bodyResult last =>
            have bound : last.clock ≤ (decClock cost state).clock := by
              have clock := evaluate_clock_le [body] bodyEnv (decClock cost state)
              simpa [bodyRun] using clock
            have smaller : (decClock cost state).clock < state.clock := by simp [decClock]; omega
            have bodyPrefix := bodyIH body bodyEnv (decClock cost state) last bodyResult smaller bodyRun
            have initialPrefix : state.ffi.ioEvents <+: last.ffi.ioEvents := by simpa [decClock] using bodyPrefix
            rw [bodyRun] at run
            cases bodyResult with
            | err error =>
              simp at run
              rcases run with ⟨rfl, rfl⟩
              exact initialPrefix
            | val values =>
              obtain ⟨value, rfl⟩ := evaluate_singleton_value body bodyEnv (decClock cost state) last values bodyRun
              dsimp only at run
              exact initialPrefix.trans (appIH value remaining last final result (by omega) run)

/-- An application expression extends the traces of its arguments,
function expression, and closure application in sequence. -/
theorem evaluate_app_ioEvents_step {C F : Type} (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (env : List Value)
    (state final : State C F) (result : Result (List Value) Value)
    (argsIH : ∀ (last : State C F) (argResult : Result (List Value) Value),
      evaluate args env state = (argResult, last) → state.ffi.ioEvents <+: last.ffi.ioEvents)
    (functionIH : ∀ (start last : State C F) (functionResult : Result (List Value) Value),
      start.clock ≤ state.clock → evaluate [function] env start = (functionResult, last) →
      start.ffi.ioEvents <+: last.ffi.ioEvents)
    (appIH : ∀ (value : Value) (arguments : List Value) (start last : State C F)
      (appResult : Result (List Value) Value), start.clock ≤ state.clock →
      evaluateApp location value arguments start = (appResult, last) → start.ffi.ioEvents <+: last.ffi.ioEvents)
    (run : evaluate [.app trace location function args] env state = (result, final)) : state.ffi.ioEvents <+: final.ffi.ioEvents := by
  rw [evaluate] at run
  split at run
  · simp at run
    rcases run with ⟨rfl, rfl⟩
    exact List.prefix_refl _
  · rw [fixClock_evaluate] at run
    cases argsRun : evaluate args env state with
    | mk argResult last =>
      have bound : last.clock ≤ state.clock := by
        have clock := evaluate_clock_le args env state
        simpa [argsRun] using clock
      rw [argsRun] at run
      have argsPrefix := argsIH last argResult argsRun
      cases argResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact argsPrefix
      | val arguments =>
        dsimp only at run
        rw [fixClock_evaluate] at run
        cases functionRun : evaluate [function] env last with
        | mk functionResult mid =>
          have functionBound : mid.clock ≤ last.clock := by
            have clock := evaluate_clock_le [function] env last
            simpa [functionRun] using clock
          rw [functionRun] at run
          have functionPrefix := functionIH last mid functionResult bound functionRun
          cases functionResult with
          | err error =>
            simp at run
            rcases run with ⟨rfl, rfl⟩
            exact argsPrefix.trans functionPrefix
          | val values =>
            obtain ⟨value, rfl⟩ := evaluate_singleton_value function env last mid values functionRun
            dsimp only at run
            exact (argsPrefix.trans functionPrefix).trans (appIH value arguments mid final result (by omega) run)

end Flapjack.Compiler.Backend.ClosSem
