import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateEvents
import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateClockShift
import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateLength

/-! BVI event trace comparisons across clock allowances. -/
namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BvlSem (Value findCode)
open Flapjack.Compiler.Backend.BviSem
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)

/-- Event-prefix invariant specialized to a given evaluation result. -/
theorem evaluate_run_ioEvents_prefix {C F : Type} (expressions : List Bvi.Exp)
    (env : List Value) (state next : BviState C F) (result : BviResult)
    (run : evaluate expressions env state = (result, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents := by
  simpa [eventGrowth, run] using evaluate_ioEvents_prefix expressions env state

/-- A non-timeout evaluation has the same events after clock extension. -/
theorem evaluate_addClock_ioEvents_of_notTimeout {C F : Type} (expressions : List Bvi.Exp)
    (env : List Value) (state next : BviState C F)
    (result : BviResult) (extra : Nat)
    (run : evaluate expressions env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    (evaluate expressions env state).2.ffi.ioEvents =
      (evaluate expressions env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  have shifted := evaluate_addClock expressions env state next result extra run notTimeout
  simp [run, shifted]

/-- The trace of a let binding is a prefix of the entire let trace. -/
theorem evaluate_let_bindings_ioEvents_prefix {C F : Type} (bindings : List Bvi.Exp) (body : Bvi.Exp) (env : List Value) (state : BviState C F) :
    (evaluate bindings env state).2.ffi.ioEvents <+:
      (evaluate [.let bindings body] env state).2.ffi.ioEvents := by
  rw [evaluate, fixClock_evaluate]
  cases bindingsRun : evaluate bindings env state with
  | mk bindingResult last =>
    cases bindingResult with
    | err error => simp
    | val values =>
      cases bodyRun : evaluate [body] (values ++ env) last with
      | mk bodyResult final =>
        simpa [bodyRun] using evaluate_run_ioEvents_prefix [body] (values ++ env) last final bodyResult bodyRun

/-- A let is trace-monotone in clock when its bindings and body are. -/
theorem evaluate_let_addClock_ioEvents_step {C F : Type} (bindings : List Bvi.Exp) (body : Bvi.Exp) (env : List Value) (state : BviState C F) (extra : Nat)
    (bindingsIH : (evaluate bindings env state).2.ffi.ioEvents <+:
      (evaluate bindings env { state with clock := state.clock + extra }).2.ffi.ioEvents)
    (bodyIH : ∀ (bodyEnv : List Value) (start : BviState C F), start.clock ≤ state.clock →
      (evaluate [body] bodyEnv start).2.ffi.ioEvents <+:
        (evaluate [body] bodyEnv { start with clock := start.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.let bindings body] env state).2.ffi.ioEvents <+:
      (evaluate [.let bindings body] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  cases run : evaluate [.let bindings body] env state with
  | mk result final =>
    by_cases timeout : result = .err (.abort .timeoutError)
    · subst result
      have sourceRun := run
      rw [evaluate, fixClock_evaluate] at sourceRun
      cases bindingsRun : evaluate bindings env state with
      | mk bindingResult last =>
        have bound : last.clock ≤ state.clock := by
          have clock := evaluate_clock_le bindings env state
          simpa [bindingsRun] using clock
        rw [bindingsRun] at sourceRun
        cases bindingResult with
        | err error =>
          simp at sourceRun
          rcases sourceRun with ⟨_, rfl⟩
          have bindingPrefix : last.ffi.ioEvents <+:
              (evaluate bindings env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
            simpa [bindingsRun] using bindingsIH
          exact bindingPrefix.trans (evaluate_let_bindings_ioEvents_prefix bindings body env
            { state with clock := state.clock + extra })
        | val values =>
          have shiftedBindings := evaluate_addClock bindings env state last (.val values) extra bindingsRun (by simp)
          have compare := bodyIH (values ++ env) last bound
          rw [evaluate, fixClock_evaluate, shiftedBindings]
          dsimp only
          dsimp only at sourceRun
          simp only [sourceRun] at compare
          exact compare
    · have equal := evaluate_addClock_ioEvents_of_notTimeout [.let bindings body] env state final result extra run timeout
      simp only [run] at equal
      rw [equal]

/-- Raising changes the result but keeps the event trace produced by its body. -/
theorem evaluate_raise_ioEvents_eq {C F : Type} (body : Bvi.Exp)
    (env : List Value) (state : BviState C F) :
    (evaluate [.raise body] env state).2.ffi.ioEvents = (evaluate [body] env state).2.ffi.ioEvents := by
  rw [evaluate]
  cases bodyRun : evaluate [body] env state with
  | mk result last => cases result <;> rfl

/-- Cross-clock trace comparison for a raise reduces to its body. -/
theorem evaluate_raise_addClock_ioEvents_step {C F : Type} (body : Bvi.Exp)
    (env : List Value) (state : BviState C F) (extra : Nat)
    (bodyIH : (evaluate [body] env state).2.ffi.ioEvents <+:
      (evaluate [body] env { state with clock := state.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.raise body] env state).2.ffi.ioEvents <+:
      (evaluate [.raise body] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  rw [evaluate_raise_ioEvents_eq, evaluate_raise_ioEvents_eq]
  exact bodyIH

/-- A tick is trace-monotone in clock when its body is. -/
theorem evaluate_tick_addClock_ioEvents_step {C F : Type} (body : Bvi.Exp)
    (env : List Value) (state : BviState C F) (extra : Nat)
    (bodyIH : ∀ (start : BviState C F), start.clock < state.clock →
      (evaluate [body] env start).2.ffi.ioEvents <+:
        (evaluate [body] env { start with clock := start.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.tick body] env state).2.ffi.ioEvents <+:
      (evaluate [.tick body] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  by_cases zero : state.clock = 0
  · have sourceTrace : (evaluate [.tick body] env state).2.ffi.ioEvents = state.ffi.ioEvents := by
      simp [evaluate, zero]
    rw [sourceTrace]
    cases targetRun : evaluate [.tick body] env { state with clock := state.clock + extra } with
    | mk result final =>
      simpa using evaluate_run_ioEvents_prefix [.tick body] env
        { state with clock := state.clock + extra } final result targetRun
  · have smaller : (decClock 1 state).clock < state.clock := by simp [decClock]; omega
    have compare := bodyIH (decClock 1 state) smaller
    have shifted : decClock 1 { state with clock := state.clock + extra } =
        { decClock 1 state with clock := (decClock 1 state).clock + extra } := by
      simp only [decClock]
      congr 1
      omega
    rw [evaluate, evaluate]
    simp only [zero, ↓reduceIte]
    have shiftedNonzero : state.clock + extra ≠ 0 := by omega
    simp only [shiftedNonzero, ↓reduceIte, shifted]
    exact compare


/-- The first expression's events are a prefix of a longer list's events. -/
theorem evaluate_list_head_ioEvents_prefix {C F : Type} (first second : Bvi.Exp) (tail : List Bvi.Exp)
    (env : List Value) (state : BviState C F) :
    (evaluate [first] env state).2.ffi.ioEvents <+:
      (evaluate (first :: second :: tail) env state).2.ffi.ioEvents := by
  rw [evaluate, fixClock_evaluate]
  cases headRun : evaluate [first] env state with
  | mk headResult last =>
    cases headResult with
    | err error => simp
    | val values =>
      cases tailRun : evaluate (second :: tail) env last with
      | mk tailResult final =>
        cases tailResult <;> simpa [tailRun] using
          evaluate_run_ioEvents_prefix (second :: tail) env last final _ tailRun

/-- Longer expression lists are trace-monotone when head and tail are. -/
theorem evaluate_list_addClock_ioEvents_step {C F : Type} (first second : Bvi.Exp) (tail : List Bvi.Exp)
    (env : List Value) (state : BviState C F) (extra : Nat)
    (headIH : (evaluate [first] env state).2.ffi.ioEvents <+:
      (evaluate [first] env { state with clock := state.clock + extra }).2.ffi.ioEvents)
    (tailIH : ∀ (start : BviState C F), start.clock ≤ state.clock →
      (evaluate (second :: tail) env start).2.ffi.ioEvents <+:
        (evaluate (second :: tail) env { start with clock := start.clock + extra }).2.ffi.ioEvents) :
    (evaluate (first :: second :: tail) env state).2.ffi.ioEvents <+:
      (evaluate (first :: second :: tail) env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  cases run : evaluate (first :: second :: tail) env state with
  | mk result final =>
    by_cases timeout : result = .err (.abort .timeoutError)
    · subst result
      have sourceRun := run
      rw [evaluate, fixClock_evaluate] at sourceRun
      cases headRun : evaluate [first] env state with
      | mk headResult last =>
        have bound : last.clock ≤ state.clock := by
          have clock := evaluate_clock_le [first] env state
          simpa [headRun] using clock
        rw [headRun] at sourceRun
        cases headResult with
        | err error =>
          simp at sourceRun
          rcases sourceRun with ⟨_, rfl⟩
          have headPrefix : last.ffi.ioEvents <+:
              (evaluate [first] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
            simpa [headRun] using headIH
          exact headPrefix.trans (evaluate_list_head_ioEvents_prefix first second tail env
            { state with clock := state.clock + extra })
        | val values =>
          have shiftedHead := evaluate_addClock [first] env state last (.val values) extra headRun (by simp)
          have compare := tailIH last bound
          cases tailRun : evaluate (second :: tail) env last with
          | mk tailResult tailFinal =>
            rw [tailRun] at sourceRun
            cases tailResult with
            | val tailValues => simp at sourceRun
            | err error =>
              simp at sourceRun
              rcases sourceRun with ⟨_, rfl⟩
              rw [evaluate, fixClock_evaluate, shiftedHead]
              cases targetRun : evaluate (second :: tail) env { last with clock := last.clock + extra } with
              | mk targetResult targetFinal =>
                cases targetResult <;> simpa [tailRun, targetRun] using compare
    · have equal := evaluate_addClock_ioEvents_of_notTimeout (first :: second :: tail) env state final result extra run timeout
      simp only [run] at equal
      rw [equal]


/-- Forced-thunk traces are monotone when selected body traces are. -/
theorem evaluate_force_addClock_ioEvents_step {C F : Type} (location index : Nat)
    (env : List Value) (state : BviState C F) (extra : Nat)
    (bodyIH : ∀ (body : Bvi.Exp) (bodyEnv : List Value) (start : BviState C F), start.clock < state.clock →
      (evaluate [body] bodyEnv start).2.ffi.ioEvents <+:
        (evaluate [body] bodyEnv { start with clock := start.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.force location index] env state).2.ffi.ioEvents <+:
      (evaluate [.force location index] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  by_cases zero : state.clock = 0
  · have source : (evaluate [.force location index] env state).2.ffi.ioEvents = state.ffi.ioEvents := by
      rw [evaluate]
      repeat' (split <;> try simp_all)
    rw [source]
    cases targetRun : evaluate [.force location index] env { state with clock := state.clock + extra } with
    | mk result final =>
      simpa using evaluate_run_ioEvents_prefix [.force location index] env
        { state with clock := state.clock + extra } final result targetRun
  · cases found : env[index]? with
    | none => simp [evaluate, found]
    | some thunk =>
      cases inspected : destThunk thunk state.refs with
      | badRef | notThunk => simp [evaluate, found, inspected]
      | isThunk mode value =>
        cases mode with
        | evaluated => simp [evaluate, found, inspected]
        | notEvaluated =>
          cases selected : findCode (some location) [thunk, value] state.code with
          | none => simp [evaluate, found, inspected, selected]
          | some entry =>
            rcases entry with ⟨args, body⟩
            have smaller : (decClock 1 state).clock < state.clock := by simp [decClock]; omega
            have compare := bodyIH body args (decClock 1 state) smaller
            have shifted : decClock 1 { state with clock := state.clock + extra } =
                { decClock 1 state with clock := (decClock 1 state).clock + extra } := by
              simp only [decClock]
              congr 1
              omega
            have shiftedNonzero : state.clock + extra ≠ 0 := by omega
            cases bodyRun : evaluate [body] args (decClock 1 state) with
            | mk bodyResult bodyNext =>
              cases targetRun : evaluate [body] args { decClock 1 state with
                  clock := (decClock 1 state).clock + extra } with
              | mk targetResult targetNext =>
                cases bodyResult <;> cases targetResult <;>
                  simp_all [evaluate]
                all_goals repeat' (split <;> simp_all)


end Flapjack.Compiler.Backend.BviProps
