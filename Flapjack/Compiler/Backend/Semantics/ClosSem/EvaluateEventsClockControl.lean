import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateEventsClock

/-! Cross-clock control-flow trace comparisons for the proof-side evaluator. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- The condition's trace is a prefix of the complete conditional trace. -/
theorem evaluate_if_condition_ioEvents_prefix {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (env : List Value) (state : State C F) :
    (evaluate [condition] env state).2.ffi.ioEvents <+:
      (evaluate [.ifThenElse trace condition yes no] env state).2.ffi.ioEvents := by
  rw [evaluate, fixClock_evaluate]
  cases conditionRun : evaluate [condition] env state with
  | mk testResult last =>
    cases testResult with
    | err error => simp
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value condition env state last values conditionRun
      dsimp only
      cases boolRun : asBool value with
      | none => simp [boolRun]
      | some choice =>
        cases choice with
        | false =>
          cases branchRun : evaluate [no] env last with
          | mk branchResult final =>
            simpa [boolRun, branchRun] using evaluate_ioEvents_prefix.1 [no] env last final branchResult branchRun
        | true =>
          cases branchRun : evaluate [yes] env last with
          | mk branchResult final =>
            simpa [boolRun, branchRun] using evaluate_ioEvents_prefix.1 [yes] env last final branchResult branchRun

/-- Conditional traces are monotone in clock when their conditions and
selected branches are. -/
theorem evaluate_if_addClock_ioEvents_step {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (env : List Value) (state : State C F) (extra : Nat)
    (conditionIH : (evaluate [condition] env state).2.ffi.ioEvents <+:
      (evaluate [condition] env { state with clock := state.clock + extra }).2.ffi.ioEvents)
    (branchIH : ∀ (choice : Bool) (start : State C F), start.clock ≤ state.clock →
      (evaluate [if choice then yes else no] env start).2.ffi.ioEvents <+:
        (evaluate [if choice then yes else no] env { start with clock := start.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.ifThenElse trace condition yes no] env state).2.ffi.ioEvents <+:
      (evaluate [.ifThenElse trace condition yes no] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  cases run : evaluate [.ifThenElse trace condition yes no] env state with
  | mk result final =>
    by_cases timeout : result = .err (.abort .timeoutError)
    · subst result
      have sourceRun := run
      rw [evaluate, fixClock_evaluate] at sourceRun
      cases conditionRun : evaluate [condition] env state with
      | mk testResult last =>
        have bound : last.clock ≤ state.clock := by
          have clock := evaluate_clock_le [condition] env state
          simpa [conditionRun] using clock
        rw [conditionRun] at sourceRun
        cases testResult with
        | err error =>
          simp at sourceRun
          rcases sourceRun with ⟨_, rfl⟩
          have testPrefix : last.ffi.ioEvents <+:
              (evaluate [condition] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
            simpa [conditionRun] using conditionIH
          exact testPrefix.trans (evaluate_if_condition_ioEvents_prefix trace condition yes no env
            { state with clock := state.clock + extra })
        | val values =>
          obtain ⟨value, rfl⟩ := evaluate_singleton_value condition env state last values conditionRun
          have shiftedTest := evaluate_addClock.1 [condition] env state last (.val [value]) extra conditionRun (by simp)
          dsimp only at sourceRun
          cases boolRun : asBool value with
          | none => simp [boolRun] at sourceRun
          | some choice =>
            cases choice with
            | false =>
              simp [boolRun] at sourceRun
              have compare := branchIH false last bound
              simp only [Bool.false_eq_true, ↓reduceIte] at compare
              rw [sourceRun] at compare
              rw [evaluate, fixClock_evaluate, shiftedTest]
              simpa [boolRun] using compare
            | true =>
              simp [boolRun] at sourceRun
              have compare := branchIH true last bound
              simp only [↓reduceIte] at compare
              rw [sourceRun] at compare
              rw [evaluate, fixClock_evaluate, shiftedTest]
              simpa [boolRun] using compare
    · have equal := evaluate_addClock_ioEvents_of_notTimeout [.ifThenElse trace condition yes no] env state final result extra run timeout
      simp only [run] at equal
      rw [equal]
      exact List.prefix_refl _

/-- The body trace is a prefix of the complete handler trace. -/
theorem evaluate_handle_body_ioEvents_prefix {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (env : List Value) (state : State C F) :
    (evaluate [body] env state).2.ffi.ioEvents <+:
      (evaluate [.handle trace body handler] env state).2.ffi.ioEvents := by
  rw [evaluate, fixClock_evaluate]
  cases bodyRun : evaluate [body] env state with
  | mk bodyResult last =>
    cases bodyResult with
    | val values => simp
    | err error =>
      cases error with
      | abort reason => simp
      | raise value =>
        cases handlerRun : evaluate [handler] (value :: env) last with
        | mk handlerResult final =>
          simpa [handlerRun] using evaluate_ioEvents_prefix.1 [handler] (value :: env) last final handlerResult handlerRun

/-- Handler traces are monotone in clock when the body and handler are. -/
theorem evaluate_handle_addClock_ioEvents_step {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (env : List Value) (state : State C F) (extra : Nat)
    (bodyIH : (evaluate [body] env state).2.ffi.ioEvents <+:
      (evaluate [body] env { state with clock := state.clock + extra }).2.ffi.ioEvents)
    (handlerIH : ∀ (value : Value) (start : State C F), start.clock ≤ state.clock →
      (evaluate [handler] (value :: env) start).2.ffi.ioEvents <+:
        (evaluate [handler] (value :: env) { start with clock := start.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.handle trace body handler] env state).2.ffi.ioEvents <+:
      (evaluate [.handle trace body handler] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  cases run : evaluate [.handle trace body handler] env state with
  | mk result final =>
    by_cases timeout : result = .err (.abort .timeoutError)
    · subst result
      have sourceRun := run
      rw [evaluate, fixClock_evaluate] at sourceRun
      cases bodyRun : evaluate [body] env state with
      | mk bodyResult last =>
        have bound : last.clock ≤ state.clock := by
          have clock := evaluate_clock_le [body] env state
          simpa [bodyRun] using clock
        rw [bodyRun] at sourceRun
        by_cases bodyTimeout : bodyResult = .err (.abort .timeoutError)
        · subst bodyResult
          have bodyPrefix : last.ffi.ioEvents <+:
              (evaluate [body] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
            simpa [bodyRun] using bodyIH
          simp at sourceRun
          rcases sourceRun with ⟨_, rfl⟩
          exact bodyPrefix.trans (evaluate_handle_body_ioEvents_prefix trace body handler env
            { state with clock := state.clock + extra })
        · have shiftedBody := evaluate_addClock.1 [body] env state last bodyResult extra bodyRun bodyTimeout
          cases bodyResult with
          | val values => simp at sourceRun
          | err error =>
            cases error with
            | abort reason =>
              simp at sourceRun
              rcases sourceRun with ⟨rfl, _⟩
              exact (bodyTimeout rfl).elim
            | raise value =>
              dsimp only at sourceRun
              have compare := handlerIH value last bound
              rw [sourceRun] at compare
              rw [evaluate, fixClock_evaluate, shiftedBody]
              exact compare
    · have equal := evaluate_addClock_ioEvents_of_notTimeout [.handle trace body handler] env state final result extra run timeout
      simp only [run] at equal
      rw [equal]
      exact List.prefix_refl _

/-- A direct call extends the trace of its argument evaluation. -/
theorem evaluate_call_args_ioEvents_prefix {C F : Type} (trace : BackendCommon.Tra)
    (ticks location : Nat) (args : List ClosLang.Exp) (env : List Value) (state : State C F) :
    (evaluate args env state).2.ffi.ioEvents <+:
      (evaluate [.call trace ticks location args] env state).2.ffi.ioEvents := by
  rw [evaluate, fixClock_evaluate]
  cases argsRun : evaluate args env state with
  | mk argResult last =>
    cases argResult with
    | err error => simp
    | val arguments =>
      dsimp only
      cases found : findCode location arguments last.code with
      | none => simp
      | some entry =>
        rcases entry with ⟨bodyEnv, body⟩
        dsimp only
        split
        · simp
        · cases bodyRun : evaluate [body] bodyEnv (decClock (ticks + 1) last) with
          | mk bodyResult final =>
            simpa [decClock, bodyRun] using evaluate_ioEvents_prefix.1 [body] bodyEnv
              (decClock (ticks + 1) last) final bodyResult bodyRun

/-- A direct call is trace-monotone when its arguments and selected code
body are trace-monotone. -/
theorem evaluate_call_addClock_ioEvents_step {C F : Type} (trace : BackendCommon.Tra)
    (ticks location : Nat) (args : List ClosLang.Exp) (env : List Value) (state : State C F) (extra : Nat)
    (argsIH : (evaluate args env state).2.ffi.ioEvents <+:
      (evaluate args env { state with clock := state.clock + extra }).2.ffi.ioEvents)
    (bodyIH : ∀ (body : ClosLang.Exp) (bodyEnv : List Value) (start : State C F), start.clock < state.clock →
      (evaluate [body] bodyEnv start).2.ffi.ioEvents <+:
        (evaluate [body] bodyEnv { start with clock := start.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.call trace ticks location args] env state).2.ffi.ioEvents <+:
      (evaluate [.call trace ticks location args] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  cases run : evaluate [.call trace ticks location args] env state with
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
          exact argsPrefix.trans (evaluate_call_args_ioEvents_prefix trace ticks location args env
            { state with clock := state.clock + extra })
        | val arguments =>
          have shiftedArgs := evaluate_addClock.1 args env state last (.val arguments) extra argsRun (by simp)
          dsimp only at sourceRun
          cases found : findCode location arguments last.code with
          | none => simp [found] at sourceRun
          | some entry =>
            rcases entry with ⟨bodyEnv, body⟩
            rw [found] at sourceRun
            dsimp only at sourceRun
            by_cases short : last.clock < ticks + 1
            · rw [if_pos short] at sourceRun
              simp at sourceRun
              rcases sourceRun with ⟨_, rfl⟩
              have argsPrefix : last.ffi.ioEvents <+:
                  (evaluate args env { state with clock := state.clock + extra }).2.ffi.ioEvents := by simpa [argsRun] using argsIH
              exact argsPrefix.trans (evaluate_call_args_ioEvents_prefix trace ticks location args env
                { state with clock := state.clock + extra })
            · rw [if_neg short] at sourceRun
              have smaller : (decClock (ticks + 1) last).clock < state.clock := by simp [decClock]; omega
              have compare := bodyIH body bodyEnv (decClock (ticks + 1) last) smaller
              rw [sourceRun] at compare
              have shifted : decClock (ticks + 1) { last with clock := last.clock + extra } =
                  { decClock (ticks + 1) last with clock := (decClock (ticks + 1) last).clock + extra } := by
                simp only [decClock]
                congr 1
                omega
              rw [evaluate, fixClock_evaluate, shiftedArgs]
              dsimp only
              rw [found]
              dsimp only
              rw [if_neg (by omega), shifted]
              exact compare
    · have equal := evaluate_addClock_ioEvents_of_notTimeout [.call trace ticks location args] env state final result extra run timeout
      simp only [run] at equal
      rw [equal]
      exact List.prefix_refl _

end Flapjack.Compiler.Backend.ClosSem
