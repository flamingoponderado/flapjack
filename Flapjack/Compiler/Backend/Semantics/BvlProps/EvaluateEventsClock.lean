import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateClockShift
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateEvents
import Flapjack.Compiler.Backend.Semantics.BvlProps.ApplyError

/-! BVL trace comparisons across clocks; proof cases have no standalone HOL declarations. -/
namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem Flapjack.SemanticPrimitivesHOL

namespace EventsClockCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end EventsClockCarrier

/-- A non-timeout evaluation has the same events after clock extension. -/
theorem evaluate_addClock_ioEvents_of_notTimeout {C F : Type} (expressions : List Bvl.Exp)
    (env : List BvlSem.Value) (state next : State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value) (extra : Nat)
    (run : evaluate expressions env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    (evaluate expressions env state).2.ffi.ioEvents =
      (evaluate expressions env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  have shifted := evaluate_addClock expressions env state next result extra run notTimeout
  simp [run, shifted]

/-- The trace of a let binding is a prefix of the entire let trace. -/
theorem evaluate_let_bindings_ioEvents_prefix {C F : Type} (bindings : List Bvl.Exp) (body : Bvl.Exp) (env : List BvlSem.Value) (state : State C F) :
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
        simpa [bodyRun] using evaluate_ioEvents_prefix [body] (values ++ env) last final bodyResult bodyRun

/-- A let is trace-monotone in clock when its bindings and body are. -/
theorem evaluate_let_addClock_ioEvents_step {C F : Type} (bindings : List Bvl.Exp) (body : Bvl.Exp) (env : List BvlSem.Value) (state : State C F) (extra : Nat)
    (bindingsIH : (evaluate bindings env state).2.ffi.ioEvents <+:
      (evaluate bindings env { state with clock := state.clock + extra }).2.ffi.ioEvents)
    (bodyIH : ∀ (bodyEnv : List BvlSem.Value) (start : State C F), start.clock ≤ state.clock →
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
      exact List.prefix_refl _

/-- Raising changes the result but keeps the event trace produced by its body. -/
theorem evaluate_raise_ioEvents_eq {C F : Type} (body : Bvl.Exp)
    (env : List BvlSem.Value) (state : State C F) :
    (evaluate [.raise body] env state).2.ffi.ioEvents = (evaluate [body] env state).2.ffi.ioEvents := by
  rw [evaluate]
  cases bodyRun : evaluate [body] env state with
  | mk result last => cases result <;> rfl

/-- Cross-clock trace comparison for a raise reduces to its body. -/
theorem evaluate_raise_addClock_ioEvents_step {C F : Type} (body : Bvl.Exp)
    (env : List BvlSem.Value) (state : State C F) (extra : Nat)
    (bodyIH : (evaluate [body] env state).2.ffi.ioEvents <+:
      (evaluate [body] env { state with clock := state.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.raise body] env state).2.ffi.ioEvents <+:
      (evaluate [.raise body] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  rw [evaluate_raise_ioEvents_eq, evaluate_raise_ioEvents_eq]
  exact bodyIH

/-- A tick is trace-monotone in clock when its body is. -/
theorem evaluate_tick_addClock_ioEvents_step {C F : Type} (body : Bvl.Exp)
    (env : List BvlSem.Value) (state : State C F) (extra : Nat)
    (bodyIH : ∀ (start : State C F), start.clock < state.clock →
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
      simpa using evaluate_ioEvents_prefix [.tick body] env
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


/-- The condition's trace is a prefix of the complete conditional trace. -/
theorem evaluate_if_condition_ioEvents_prefix {C F : Type} (condition yes no : Bvl.Exp) (env : List BvlSem.Value) (state : State C F) :
    (evaluate [condition] env state).2.ffi.ioEvents <+:
      (evaluate [.ifThenElse condition yes no] env state).2.ffi.ioEvents := by
  rw [evaluate, fixClock_evaluate]
  cases conditionRun : evaluate [condition] env state with
  | mk testResult last =>
    cases testResult with
    | err error => simp
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton condition env state last values conditionRun
      dsimp only
      cases boolRun : asBool value with
      | none => simp [boolRun]
      | some choice =>
        cases choice with
        | false =>
          cases branchRun : evaluate [no] env last with
          | mk branchResult final =>
            simpa [boolRun, branchRun] using evaluate_ioEvents_prefix [no] env last final branchResult branchRun
        | true =>
          cases branchRun : evaluate [yes] env last with
          | mk branchResult final =>
            simpa [boolRun, branchRun] using evaluate_ioEvents_prefix [yes] env last final branchResult branchRun

/-- Conditional traces are monotone in clock when their conditions and
selected branches are. -/
theorem evaluate_if_addClock_ioEvents_step {C F : Type} (condition yes no : Bvl.Exp) (env : List BvlSem.Value) (state : State C F) (extra : Nat)
    (conditionIH : (evaluate [condition] env state).2.ffi.ioEvents <+:
      (evaluate [condition] env { state with clock := state.clock + extra }).2.ffi.ioEvents)
    (branchIH : ∀ (choice : Bool) (start : State C F), start.clock ≤ state.clock →
      (evaluate [if choice then yes else no] env start).2.ffi.ioEvents <+:
        (evaluate [if choice then yes else no] env { start with clock := start.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.ifThenElse condition yes no] env state).2.ffi.ioEvents <+:
      (evaluate [.ifThenElse condition yes no] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  cases run : evaluate [.ifThenElse condition yes no] env state with
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
          exact testPrefix.trans (evaluate_if_condition_ioEvents_prefix condition yes no env
            { state with clock := state.clock + extra })
        | val values =>
          obtain ⟨value, rfl⟩ := evaluate_singleton condition env state last values conditionRun
          have shiftedTest := evaluate_addClock [condition] env state last (.val [value]) extra conditionRun (by simp)
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
    · have equal := evaluate_addClock_ioEvents_of_notTimeout [.ifThenElse condition yes no] env state final result extra run timeout
      simp only [run] at equal
      rw [equal]
      exact List.prefix_refl _

/-- The body trace is a prefix of the complete handler trace. -/
theorem evaluate_handle_body_ioEvents_prefix {C F : Type} (body handler : Bvl.Exp) (env : List BvlSem.Value) (state : State C F) :
    (evaluate [body] env state).2.ffi.ioEvents <+:
      (evaluate [.handle body handler] env state).2.ffi.ioEvents := by
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
          simpa [handlerRun] using evaluate_ioEvents_prefix [handler] (value :: env) last final handlerResult handlerRun

/-- Handler traces are monotone in clock when the body and handler are. -/
theorem evaluate_handle_addClock_ioEvents_step {C F : Type} (body handler : Bvl.Exp) (env : List BvlSem.Value) (state : State C F) (extra : Nat)
    (bodyIH : (evaluate [body] env state).2.ffi.ioEvents <+:
      (evaluate [body] env { state with clock := state.clock + extra }).2.ffi.ioEvents)
    (handlerIH : ∀ (value : BvlSem.Value) (start : State C F), start.clock ≤ state.clock →
      (evaluate [handler] (value :: env) start).2.ffi.ioEvents <+:
        (evaluate [handler] (value :: env) { start with clock := start.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.handle body handler] env state).2.ffi.ioEvents <+:
      (evaluate [.handle body handler] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  cases run : evaluate [.handle body handler] env state with
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
          exact bodyPrefix.trans (evaluate_handle_body_ioEvents_prefix body handler env
            { state with clock := state.clock + extra })
        · have shiftedBody := evaluate_addClock [body] env state last bodyResult extra bodyRun bodyTimeout
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
    · have equal := evaluate_addClock_ioEvents_of_notTimeout [.handle body handler] env state final result extra run timeout
      simp only [run] at equal
      rw [equal]
      exact List.prefix_refl _

/-- A direct call extends the trace of its argument evaluation. -/
theorem evaluate_call_args_ioEvents_prefix {C F : Type} (ticks : Nat) (location : Option Nat) (args : List Bvl.Exp) (env : List BvlSem.Value) (state : State C F) :
    (evaluate args env state).2.ffi.ioEvents <+:
      (evaluate [.call ticks location args] env state).2.ffi.ioEvents := by
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
            simpa [decClock, bodyRun] using evaluate_ioEvents_prefix [body] bodyEnv
              (decClock (ticks + 1) last) final bodyResult bodyRun

/-- A direct call is trace-monotone when its arguments and selected code
body are trace-monotone. -/
theorem evaluate_call_addClock_ioEvents_step {C F : Type} (ticks : Nat) (location : Option Nat) (args : List Bvl.Exp) (env : List BvlSem.Value) (state : State C F) (extra : Nat)
    (argsIH : (evaluate args env state).2.ffi.ioEvents <+:
      (evaluate args env { state with clock := state.clock + extra }).2.ffi.ioEvents)
    (bodyIH : ∀ (body : Bvl.Exp) (bodyEnv : List BvlSem.Value) (start : State C F), start.clock < state.clock →
      (evaluate [body] bodyEnv start).2.ffi.ioEvents <+:
        (evaluate [body] bodyEnv { start with clock := start.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.call ticks location args] env state).2.ffi.ioEvents <+:
      (evaluate [.call ticks location args] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  cases run : evaluate [.call ticks location args] env state with
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
          exact argsPrefix.trans (evaluate_call_args_ioEvents_prefix ticks location args env
            { state with clock := state.clock + extra })
        | val arguments =>
          have shiftedArgs := evaluate_addClock args env state last (.val arguments) extra argsRun (by simp)
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
              exact argsPrefix.trans (evaluate_call_args_ioEvents_prefix ticks location args env
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
    · have equal := evaluate_addClock_ioEvents_of_notTimeout [.call ticks location args] env state final result extra run timeout
      simp only [run] at equal
      rw [equal]
      exact List.prefix_refl _


/-- Primitive dispatch itself cannot time out. -/
theorem doApp_not_timeout {C F : Type} (op : ClosLang.Op) (args : List BvlSem.Value)
    (state : State C F) : doApp op args state ≠ .err (.abort .timeoutError) := by
  intro run
  have error := doAppError op args state (.abort .timeoutError) run
  rcases error with error | ⟨name, outcome, _, error⟩ <;> cases error

/-- The argument trace is a prefix of its primitive application trace. -/
theorem evaluate_op_args_ioEvents_prefix {C F : Type} (op : ClosLang.Op) (args : List Bvl.Exp)
    (env : List BvlSem.Value) (state : State C F) :
    (evaluate args env state).2.ffi.ioEvents <+:
      (evaluate [.op op args] env state).2.ffi.ioEvents := by
  rw [evaluate, fixClock_evaluate]
  cases argsRun : evaluate args env state with
  | mk argResult last =>
    cases argResult with
    | err error => simp
    | val arguments =>
      cases appRun : doApp op arguments.reverse last with
      | err error => simp [appRun]
      | val pair =>
        rcases pair with ⟨value, next⟩
        simpa [appRun] using doApp_ioEvents_prefix op arguments.reverse last next value appRun

/-- A primitive operation is trace-monotone when its arguments are. -/
theorem evaluate_op_addClock_ioEvents_step {C F : Type} (op : ClosLang.Op) (args : List Bvl.Exp)
    (env : List BvlSem.Value) (state : State C F) (extra : Nat)
    (argsIH : (evaluate args env state).2.ffi.ioEvents <+:
      (evaluate args env { state with clock := state.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.op op args] env state).2.ffi.ioEvents <+:
      (evaluate [.op op args] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  cases run : evaluate [.op op args] env state with
  | mk result final =>
    by_cases timeout : result = .err (.abort .timeoutError)
    · subst result
      have sourceRun := run
      rw [evaluate, fixClock_evaluate] at sourceRun
      cases argsRun : evaluate args env state with
      | mk argResult last =>
        rw [argsRun] at sourceRun
        cases argResult with
        | err error =>
          simp at sourceRun
          rcases sourceRun with ⟨_, rfl⟩
          have argPrefix : last.ffi.ioEvents <+:
              (evaluate args env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
            simpa [argsRun] using argsIH
          exact argPrefix.trans (evaluate_op_args_ioEvents_prefix op args env
            { state with clock := state.clock + extra })
        | val values =>
          cases appRun : doApp op values.reverse last with
          | err error =>
            simp [appRun] at sourceRun
            have impossible : error = .abort .timeoutError := sourceRun.1
            subst error
            exact (doApp_not_timeout op values.reverse last appRun).elim
          | val pair => simp [appRun] at sourceRun
    · have equal := evaluate_addClock_ioEvents_of_notTimeout [.op op args] env state final result extra run timeout
      simp only [run] at equal
      rw [equal]
      exact List.prefix_refl _

/-- The first expression's events are a prefix of a longer list's events. -/
theorem evaluate_list_head_ioEvents_prefix {C F : Type} (first second : Bvl.Exp) (tail : List Bvl.Exp)
    (env : List BvlSem.Value) (state : State C F) :
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
          evaluate_ioEvents_prefix (second :: tail) env last final _ tailRun

/-- Longer expression lists are trace-monotone when head and tail are. -/
theorem evaluate_list_addClock_ioEvents_step {C F : Type} (first second : Bvl.Exp) (tail : List Bvl.Exp)
    (env : List BvlSem.Value) (state : State C F) (extra : Nat)
    (headIH : (evaluate [first] env state).2.ffi.ioEvents <+:
      (evaluate [first] env { state with clock := state.clock + extra }).2.ffi.ioEvents)
    (tailIH : ∀ (start : State C F), start.clock ≤ state.clock →
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
      exact List.prefix_refl _

/-- Forced-thunk traces are monotone when selected body traces are. -/
theorem evaluate_force_addClock_ioEvents_step {C F : Type} (location index : Nat)
    (env : List BvlSem.Value) (state : State C F) (extra : Nat)
    (bodyIH : ∀ (body : Bvl.Exp) (bodyEnv : List BvlSem.Value) (start : State C F), start.clock < state.clock →
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
      simpa using evaluate_ioEvents_prefix [.force location index] env
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
            simpa [evaluate, found, inspected, selected, zero, shiftedNonzero, shifted] using compare

/-- BVL traces grow monotonically as more clock is supplied. -/
theorem evaluate_addClock_ioEvents_prefix {C F : Type} (expressions : List Bvl.Exp)
    (env : List BvlSem.Value) (state : State C F) (extra : Nat) :
    (evaluate expressions env state).2.ffi.ioEvents <+:
      (evaluate expressions env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  have allRanks : ∀ clock weight : Nat, ∀ (expressions : List Bvl.Exp)
      (env : List BvlSem.Value) (state : State C F), state.clock = clock → expsWeight expressions = weight →
      ∀ extra, (evaluate expressions env state).2.ffi.ioEvents <+:
        (evaluate expressions env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (expressions : List Bvl.Exp) (env : List BvlSem.Value) (state : State C F),
            state.clock ≤ clock → expsWeight expressions < weight → ∀ extra,
            (evaluate expressions env state).2.ffi.ioEvents <+:
              (evaluate expressions env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
          intro expressions env state clockLe weightLt extra
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact clockIH state.clock clockLt (expsWeight expressions) expressions env state rfl rfl extra
          · exact weightIH (expsWeight expressions) weightLt expressions env state clockEq rfl extra
        have smaller : ∀ (expressions : List Bvl.Exp) (env : List BvlSem.Value) (state : State C F),
            state.clock < clock → ∀ extra, (evaluate expressions env state).2.ffi.ioEvents <+:
              (evaluate expressions env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
          intro expressions env state clockLt extra
          exact clockIH state.clock clockLt (expsWeight expressions) expressions env state rfl rfl extra
        intro expressions env state stateClock measure extra
        cases expressions with
        | nil => simp [evaluate]
        | cons first rest =>
          cases rest with
          | cons second tail =>
            apply evaluate_list_addClock_ioEvents_step first second tail env state extra ?_ ?_
            · apply exprIH [first] env state (by omega) ?_ extra
              simp only [expsWeight] at measure ⊢; have := expWeight_pos second; omega
            · intro start bound
              apply exprIH (second :: tail) env start (by omega) ?_ extra
              simp only [expsWeight] at measure ⊢; omega
          | nil =>
            cases first with
            | var index =>
              rw [evaluate, evaluate]
              split <;> simp
            | raise body =>
              apply evaluate_raise_addClock_ioEvents_step body env state extra
              apply exprIH [body] env state (by omega) ?_ extra
              simp only [expsWeight, expWeight] at measure ⊢; omega
            | tick body =>
              apply evaluate_tick_addClock_ioEvents_step body env state extra
              intro start bound
              exact smaller [body] env start (by omega) extra
            | «let» bindings body =>
              apply evaluate_let_addClock_ioEvents_step bindings body env state extra ?_ ?_
              · apply exprIH bindings env state (by omega) ?_ extra
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro bodyEnv start bound
                apply exprIH [body] bodyEnv start (by omega) ?_ extra
                simp only [expsWeight, expWeight] at measure ⊢; omega
            | handle body handler =>
              apply evaluate_handle_addClock_ioEvents_step body handler env state extra ?_ ?_
              · apply exprIH [body] env state (by omega) ?_ extra
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro value start bound
                apply exprIH [handler] (value :: env) start (by omega) ?_ extra
                simp only [expsWeight, expWeight] at measure ⊢; omega
            | ifThenElse condition yes no =>
              apply evaluate_if_addClock_ioEvents_step condition yes no env state extra ?_ ?_
              · apply exprIH [condition] env state (by omega) ?_ extra
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro choice start bound
                apply exprIH [if choice then yes else no] env start (by omega) ?_ extra
                cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte, expsWeight, expWeight] at measure ⊢ <;> omega
            | op op args =>
              apply evaluate_op_addClock_ioEvents_step op args env state extra
              apply exprIH args env state (by omega) ?_ extra
              simp only [expsWeight, expWeight] at measure ⊢; omega
            | call ticks location args =>
              apply evaluate_call_addClock_ioEvents_step ticks location args env state extra ?_ ?_
              · apply exprIH args env state (by omega) ?_ extra
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro body bodyEnv start bound
                exact smaller [body] bodyEnv start (by omega) extra
            | force location index =>
              apply evaluate_force_addClock_ioEvents_step location index env state extra
              intro body bodyEnv start bound
              exact smaller [body] bodyEnv start (by omega) extra
  exact allRanks state.clock (expsWeight expressions) expressions env state rfl rfl extra

/-- Increasing the clock extends the observable event trace. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_add_to_clock_io_events_mono"
  (fmap_as_finite_support := [refs])]
theorem evaluateAddToClockIoEventsMono {C F : Type} (expressions : List Bvl.Exp)
    (env : List BvlSem.Value) (state : Flapjack.Compiler.Backend.BvlSem.State C F) (extra : Nat) :
    (evaluateTuple (expressions, env, state)).2.ffi.ioEvents <+:
      (evaluateTuple (expressions, env, incClock extra state)).2.ffi.ioEvents :=
  evaluate_addClock_ioEvents_prefix expressions env state extra

end Flapjack.Compiler.Backend.BvlProps
