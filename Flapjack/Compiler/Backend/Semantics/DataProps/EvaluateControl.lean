import Flapjack.Compiler.Backend.Semantics.DataSem.EvaluateClock

/-! Control preservation for continuing data-language executions. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- A continuing assignment preserves the stack and handler, including when
the primitive installs code. This is one case of the still-open general
evaluator control-preservation result. -/
theorem evaluate_assign_stack_handler {C F : Type} (dest : Nat) (op : ClosLang.Op) (names : List Nat)
    (live : Option NumSet) (state next : State C F)
    (run : evaluate (.assign dest op names live) state = (none, next)) :
    next.stack = state.stack ∧ next.handler = state.handler := by
  by_cases invalid : (DataLang.opRequiresNames op == live.isNone) = true
  · simp [evaluate, invalid] at run
  · cases read : getVars names state.locals with
    | none => simp [evaluate, invalid, read] at run
    | some args =>
      cases cut : cutStateOpt live state with
      | none => simp [evaluate, invalid, read, cut] at run
      | some prepared =>
        have cutControl := cutStateOpt_control live state prepared cut
        cases app : doApp op args prepared with
        | err error => simp [evaluate, invalid, read, cut, app] at run
        | val pair =>
          obtain ⟨value, applied⟩ := pair
          have frame := doApp_controlFrame op args prepared applied value app
          have appControl : applied.stack = prepared.stack ∧ applied.handler = prepared.handler :=
            ⟨frame.2.1, frame.2.2.1⟩
          simp [evaluate, invalid, read, cut, app] at run
          subst next
          exact ⟨appControl.1.trans cutControl.1, appControl.2.trans cutControl.2.1⟩

/-- Continuing simple instructions preserve the stack and handler. These
are auxiliary cases of the general evaluator preservation result. -/
theorem evaluate_skip_stack_handler {C F : Type} (state next : State C F)
    (run : evaluate .skip state = (none, next)) : next.stack = state.stack ∧ next.handler = state.handler := by
  simp [evaluate] at run
  subst next
  exact ⟨rfl, rfl⟩

theorem evaluate_move_stack_handler {C F : Type} (dest src : Nat) (state next : State C F)
    (run : evaluate (.move dest src) state = (none, next)) :
    next.stack = state.stack ∧ next.handler = state.handler := by
  cases read : getVar src state.locals with
  | none => simp [evaluate, read] at run
  | some value =>
    simp [evaluate, read] at run
    subst next
    exact ⟨rfl, rfl⟩

theorem evaluate_tick_stack_handler {C F : Type} (state next : State C F)
    (run : evaluate .tick state = (none, next)) : next.stack = state.stack ∧ next.handler = state.handler := by
  by_cases zero : state.clock = 0
  · simp [evaluate, zero] at run
  · simp [evaluate, zero] at run
    subst next
    exact ⟨rfl, rfl⟩

theorem evaluate_makeSpace_stack_handler {C F : Type} (amount : Nat) (names : NumSet)
    (state next : State C F) (run : evaluate (.makeSpace amount names) state = (none, next)) :
    next.stack = state.stack ∧ next.handler = state.handler := by
  exact ⟨(evaluate_makeSpace_control amount names state next run).1,
    (evaluate_makeSpace_control amount names state next run).2.1⟩

theorem evaluate_raise_stack_handler {C F : Type} (name : Nat) (state next : State C F)
    (run : evaluate (.raise name) state = (none, next)) : next.stack = state.stack ∧ next.handler = state.handler := by
  cases read : getVar name state.locals with
  | none => simp [evaluate, read] at run
  | some value =>
    cases jump : jumpExc state <;> simp [evaluate, read, jump] at run

theorem evaluate_return_stack_handler {C F : Type} (names : List Nat) (state next : State C F)
    (run : evaluate (.return names) state = (none, next)) : next.stack = state.stack ∧ next.handler = state.handler := by
  cases read : getVars names state.locals <;> simp [evaluate, read] at run

/-- Continuing sequence preservation follows from both component cases. -/
theorem evaluate_seq_stack_handler {C F : Type} (first second : DataLang.Prog) (state next : State C F)
    (firstControl : ∀ before after : State C F, evaluate first before = (none, after) →
      after.stack = before.stack ∧ after.handler = before.handler)
    (secondControl : ∀ before after : State C F, evaluate second before = (none, after) →
      after.stack = before.stack ∧ after.handler = before.handler)
    (run : evaluate (.seq first second) state = (none, next)) :
    next.stack = state.stack ∧ next.handler = state.handler := by
  rw [evaluate, fixClock_evaluate] at run
  cases firstRun : evaluate first state with
  | mk result mid =>
    rw [firstRun] at run
    cases result with
    | some outcome => simp at run
    | none =>
      have before := firstControl state mid firstRun
      have after := secondControl mid next run
      exact ⟨after.1.trans before.1, after.2.trans before.2⟩

/-- Continuing conditional preservation follows from both branch cases. -/
theorem evaluate_if_stack_handler {C F : Type} (name : Nat) (yes no : DataLang.Prog) (state next : State C F)
    (yesControl : ∀ before after : State C F, evaluate yes before = (none, after) →
      after.stack = before.stack ∧ after.handler = before.handler)
    (noControl : ∀ before after : State C F, evaluate no before = (none, after) →
      after.stack = before.stack ∧ after.handler = before.handler)
    (run : evaluate (.ifThenElse name yes no) state = (none, next)) :
    next.stack = state.stack ∧ next.handler = state.handler := by
  cases read : getVar name state.locals with
  | none => simp [evaluate, read] at run
  | some value =>
    by_cases yes : isBool true value
    · apply yesControl state next
      simpa [evaluate, read, yes] using run
    · by_cases no : isBool false value
      · apply noControl state next
        simpa [evaluate, read, yes, no] using run
      · simp [evaluate, read, yes, no] at run

end Flapjack.Compiler.Backend.DataSem
