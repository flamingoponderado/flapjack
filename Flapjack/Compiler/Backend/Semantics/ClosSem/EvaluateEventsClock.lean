import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateEventsFull

/-! Clock-extension event-prefix steps for the proof-side closure evaluator.
The evaluator and its carriers await HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- A completed head evaluation is a prefix of the complete sequence trace. -/
theorem evaluate_cons_head_ioEvents_prefix {C F : Type} (head : ClosLang.Exp) (tail : List ClosLang.Exp)
    (env : List Value) (state : State C F) :
    (evaluate [head] env state).2.ffi.ioEvents <+: (evaluate (head :: tail) env state).2.ffi.ioEvents := by
  cases headRun : evaluate [head] env state with
  | mk headResult last =>
    cases headResult with
    | err error =>
      rw [ClosProps.evaluate_cons_error head tail env state last error headRun]
      simp
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value head env state last values headRun
      rw [ClosProps.evaluate_cons_value head tail env state last value headRun]
      cases tailRun : evaluate tail env last with
      | mk tailResult final =>
        cases tailResult <;> simpa using evaluate_ioEvents_prefix.1 tail env last final _ tailRun

/-- Cross-clock trace comparison for a sequence, assuming the head and tail
comparisons. -/
theorem evaluate_cons_addClock_ioEvents_step {C F : Type} (head : ClosLang.Exp) (tail : List ClosLang.Exp)
    (env : List Value) (state : State C F) (extra : Nat)
    (headIH : (evaluate [head] env state).2.ffi.ioEvents <+:
      (evaluate [head] env { state with clock := state.clock + extra }).2.ffi.ioEvents)
    (tailIH : ∀ (start : State C F), start.clock ≤ state.clock →
      (evaluate tail env start).2.ffi.ioEvents <+:
        (evaluate tail env { start with clock := start.clock + extra }).2.ffi.ioEvents) :
    (evaluate (head :: tail) env state).2.ffi.ioEvents <+:
      (evaluate (head :: tail) env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  cases run : evaluate (head :: tail) env state with
  | mk result final =>
    by_cases timeout : result = .err (.abort .timeoutError)
    · subst result
      cases headRun : evaluate [head] env state with
      | mk headResult last =>
        cases headResult with
        | err error =>
          have sourceRun := ClosProps.evaluate_cons_error head tail env state last error headRun
          rw [sourceRun] at run
          simp at run
          rcases run with ⟨rfl, rfl⟩
          have headPrefix : last.ffi.ioEvents <+:
              (evaluate [head] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
            simpa [headRun] using headIH
          have sequencePrefix := evaluate_cons_head_ioEvents_prefix head tail env { state with clock := state.clock + extra }
          simpa [sourceRun] using headPrefix.trans sequencePrefix
        | val values =>
          obtain ⟨value, rfl⟩ := evaluate_singleton_value head env state last values headRun
          have bound : last.clock ≤ state.clock := by
            have clock := evaluate_clock_le [head] env state
            simpa [headRun] using clock
          have shiftedHead := evaluate_addClock.1 [head] env state last (.val [value]) extra headRun (by simp)
          have sourceSequence := ClosProps.evaluate_cons_value head tail env state last value headRun
          have targetSequence := ClosProps.evaluate_cons_value head tail env { state with clock := state.clock + extra }
            { last with clock := last.clock + extra } value shiftedHead
          have compare := tailIH last bound
          cases sourceTail : evaluate tail env last with
          | mk sourceResult sourceLast =>
            cases targetTail : evaluate tail env { last with clock := last.clock + extra } with
            | mk targetResult targetLast =>
              rw [sourceTail] at sourceSequence
              rw [targetTail] at targetSequence
              cases sourceResult <;> cases targetResult <;> simp_all
    · have equal := evaluate_addClock_ioEvents_of_notTimeout (head :: tail) env state final result extra run timeout
      simp only [run] at equal
      rw [equal]
      exact List.prefix_refl _

/-- Evaluating an ordinary operation extends the trace produced by its
arguments. -/
theorem evaluate_ordinaryOp_args_ioEvents_prefix {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List Value) (state : State C F)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk) :
    (evaluate args env state).2.ffi.ioEvents <+:
      (evaluate [.op trace op args] env state).2.ffi.ioEvents := by
  rw [evaluate_ordinaryOp_eq trace op args env state notInstall notForce]
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

/-- An ordinary operation is trace-monotone in clock whenever its arguments
are; its own dispatcher cannot time out. -/
theorem evaluate_ordinaryOp_addClock_ioEvents_step {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List Value) (state : State C F) (extra : Nat)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : (evaluate args env state).2.ffi.ioEvents <+:
      (evaluate args env { state with clock := state.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.op trace op args] env state).2.ffi.ioEvents <+:
      (evaluate [.op trace op args] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  cases run : evaluate [.op trace op args] env state with
  | mk result final =>
    by_cases timeout : result = .err (.abort .timeoutError)
    · subst result
      have sourceRun := run
      rw [evaluate_ordinaryOp_eq trace op args env state notInstall notForce] at sourceRun
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
          have continuation := evaluate_ordinaryOp_args_ioEvents_prefix trace op args env
            { state with clock := state.clock + extra } notInstall notForce
          exact argPrefix.trans continuation
        | val values =>
          cases appRun : doApp op values.reverse last with
          | err error =>
            simp [appRun] at sourceRun
            have impossible : error = .abort .timeoutError := sourceRun.1
            subst error
            exact (doApp_not_timeout op values.reverse last appRun).elim
          | val pair => simp [appRun] at sourceRun
    · have equal := evaluate_addClock_ioEvents_of_notTimeout [.op trace op args] env state final result extra run timeout
      simp only [run] at equal
      rw [equal]
      exact List.prefix_refl _

/-- The trace of a let binding is a prefix of the entire let trace. -/
theorem evaluate_let_bindings_ioEvents_prefix {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (env : List Value) (state : State C F) :
    (evaluate bindings env state).2.ffi.ioEvents <+:
      (evaluate [.let trace bindings body] env state).2.ffi.ioEvents := by
  rw [evaluate, fixClock_evaluate]
  cases bindingsRun : evaluate bindings env state with
  | mk bindingResult last =>
    cases bindingResult with
    | err error => simp
    | val values =>
      cases bodyRun : evaluate [body] (values ++ env) last with
      | mk bodyResult final =>
        simpa [bodyRun] using evaluate_ioEvents_prefix.1 [body] (values ++ env) last final bodyResult bodyRun

/-- A let is trace-monotone in clock when its bindings and body are. -/
theorem evaluate_let_addClock_ioEvents_step {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (env : List Value) (state : State C F) (extra : Nat)
    (bindingsIH : (evaluate bindings env state).2.ffi.ioEvents <+:
      (evaluate bindings env { state with clock := state.clock + extra }).2.ffi.ioEvents)
    (bodyIH : ∀ (bodyEnv : List Value) (start : State C F), start.clock ≤ state.clock →
      (evaluate [body] bodyEnv start).2.ffi.ioEvents <+:
        (evaluate [body] bodyEnv { start with clock := start.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.let trace bindings body] env state).2.ffi.ioEvents <+:
      (evaluate [.let trace bindings body] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  cases run : evaluate [.let trace bindings body] env state with
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
          exact bindingPrefix.trans (evaluate_let_bindings_ioEvents_prefix trace bindings body env
            { state with clock := state.clock + extra })
        | val values =>
          have shiftedBindings := evaluate_addClock.1 bindings env state last (.val values) extra bindingsRun (by simp)
          have compare := bodyIH (values ++ env) last bound
          rw [evaluate, fixClock_evaluate, shiftedBindings]
          dsimp only
          dsimp only at sourceRun
          simp only [sourceRun] at compare
          exact compare
    · have equal := evaluate_addClock_ioEvents_of_notTimeout [.let trace bindings body] env state final result extra run timeout
      simp only [run] at equal
      rw [equal]
      exact List.prefix_refl _

/-- Raising changes the result but keeps the event trace produced by its body. -/
theorem evaluate_raise_ioEvents_eq {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (env : List Value) (state : State C F) :
    (evaluate [.raise trace body] env state).2.ffi.ioEvents = (evaluate [body] env state).2.ffi.ioEvents := by
  rw [evaluate]
  cases bodyRun : evaluate [body] env state with
  | mk result last => cases result <;> rfl

/-- Cross-clock trace comparison for a raise reduces to its body. -/
theorem evaluate_raise_addClock_ioEvents_step {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (env : List Value) (state : State C F) (extra : Nat)
    (bodyIH : (evaluate [body] env state).2.ffi.ioEvents <+:
      (evaluate [body] env { state with clock := state.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.raise trace body] env state).2.ffi.ioEvents <+:
      (evaluate [.raise trace body] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  rw [evaluate_raise_ioEvents_eq, evaluate_raise_ioEvents_eq]
  exact bodyIH

/-- A tick is trace-monotone in clock when its body is. -/
theorem evaluate_tick_addClock_ioEvents_step {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (env : List Value) (state : State C F) (extra : Nat)
    (bodyIH : ∀ (start : State C F), start.clock < state.clock →
      (evaluate [body] env start).2.ffi.ioEvents <+:
        (evaluate [body] env { start with clock := start.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.tick trace body] env state).2.ffi.ioEvents <+:
      (evaluate [.tick trace body] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  by_cases zero : state.clock = 0
  · have sourceTrace : (evaluate [.tick trace body] env state).2.ffi.ioEvents = state.ffi.ioEvents := by
      simp [evaluate, zero]
    rw [sourceTrace]
    cases targetRun : evaluate [.tick trace body] env { state with clock := state.clock + extra } with
    | mk result final =>
      simpa using evaluate_ioEvents_prefix.1 [.tick trace body] env
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

/-- Recursive bindings do not affect the event trace before their body, so
their clock comparison reduces to comparing that body. -/
theorem evaluate_letrec_addClock_ioEvents_step {C F : Type} (names : List Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat)) (functions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (env : List Value) (state : State C F) (extra : Nat)
    (bodyIH : ∀ (bodyEnv : List Value),
      (evaluate [body] bodyEnv state).2.ffi.ioEvents <+:
        (evaluate [body] bodyEnv { state with clock := state.clock + extra }).2.ffi.ioEvents) :
    (evaluate [.letrec names location selected functions body] env state).2.ffi.ioEvents <+:
      (evaluate [.letrec names location selected functions body] env { state with clock := state.clock + extra }).2.ffi.ioEvents := by
  by_cases good : functions.all (fun (arity, _) => arity ≤ state.maxApp && arity != 0) = true
  · cases selected with
    | none =>
      rw [evaluate.eq_def, evaluate.eq_def]
      dsimp only
      rw [if_pos good, if_pos good]
      exact bodyIH _
    | some selected =>
      cases captured : lookupVars selected env with
      | none =>
        rw [evaluate.eq_def, evaluate.eq_def]
        dsimp only
        rw [if_pos good, if_pos good, captured]
        simp
      | some values =>
        rw [evaluate.eq_def, evaluate.eq_def]
        dsimp only
        rw [if_pos good, if_pos good, captured]
        exact bodyIH _
  · rw [evaluate.eq_def, evaluate.eq_def]
    dsimp only
    rw [if_neg good, if_neg good]
    simp

end Flapjack.Compiler.Backend.ClosSem
