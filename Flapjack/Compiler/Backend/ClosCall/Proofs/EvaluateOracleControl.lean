import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateControlWellformed

/-! Preservation of empty oracle auxiliary output by closure evaluator
control-flow cases. These induction steps are Flapjack proof infrastructure,
not ports of a HOL declaration. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL

/-- Empty lists and variable lookup leave the oracle unchanged. -/
theorem evaluate_nil_oracleAuxEmpty {C F : Type} (env : List ClosSem.Value) (state : ClosSem.State C F)
    (empty : OracleAuxEmpty state.compileOracle) :
    OracleAuxEmpty (evaluate [] env state).2.compileOracle := by
  simpa [evaluate] using empty

theorem evaluate_var_oracleAuxEmpty {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (env : List ClosSem.Value) (state : ClosSem.State C F) (empty : OracleAuxEmpty state.compileOracle) :
    OracleAuxEmpty (evaluate [.var trace index] env state).2.compileOracle := by
  cases found : env[index]? <;> simpa [evaluate, found] using empty

/-- Creating a closure does not consult or change the compiler oracle. -/
theorem evaluate_fn_oracleAuxEmpty {C F : Type}
    (name : Flapjack.Basis.Pure.MlString.MlString) (loc : Option Nat) (arity : Nat)
    (selected : Option (List Nat)) (body : ClosLang.Exp) (env : List ClosSem.Value)
    (state : ClosSem.State C F) (empty : OracleAuxEmpty state.compileOracle) :
    OracleAuxEmpty (evaluate [.fn name loc selected arity body] env state).2.compileOracle := by
  by_cases valid : arity ≤ state.maxApp ∧ arity ≠ 0
  · cases selected with
    | none => simpa [evaluate, valid] using empty
    | some indices => cases found : lookupVars indices env <;> simpa [evaluate, valid, found] using empty
  · cases selected <;> simpa [evaluate, valid] using empty

/-- Raising propagates the oracle produced by evaluation of its argument. -/
theorem evaluate_raise_oracleAuxEmpty {C F : Type} (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (bodyIH : OracleAuxEmpty (evaluate [body] env state).2.compileOracle) :
    OracleAuxEmpty (evaluate [.raise trace body] env state).2.compileOracle := by
  cases run : evaluate [body] env state with
  | mk result final =>
    rw [run] at bodyIH
    rw [evaluate, run]
    cases result <;> exact bodyIH

/-- Let-bindings pass the updated oracle to their body. -/
theorem evaluate_let_oracleAuxEmpty {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (bindingsIH : OracleAuxEmpty (evaluate bindings env state).2.compileOracle)
    (bodyIH : ∀ (bodyEnv : List ClosSem.Value) (start : ClosSem.State C F),
      OracleAuxEmpty start.compileOracle → OracleAuxEmpty (evaluate [body] bodyEnv start).2.compileOracle) :
    OracleAuxEmpty (evaluate [.let trace bindings body] env state).2.compileOracle := by
  cases run : evaluate bindings env state with
  | mk result final =>
    rw [run] at bindingsIH
    rw [evaluate, fixClock_evaluate, run]
    cases result with
    | err error => exact bindingsIH
    | val values => exact bodyIH (values ++ env) final bindingsIH

/-- Handlers preserve the oracle produced before an exception is raised. -/
theorem evaluate_handle_oracleAuxEmpty {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (bodyIH : OracleAuxEmpty (evaluate [body] env state).2.compileOracle)
    (handlerIH : ∀ (bodyEnv : List ClosSem.Value) (start : ClosSem.State C F),
      OracleAuxEmpty start.compileOracle → OracleAuxEmpty (evaluate [handler] bodyEnv start).2.compileOracle) :
    OracleAuxEmpty (evaluate [.handle trace body handler] env state).2.compileOracle := by
  cases run : evaluate [body] env state with
  | mk result final =>
    rw [run] at bodyIH
    rw [evaluate, fixClock_evaluate, run]
    cases result with
    | val values => exact bodyIH
    | err error =>
      cases error with
      | abort reason => exact bodyIH
      | raise value => exact handlerIH (value :: env) final bodyIH

/-- Both conditional branches start with the condition's resulting oracle. -/
theorem evaluate_if_oracleAuxEmpty {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (conditionIH : OracleAuxEmpty (evaluate [condition] env state).2.compileOracle)
    (yesIH : ∀ (start : ClosSem.State C F), OracleAuxEmpty start.compileOracle →
      OracleAuxEmpty (evaluate [yes] env start).2.compileOracle)
    (noIH : ∀ (start : ClosSem.State C F), OracleAuxEmpty start.compileOracle →
      OracleAuxEmpty (evaluate [no] env start).2.compileOracle) :
    OracleAuxEmpty (evaluate [.ifThenElse trace condition yes no] env state).2.compileOracle := by
  cases run : evaluate [condition] env state with
  | mk result final =>
    rw [run] at conditionIH
    rw [evaluate, fixClock_evaluate, run]
    cases result with
    | err error => exact conditionIH
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value condition env state final values run
      cases choice : asBool value with
      | none => simpa [choice] using conditionIH
      | some flag =>
        cases flag with
        | false => simpa [choice] using noIH final conditionIH
        | true => simpa [choice] using yesIH final conditionIH

/-- Sequencing passes the first expression's oracle to the remaining list. -/
theorem evaluate_cons_oracleAuxEmpty {C F : Type} (first second : ClosLang.Exp)
    (rest : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (headIH : OracleAuxEmpty (evaluate [first] env state).2.compileOracle)
    (tailIH : ∀ (start : ClosSem.State C F), OracleAuxEmpty start.compileOracle →
      OracleAuxEmpty (evaluate (second :: rest) env start).2.compileOracle) :
    OracleAuxEmpty (evaluate (first :: second :: rest) env state).2.compileOracle := by
  cases run : evaluate [first] env state with
  | mk result final =>
    rw [run] at headIH
    rw [evaluate, fixClock_evaluate, run]
    cases result with
    | err error => exact headIH
    | val values =>
      cases tailRun : evaluate (second :: rest) env final with
      | mk tailResult tailFinal =>
        have tailEmpty := tailIH final headIH
        rw [tailRun] at tailEmpty
        cases tailResult <;> exact tailEmpty

/-- Application passes the oracle through argument and function evaluation. -/
theorem evaluate_app_oracleAuxEmpty {C F : Type} (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (stateEmpty : OracleAuxEmpty state.compileOracle)
    (argsIH : OracleAuxEmpty (evaluate args env state).2.compileOracle)
    (fnIH : ∀ (start : ClosSem.State C F), OracleAuxEmpty start.compileOracle →
      OracleAuxEmpty (evaluate [function] env start).2.compileOracle)
    (appIH : ∀ (value : ClosSem.Value) (values : List ClosSem.Value) (start : ClosSem.State C F),
      OracleAuxEmpty start.compileOracle → OracleAuxEmpty (evaluateApp location value values start).2.compileOracle) :
    OracleAuxEmpty (evaluate [.app trace location function args] env state).2.compileOracle := by
  cases args with
  | nil => simpa [evaluate] using stateEmpty
  | cons first rest =>
    cases run : evaluate (first :: rest) env state with
    | mk result final =>
      rw [run] at argsIH
      rw [evaluate]
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      rw [fixClock_evaluate, run]
      cases result with
      | err error => exact argsIH
      | val values =>
        rw [fixClock_evaluate]
        have fnEmpty := fnIH final argsIH
        cases fnRun : evaluate [function] env final with
        | mk fnResult fnFinal =>
          rw [fnRun] at fnEmpty
          cases fnResult with
          | err error => exact fnEmpty
          | val fnValues =>
            obtain ⟨fnValue, rfl⟩ := evaluate_singleton_value function env final fnFinal fnValues fnRun
            simpa using appIH fnValue values fnFinal fnEmpty

/-- A closure application preserves oracle emptiness if body evaluation and
subsequent applications do so at smaller clocks. -/
theorem evaluateApp_oracleAuxEmpty_step {C F : Type} (location : Option Nat)
    (function : ClosSem.Value) (args : List ClosSem.Value) (state : ClosSem.State C F)
    (stateEmpty : OracleAuxEmpty state.compileOracle)
    (bodyIH : ∀ (body : ClosLang.Exp) (env : List ClosSem.Value) (start : ClosSem.State C F),
      start.clock < state.clock → OracleAuxEmpty start.compileOracle →
      OracleAuxEmpty (evaluate [body] env start).2.compileOracle)
    (appIH : ∀ (value : ClosSem.Value) (rest : List ClosSem.Value) (start : ClosSem.State C F),
      start.clock < state.clock → OracleAuxEmpty start.compileOracle →
      OracleAuxEmpty (evaluateApp location value rest start).2.compileOracle) :
    OracleAuxEmpty (evaluateApp location function args state).2.compileOracle := by
  cases args with
  | nil => simpa [evaluateApp] using stateEmpty
  | cons first rest =>
    rw [evaluateApp]
    cases found : destClosure state.maxApp location function (first :: rest) with
    | none => simpa using stateEmpty
    | some kind =>
      cases kind with
      | partialApp value =>
        dsimp only
        split <;> simpa [decClock] using stateEmpty
      | fullApp body bodyEnv remaining =>
        have remainingLt := destClosure_full_remaining_lt state.maxApp location function (first :: rest)
          bodyEnv remaining body found
        let cost := (first :: rest).length - remaining.length
        have costPositive : 0 < cost := Nat.sub_pos_of_lt remainingLt
        dsimp only
        split
        · simpa using stateEmpty
        · rename_i enough
          rw [fixClock_evaluate]
          have smaller : (decClock cost state).clock < state.clock := by simp [decClock]; omega
          have bodyEmpty := bodyIH body bodyEnv (decClock cost state) smaller stateEmpty
          cases run : evaluate [body] bodyEnv (decClock cost state) with
          | mk result final =>
            rw [run] at bodyEmpty
            have bodyBound : final.clock ≤ (decClock cost state).clock := by
              have bound := evaluate_clock_le [body] bodyEnv (decClock cost state)
              simpa [run] using bound
            cases result with
            | err error => exact bodyEmpty
            | val values =>
              obtain ⟨value, rfl⟩ := evaluate_singleton_value body bodyEnv (decClock cost state) final values run
              exact appIH value remaining final (by omega) bodyEmpty

/-- A clock tick does not itself modify the oracle. -/
theorem evaluate_tick_oracleAuxEmpty {C F : Type} (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (stateEmpty : OracleAuxEmpty state.compileOracle)
    (bodyIH : OracleAuxEmpty (evaluate [body] env (decClock 1 state)).2.compileOracle) :
    OracleAuxEmpty (evaluate [.tick trace body] env state).2.compileOracle := by
  rw [evaluate]
  by_cases zero : state.clock = 0
  · simpa [zero] using stateEmpty
  · simpa [zero] using bodyIH

/-- A direct call passes its arguments' oracle to the called code. -/
theorem evaluate_call_oracleAuxEmpty {C F : Type} (trace : BackendCommon.Tra)
    (ticks label : Nat) (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (argsIH : OracleAuxEmpty (evaluate args env state).2.compileOracle)
    (bodyIH : ∀ (body : ClosLang.Exp) (bodyEnv : List ClosSem.Value) (start : ClosSem.State C F),
      OracleAuxEmpty start.compileOracle → OracleAuxEmpty (evaluate [body] bodyEnv start).2.compileOracle) :
    OracleAuxEmpty (evaluate [.call trace ticks label args] env state).2.compileOracle := by
  cases run : evaluate args env state with
  | mk result final =>
    rw [run] at argsIH
    rw [evaluate, fixClock_evaluate, run]
    cases result with
    | err error => exact argsIH
    | val values =>
      cases found : findCode label values final.code with
      | none => simpa [found] using argsIH
      | some pair =>
        obtain ⟨bodyEnv, body⟩ := pair
        simp only [found]
        split
        · simpa using argsIH
        · exact bodyIH body bodyEnv (decClock (ticks + 1) final) argsIH

/-- Recursive binding construction leaves the oracle unchanged before the body. -/
theorem evaluate_letrec_oracleAuxEmpty {C F : Type}
    (names : List Flapjack.Basis.Pure.MlString.MlString) (loc : Option Nat)
    (selected : Option (List Nat)) (fns : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (env : List ClosSem.Value) (state : ClosSem.State C F) (stateEmpty : OracleAuxEmpty state.compileOracle)
    (bodyIH : ∀ bodyEnv, OracleAuxEmpty (evaluate [body] bodyEnv state).2.compileOracle) :
    OracleAuxEmpty (evaluate [.letrec names loc selected fns body] env state).2.compileOracle := by
  rw [evaluate.eq_def]
  by_cases valid : fns.all (fun (arity, _) => arity ≤ state.maxApp && arity != 0) = true
  · simp only [valid, ↓reduceIte]
    cases selected with
    | none => exact bodyIH _
    | some indices =>
      cases found : lookupVars indices env with
      | none => simpa [found] using stateEmpty
      | some captured => simpa [found] using bodyIH _
  · simpa [valid] using stateEmpty

end Flapjack.Compiler.Backend.ClosCall
