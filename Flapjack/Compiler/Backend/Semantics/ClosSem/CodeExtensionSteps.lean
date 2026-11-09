module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.CodeExtensionPrimitive
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength

@[expose] public section

/-! Structural evaluator steps under a safe code extension. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- Empty expression lists are unaffected by extra code. -/
theorem evaluate_nil_codeExtension {C F : Type} (source : State C F) : EvalCodeExtensionAt source [] := by
  intro env target result next run noType states
  simp [evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨target, by simp [evaluate], states⟩

/-- Variables are unaffected by extra code. -/
theorem evaluate_var_codeExtension {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (source : State C F) : EvalCodeExtensionAt source [.var trace index] := by
  intro env target result next run noType states
  cases lookup : env[index]? with
  | none =>
    simp [evaluate, lookup] at run
    exact False.elim (noType run.1.symm)
  | some value =>
    simp [evaluate, lookup] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨target, by simp [evaluate, lookup], states⟩

/-- Closure creation is unaffected by extra code. -/
theorem evaluate_fn_codeExtension {C F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (location : Option Nat) (selected : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp)
    (source : State C F) : EvalCodeExtensionAt source [.fn name location selected arity body] := by
  intro env target result next run noType states
  have maxEq : target.maxApp = source.maxApp := by rw [states.1]
  rw [evaluate.eq_def] at run ⊢
  dsimp only at run ⊢
  simp only [maxEq]
  repeat' split at run <;> simp_all

/-- Sequence two or more expressions under a safe code extension. -/
theorem evaluate_cons_codeExtension {C F : Type} (first second : ClosLang.Exp) (rest : List ClosLang.Exp)
    (source : State C F) (firstIH : EvalCodeExtensionAt source [first])
    (restIH : ∀ state : State C F, state.clock ≤ source.clock → EvalCodeExtensionAt state (second :: rest)) :
    EvalCodeExtensionAt source (first :: second :: rest) := by
  intro env target result next run noType states
  rw [evaluate, fixClock_evaluate] at run
  cases firstRun : evaluate [first] env source with
  | mk firstResult middle =>
    have middleClock : middle.clock ≤ source.clock := by
      have h := evaluate_clock_le [first] env source
      simpa [firstRun] using h
    rw [firstRun] at run
    cases firstResult with
    | err error =>
      cases run
      obtain ⟨targetMiddle, targetRun, related⟩ := firstIH env target (.err error) middle firstRun noType states
      refine ⟨targetMiddle, ?_, related⟩
      rw [evaluate, fixClock_evaluate, targetRun]
    | val values =>
      have firstNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetMiddle, targetRun, related⟩ := firstIH env target (.val values) middle firstRun firstNoType states
      dsimp only at run
      cases restRun : evaluate (second :: rest) env middle with
      | mk restResult last =>
        rw [restRun] at run
        cases restResult with
        | err error =>
          cases run
          obtain ⟨targetLast, targetRest, lastRel⟩ :=
            restIH middle middleClock env targetMiddle (.err error) last restRun noType related
          refine ⟨targetLast, ?_, lastRel⟩
          rw [evaluate, fixClock_evaluate, targetRun, targetRest]
        | val tailValues =>
          cases run
          have restNoType : (Result.val tailValues : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
          obtain ⟨targetLast, targetRest, lastRel⟩ :=
            restIH middle middleClock env targetMiddle (.val tailValues) last restRun restNoType related
          refine ⟨targetLast, ?_, lastRel⟩
          rw [evaluate, fixClock_evaluate, targetRun, targetRest]

/-- Raising an expression preserves the extension simulation. -/
theorem evaluate_raise_codeExtension {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (source : State C F) (bodyIH : EvalCodeExtensionAt source [body]) :
    EvalCodeExtensionAt source [.raise trace body] := by
  intro env target result next run noType states
  cases bodyRun : evaluate [body] env source with
  | mk bodyResult middle =>
    have bodyNoType : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      simp [evaluate, bodyRun] at run
      exact noType run.1.symm
    obtain ⟨targetMiddle, targetRun, middleRel⟩ := bodyIH env target bodyResult middle bodyRun bodyNoType states
    cases bodyResult <;> simp [evaluate, bodyRun] at run <;> obtain ⟨rfl, rfl⟩ := run <;>
      refine ⟨targetMiddle, ?_, middleRel⟩ <;> simp [evaluate, targetRun]

/-- A tick preserves the extension after decrementing both clocks. -/
theorem evaluate_tick_codeExtension {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (source : State C F) (bodyIH : EvalCodeExtensionAt (decClock 1 source) [body]) :
    EvalCodeExtensionAt source [.tick trace body] := by
  intro env target result next run noType states
  have clockEq : target.clock = source.clock := by rw [states.1]
  by_cases zero : source.clock = 0
  · simp [evaluate, zero] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨target, by simp [evaluate, clockEq, zero], states⟩
  · have bodyRun : evaluate [body] env (decClock 1 source) = (result, next) := by simpa [evaluate, zero] using run
    obtain ⟨targetNext, targetRun, nextRel⟩ :=
      bodyIH env (decClock 1 target) result next bodyRun noType (codeExtension_decClock source target 1 states)
    exact ⟨targetNext, by simpa [evaluate, clockEq, zero] using targetRun, nextRel⟩

/-- Let bindings and their body preserve the code-extension simulation. -/
theorem evaluate_let_codeExtension {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (source : State C F)
    (bindingsIH : EvalCodeExtensionAt source bindings)
    (bodyIH : ∀ state : State C F, state.clock ≤ source.clock → EvalCodeExtensionAt state [body]) :
    EvalCodeExtensionAt source [.let trace bindings body] := by
  intro env target result next run noType states
  rw [evaluate, fixClock_evaluate] at run
  cases bindingsRun : evaluate bindings env source with
  | mk bindingsResult middle =>
    have middleClock : middle.clock ≤ source.clock := by
      have h := evaluate_clock_le bindings env source
      simpa [bindingsRun] using h
    rw [bindingsRun] at run
    cases bindingsResult with
    | err error =>
      cases run
      obtain ⟨targetMiddle, targetRun, related⟩ := bindingsIH env target (.err error) middle bindingsRun noType states
      refine ⟨targetMiddle, ?_, related⟩
      rw [evaluate, fixClock_evaluate, targetRun]
    | val values =>
      have notType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetMiddle, targetRun, related⟩ := bindingsIH env target (.val values) middle bindingsRun notType states
      obtain ⟨targetNext, targetBody, nextRel⟩ := bodyIH middle middleClock (values ++ env) targetMiddle result next run noType related
      refine ⟨targetNext, ?_, nextRel⟩
      rw [evaluate, fixClock_evaluate, targetRun]
      exact targetBody

/-- Exception handlers preserve the extension relation. -/
theorem evaluate_handle_codeExtension {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (source : State C F) (bodyIH : EvalCodeExtensionAt source [body])
    (handlerIH : ∀ state : State C F, state.clock ≤ source.clock → EvalCodeExtensionAt state [handler]) :
    EvalCodeExtensionAt source [.handle trace body handler] := by
  intro env target result next run noType states
  rw [evaluate, fixClock_evaluate] at run
  cases bodyRun : evaluate [body] env source with
  | mk bodyResult middle =>
    have middleClock : middle.clock ≤ source.clock := by
      have h := evaluate_clock_le [body] env source
      simpa [bodyRun] using h
    rw [bodyRun] at run
    have bodyNoType : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      cases run
      exact noType rfl
    obtain ⟨targetMiddle, targetRun, related⟩ := bodyIH env target bodyResult middle bodyRun bodyNoType states
    cases bodyResult with
    | val values =>
      cases run
      exact ⟨targetMiddle, by rw [evaluate, fixClock_evaluate, targetRun], related⟩
    | err error =>
      cases error with
      | abort reason =>
        cases run
        exact ⟨targetMiddle, by rw [evaluate, fixClock_evaluate, targetRun], related⟩
      | raise value =>
        obtain ⟨targetNext, targetHandler, nextRel⟩ :=
          handlerIH middle middleClock (value :: env) targetMiddle result next run noType related
        refine ⟨targetNext, ?_, nextRel⟩
        rw [evaluate, fixClock_evaluate, targetRun]
        exact targetHandler

/-- A conditional follows the same branch under a code extension. -/
theorem evaluate_if_codeExtension {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (source : State C F) (conditionIH : EvalCodeExtensionAt source [condition])
    (yesIH : ∀ state : State C F, state.clock ≤ source.clock → EvalCodeExtensionAt state [yes])
    (noIH : ∀ state : State C F, state.clock ≤ source.clock → EvalCodeExtensionAt state [no]) :
    EvalCodeExtensionAt source [.ifThenElse trace condition yes no] := by
  intro env target result next run noType states
  rw [evaluate, fixClock_evaluate] at run
  cases testRun : evaluate [condition] env source with
  | mk testResult middle =>
    have middleClock : middle.clock ≤ source.clock := by
      have h := evaluate_clock_le [condition] env source
      simpa [testRun] using h
    rw [testRun] at run
    cases testResult with
    | err error =>
      cases run
      obtain ⟨targetMiddle, targetRun, related⟩ := conditionIH env target (.err error) middle testRun noType states
      exact ⟨targetMiddle, by rw [evaluate, fixClock_evaluate, targetRun], related⟩
    | val values =>
      have notType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetMiddle, targetRun, related⟩ := conditionIH env target (.val values) middle testRun notType states
      dsimp only at run
      split at run
      · simp at run
        exact False.elim (noType run.1.symm)
      · rename_i test
        obtain ⟨targetNext, targetBranch, nextRel⟩ := yesIH middle middleClock env targetMiddle result next run noType related
        refine ⟨targetNext, ?_, nextRel⟩
        rw [evaluate, fixClock_evaluate, targetRun]
        simpa [test] using targetBranch
      · rename_i test
        obtain ⟨targetNext, targetBranch, nextRel⟩ := noIH middle middleClock env targetMiddle result next run noType related
        refine ⟨targetNext, ?_, nextRel⟩
        rw [evaluate, fixClock_evaluate, targetRun]
        simpa [test] using targetBranch

/-- Recursive closure construction preserves the extension before evaluating
the enclosing body. -/
theorem evaluate_letrec_codeExtension {C F : Type} (names : List Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat)) (functions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (source : State C F) (bodyIH : EvalCodeExtensionAt source [body]) :
    EvalCodeExtensionAt source [.letrec names location selected functions body] := by
  intro env target result next run noType states
  have maxEq : target.maxApp = source.maxApp := by rw [states.1]
  rw [evaluate.eq_def] at run ⊢
  dsimp only at run ⊢
  simp only [maxEq]
  by_cases valid : functions.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true
  · cases selected with
    | none =>
      simp only [valid, ↓reduceIte] at run ⊢
      exact bodyIH _ target result next run noType states
    | some capturedNames =>
      cases captured : lookupVars capturedNames env with
      | none =>
        simp [valid, captured] at run
        exact False.elim (noType run.1.symm)
      | some values =>
        simp only [valid, ↓reduceIte, captured] at run ⊢
        exact bodyIH _ target result next run noType states
  · simp [valid] at run
    exact False.elim (noType run.1.symm)

/-- Direct calls follow the same existing code entry under extension. -/
theorem evaluate_call_codeExtension {C F : Type} (trace : BackendCommon.Tra) (ticks location : Nat)
    (args : List ClosLang.Exp) (source : State C F) (argsIH : EvalCodeExtensionAt source args)
    (bodyIH : ∀ body (state : State C F), state.clock < source.clock → EvalCodeExtensionAt state [body]) :
    EvalCodeExtensionAt source [.call trace ticks location args] := by
  intro env target result next run noType states
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    have middleClock : middle.clock ≤ source.clock := by
      have h := evaluate_clock_le args env source
      simpa [argsRun] using h
    rw [argsRun] at run
    cases argsResult with
    | err error =>
      cases run
      obtain ⟨targetMiddle, targetRun, middleRel⟩ := argsIH env target (.err error) middle argsRun noType states
      exact ⟨targetMiddle, by rw [evaluate, fixClock_evaluate, targetRun], middleRel⟩
    | val values =>
      have argsNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetMiddle, targetRun, middleRel⟩ := argsIH env target (.val values) middle argsRun argsNoType states
      dsimp only at run
      cases found : findCode location values middle.code with
      | none =>
        rw [found] at run
        cases run
        exact False.elim (noType rfl)
      | some entry =>
        obtain ⟨bodyEnv, body⟩ := entry
        have targetFound := findCode_of_codeSubmap middle.code targetMiddle.code location values (bodyEnv, body)
          middleRel.2.1 found
        have clockEq : targetMiddle.clock = middle.clock := by rw [middleRel.1]
        rw [found] at run
        dsimp only at run
        by_cases timeout : middle.clock < ticks + 1
        · rw [if_pos timeout] at run
          cases run
          refine ⟨{ targetMiddle with clock := 0 }, ?_, codeExtension_withClock middle targetMiddle 0 middleRel⟩
          rw [evaluate, fixClock_evaluate, targetRun]
          dsimp only
          rw [targetFound]
          dsimp only
          simp [clockEq, timeout]
        · rw [if_neg timeout] at run
          have smaller : (decClock (ticks + 1) middle).clock < source.clock := by simp [decClock]; omega
          obtain ⟨targetNext, targetBody, nextRel⟩ :=
            bodyIH body (decClock (ticks + 1) middle) smaller bodyEnv (decClock (ticks + 1) targetMiddle)
              result next run noType (codeExtension_decClock middle targetMiddle (ticks + 1) middleRel)
          refine ⟨targetNext, ?_, nextRel⟩
          rw [evaluate, fixClock_evaluate, targetRun]
          dsimp only
          rw [targetFound]
          dsimp only
          simpa [clockEq, timeout] using targetBody

/-- Application simulations at clocks below a bound. -/
def AppCodeExtensionBelow {C F : Type} (clock : Nat) : Prop :=
  ∀ (location : Option Nat) (function : Value) (args : List Value) (source target : State C F)
    (result : Result (List Value) Value) (next : State C F),
    source.clock < clock → evaluateApp location function args source = (result, next) →
    result ≠ .err (.abort .typeError) → CodeExtension source target →
    ∃ targetNext, evaluateApp location function args target = (result, targetNext) ∧ CodeExtension next targetNext

/-- Closure application is unchanged by a safe code extension when its body
and recursive application cases hold at smaller clocks. -/
theorem evaluateApp_codeExtension {C F : Type} (location : Option Nat) (function : Value)
    (args : List Value) (source target : State C F) (result : Result (List Value) Value) (next : State C F)
    (run : evaluateApp location function args source = (result, next))
    (noType : result ≠ .err (.abort .typeError)) (states : CodeExtension source target)
    (bodyIH : ∀ (body : ClosLang.Exp) (state : State C F), state.clock < source.clock → EvalCodeExtensionAt state [body])
    (appIH : AppCodeExtensionBelow (C := C) (F := F) source.clock) :
    ∃ targetNext, evaluateApp location function args target = (result, targetNext) ∧ CodeExtension next targetNext := by
  have clockEq : target.clock = source.clock := by rw [states.1]
  have maxEq : target.maxApp = source.maxApp := by rw [states.1]
  cases args with
  | nil =>
    simp [evaluateApp] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨target, by simp [evaluateApp], states⟩
  | cons first rest =>
    rw [evaluateApp] at run
    cases found : destClosure source.maxApp location function (first :: rest) with
    | none =>
      rw [found] at run
      cases run
      exact False.elim (noType rfl)
    | some kind =>
      rw [found] at run
      have targetFound : destClosure target.maxApp location function (first :: rest) = some kind := by
        simpa [maxEq] using found
      cases kind with
      | partialApp value =>
        dsimp only at run
        by_cases timeout : source.clock < (first :: rest).length
        · rw [if_pos timeout] at run
          cases run
          refine ⟨{ target with clock := 0 }, ?_, codeExtension_withClock source target 0 states⟩
          rw [evaluateApp, targetFound]
          dsimp only
          rw [if_pos (by simpa [clockEq] using timeout)]
          rfl
        · rw [if_neg timeout] at run
          cases run
          refine ⟨decClock (first :: rest).length target, ?_, codeExtension_decClock source target _ states⟩
          rw [evaluateApp, targetFound]
          dsimp only
          rw [if_neg (by simpa [clockEq] using timeout)]
      | fullApp body env remaining =>
        dsimp only at run
        let cost := (first :: rest).length - remaining.length
        have positive : 0 < cost := Nat.sub_pos_of_lt (destClosure_full_remaining_lt _ _ _ _ _ _ _ found)
        by_cases timeout : source.clock < cost
        · rw [if_pos timeout] at run
          cases run
          refine ⟨{ target with clock := 0 }, ?_, codeExtension_withClock source target 0 states⟩
          rw [evaluateApp, targetFound]
          dsimp only
          rw [if_pos (by simpa [clockEq, cost] using timeout)]
          rfl
        · rw [if_neg timeout, fixClock_evaluate] at run
          have smaller : (decClock cost source).clock < source.clock := by simp [decClock]; omega
          cases bodyRun : evaluate [body] env (decClock cost source) with
          | mk bodyResult middle =>
            have bodyNoType : bodyResult ≠ .err (.abort .typeError) := by
              intro bad
              subst bodyResult
              rw [bodyRun] at run
              cases run
              exact noType rfl
            obtain ⟨targetMiddle, targetBody, middleRel⟩ :=
              bodyIH body (decClock cost source) smaller env (decClock cost target) bodyResult middle
                bodyRun bodyNoType (codeExtension_decClock source target cost states)
            rw [bodyRun] at run
            cases bodyResult with
            | err error =>
              cases run
              refine ⟨targetMiddle, ?_, middleRel⟩
              rw [evaluateApp, targetFound]
              dsimp only
              rw [if_neg (by simpa [clockEq, cost] using timeout), fixClock_evaluate, targetBody]
            | val values =>
              have size := (evaluate_length (C := C) (F := F)).1 [body] env (decClock cost source) middle values bodyRun
              cases values with
              | nil => simp at size
              | cons value tail =>
                cases tail with
                | cons other tail => simp at size
                | nil =>
                  have middleClock : middle.clock < source.clock := by
                    have h := evaluate_clock_le [body] env (decClock cost source)
                    rw [bodyRun] at h
                    exact Nat.lt_of_le_of_lt h smaller
                  obtain ⟨targetNext, targetApp, nextRel⟩ :=
                    appIH location value remaining middle targetMiddle result next middleClock run noType middleRel
                  refine ⟨targetNext, ?_, nextRel⟩
                  rw [evaluateApp, targetFound]
                  dsimp only
                  rw [if_neg (by simpa [clockEq, cost] using timeout), fixClock_evaluate, targetBody]
                  exact targetApp

/-- Application expressions evaluate their arguments and function identically
under a safe code extension. -/
theorem evaluate_app_codeExtension {C F : Type} (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (source : State C F)
    (argsIH : EvalCodeExtensionAt source args)
    (functionIH : ∀ state : State C F, state.clock ≤ source.clock → EvalCodeExtensionAt state [function])
    (appIH : AppCodeExtensionBelow (C := C) (F := F) (source.clock + 1)) :
    EvalCodeExtensionAt source [.app trace location function args] := by
  intro env target result next run noType states
  cases args with
  | nil =>
    simp [evaluate] at run
    exact False.elim (noType run.1.symm)
  | cons first rest =>
    rw [evaluate, fixClock_evaluate] at run
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run
    cases argsRun : evaluate (first :: rest) env source with
    | mk argsResult middle =>
      have middleClock : middle.clock ≤ source.clock := by
        have h := evaluate_clock_le (first :: rest) env source
        simpa [argsRun] using h
      rw [argsRun] at run
      cases argsResult with
      | err error =>
        cases run
        obtain ⟨targetMiddle, targetRun, middleRel⟩ := argsIH env target (.err error) middle argsRun noType states
        refine ⟨targetMiddle, ?_, middleRel⟩
        rw [evaluate, fixClock_evaluate, targetRun]
        rfl
      | val values =>
        have argsNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
        obtain ⟨targetMiddle, targetRun, middleRel⟩ := argsIH env target (.val values) middle argsRun argsNoType states
        rw [fixClock_evaluate] at run
        cases functionRun : evaluate [function] env middle with
        | mk functionResult last =>
          rw [functionRun] at run
          cases functionResult with
          | err error =>
            cases run
            obtain ⟨targetLast, targetFunction, lastRel⟩ :=
              functionIH middle middleClock env targetMiddle (.err error) last functionRun noType middleRel
            refine ⟨targetLast, ?_, lastRel⟩
            rw [evaluate, fixClock_evaluate, targetRun]
            simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
            rw [fixClock_evaluate, targetFunction]
          | val functions =>
            have functionNoType : (Result.val functions : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
            obtain ⟨targetLast, targetFunction, lastRel⟩ :=
              functionIH middle middleClock env targetMiddle (.val functions) last functionRun functionNoType middleRel
            have lastClock : last.clock ≤ source.clock := by
              have h := evaluate_clock_le [function] env middle
              rw [functionRun] at h
              simp only at h
              omega
            obtain ⟨targetNext, targetApp, nextRel⟩ :=
              appIH location _ values last targetLast result next (by omega) run noType lastRel
            refine ⟨targetNext, ?_, nextRel⟩
            rw [evaluate, fixClock_evaluate, targetRun]
            simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
            rw [fixClock_evaluate, targetFunction]
            exact targetApp

/-- Installation and the installed program preserve safe code extensions. -/
theorem evaluate_install_codeExtension {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (source : State C F) (argsIH : EvalCodeExtensionAt source args)
    (programIH : ∀ program (state : State C F), state.clock < source.clock → EvalCodeExtensionAt state program) :
    EvalCodeExtensionAt source [.op trace .install args] := by
  intro env target result next run noType states
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    have middleClock : middle.clock ≤ source.clock := by
      have h := evaluate_clock_le args env source
      simpa [argsRun] using h
    rw [argsRun] at run
    cases argsResult with
    | err error =>
      cases run
      obtain ⟨targetMiddle, targetRun, middleRel⟩ := argsIH env target (.err error) middle argsRun noType states
      refine ⟨targetMiddle, ?_, middleRel⟩
      rw [evaluate, fixClock_evaluate, targetRun]
    | val values =>
      have argsNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetMiddle, targetRun, middleRel⟩ := argsIH env target (.val values) middle argsRun argsNoType states
      dsimp only at run
      cases installRun : doInstall values.reverse middle with
      | mk installResult installed =>
        rw [installRun] at run
        cases installResult with
        | err error =>
          cases run
          obtain ⟨targetInstalled, targetInstall, installedRel⟩ :=
            doInstall_codeExtension values.reverse middle targetMiddle next (.err error) installRun (by intro h; cases h; exact noType rfl) middleRel
          refine ⟨targetInstalled, ?_, installedRel⟩
          rw [evaluate, fixClock_evaluate, targetRun]
          dsimp only
          rw [targetInstall]
        | val program =>
          have installNoType : (Result.val program : Result (List ClosLang.Exp) Value) ≠ .err (.abort .typeError) := by simp
          obtain ⟨targetInstalled, targetInstall, installedRel⟩ :=
            doInstall_codeExtension values.reverse middle targetMiddle installed (.val program) installRun installNoType middleRel
          dsimp only at run
          cases programRun : evaluate program [] installed with
          | mk programResult final =>
            have installedClock := doInstall_success_clock values.reverse middle installed program installRun
            have smaller : installed.clock < source.clock := by omega
            rw [programRun] at run
            cases programResult with
            | err error =>
              cases run
              obtain ⟨targetFinal, targetProgram, finalRel⟩ :=
                programIH program installed smaller [] targetInstalled (.err error) final programRun noType installedRel
              refine ⟨targetFinal, ?_, finalRel⟩
              rw [evaluate, fixClock_evaluate, targetRun]
              dsimp only
              rw [targetInstall]
              dsimp only
              rw [targetProgram]
            | val programValues =>
              have programNoType : (Result.val programValues : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
              obtain ⟨targetFinal, targetProgram, finalRel⟩ :=
                programIH program installed smaller [] targetInstalled (.val programValues) final programRun programNoType installedRel
              cases run
              refine ⟨targetFinal, ?_, finalRel⟩
              rw [evaluate, fixClock_evaluate, targetRun]
              dsimp only
              rw [targetInstall]
              dsimp only
              rw [targetProgram]

/-- Forcing a thunk preserves its result and the safe code extension. -/
theorem evaluate_force_codeExtension {C F : Type} (trace : BackendCommon.Tra) (args : List ClosLang.Exp)
    (source : State C F) (argsIH : EvalCodeExtensionAt source args)
    (forceIH : ∀ state : State C F, state.clock ≤ source.clock →
      EvalCodeExtensionAt state [appUnit (.var .none 0)]) :
    EvalCodeExtensionAt source [.op trace (.thunkOp .forceThunk) args] := by
  intro env target result next run noType states
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    have middleClock : middle.clock ≤ source.clock := by
      have h := evaluate_clock_le args env source
      simpa [argsRun] using h
    rw [argsRun] at run
    cases argsResult with
    | err error =>
      cases run
      obtain ⟨targetMiddle, targetRun, middleRel⟩ := argsIH env target (.err error) middle argsRun noType states
      refine ⟨targetMiddle, ?_, middleRel⟩
      rw [evaluate, fixClock_evaluate, targetRun]
    | val values =>
      have argsNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetMiddle, targetRun, middleRel⟩ := argsIH env target (.val values) middle argsRun argsNoType states
      have refsEq : targetMiddle.refs = middle.refs := by rw [middleRel.1]
      dsimp only at run
      cases dest : destThunk values middle.refs with
      | badRef | notThunk =>
        simp [dest] at run
        exact False.elim (noType run.1.symm)
      | isThunk mode value =>
        have targetDest : destThunk values targetMiddle.refs = .isThunk mode value := by simpa [refsEq] using dest
        cases mode with
        | evaluated =>
          rw [dest] at run
          cases run
          refine ⟨targetMiddle, ?_, middleRel⟩
          rw [evaluate, fixClock_evaluate, targetRun]
          dsimp only
          rw [targetDest]
        | notEvaluated =>
          rw [dest] at run
          dsimp only at run
          cases forceRun : evaluate [appUnit (.var .none 0)] [value] middle with
          | mk forceResult last =>
            rw [forceRun] at run
            cases forceResult with
            | err error =>
              cases run
              obtain ⟨targetLast, targetForce, lastRel⟩ :=
                forceIH middle middleClock [value] targetMiddle (.err error) last forceRun noType middleRel
              refine ⟨targetLast, ?_, lastRel⟩
              rw [evaluate, fixClock_evaluate, targetRun]
              dsimp only
              rw [targetDest]
              dsimp only
              rw [targetForce]
            | val forced =>
              have forceNoType : (Result.val forced : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
              obtain ⟨targetLast, targetForce, lastRel⟩ :=
                forceIH middle middleClock [value] targetMiddle (.val forced) last forceRun forceNoType middleRel
              have lastRefs : targetLast.refs = last.refs := by rw [lastRel.1]
              dsimp only at run
              cases update : updateThunk values last.refs forced with
              | none =>
                simp [update] at run
                exact False.elim (noType run.1.symm)
              | some refs =>
                rw [update] at run
                cases run
                refine ⟨{ targetLast with refs := refs }, ?_, codeExtension_withRefs last targetLast refs lastRel⟩
                rw [evaluate, fixClock_evaluate, targetRun]
                dsimp only
                rw [targetDest]
                dsimp only
                rw [targetForce]
                dsimp only
                rw [lastRefs, update]

end Flapjack.Compiler.Backend.ClosSem
