import Flapjack.Compiler.Backend.ClosInterp.Proofs.NoInstallEvaluate

/-! No-install preservation steps for closure evaluator control flow. The
evaluator and its carriers await HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- Sequencing preserves the invariant when evaluating its head and tail does. -/
theorem evaluate_cons_noInstall_step {C F : Type} (head : ClosLang.Exp) (tail : List ClosLang.Exp)
    (env : List ClosSem.Value) (state next : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (headIH : ∀ (last : ClosSem.State C F) (headResult : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [head] env state = (headResult, last) → resultNoInstall headResult ∧ evalStateNoInstall last)
    (tailIH : ∀ (start final : ClosSem.State C F) (tailResult : Result (List ClosSem.Value) ClosSem.Value),
      start.clock ≤ state.clock → evalStateNoInstall start → ClosSem.evaluate tail env start = (tailResult, final) →
      resultNoInstall tailResult ∧ evalStateNoInstall final)
    (run : ClosSem.evaluate (head :: tail) env state = (result, next)) :
    resultNoInstall result ∧ evalStateNoInstall next := by
  cases headRun : ClosSem.evaluate [head] env state with
  | mk headResult last =>
    obtain ⟨headOk, lastOk⟩ := headIH last headResult headRun
    cases headResult with
    | err error =>
      rw [ClosProps.evaluate_cons_error head tail env state last error headRun] at run
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨headOk, lastOk⟩
    | val values =>
      obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value head env state last values headRun
      have valueOk : valueNoInstall value = true := by simpa [resultNoInstall, valuesNoInstall] using headOk
      have bound : last.clock ≤ state.clock := by
        have clock := ClosSem.evaluate_clock_le [head] env state
        simpa [headRun] using clock
      rw [ClosProps.evaluate_cons_value head tail env state last value headRun] at run
      cases tailRun : ClosSem.evaluate tail env last with
      | mk tailResult final =>
        rw [tailRun] at run
        obtain ⟨tailOk, finalOk⟩ := tailIH last final tailResult bound lastOk tailRun
        cases tailResult with
        | err error =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨tailOk, finalOk⟩
        | val tailValues =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨by simpa [resultNoInstall, valuesNoInstall, valueOk] using tailOk, finalOk⟩

/-- Raising a safe result preserves the invariant on language exceptions. -/
theorem evaluate_raise_noInstall_step {C F : Type} (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (env : List ClosSem.Value) (state next : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyIH : ∀ (last : ClosSem.State C F) (bodyResult : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [body] env state = (bodyResult, last) → resultNoInstall bodyResult ∧ evalStateNoInstall last)
    (run : ClosSem.evaluate [.raise trace body] env state = (result, next)) :
    resultNoInstall result ∧ evalStateNoInstall next := by
  cases bodyRun : ClosSem.evaluate [body] env state with
  | mk bodyResult last =>
    rw [ClosSem.evaluate, bodyRun] at run
    obtain ⟨bodyOk, lastOk⟩ := bodyIH last bodyResult bodyRun
    cases bodyResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨bodyOk, lastOk⟩
    | val values =>
      obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value body env state last values bodyRun
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨by simpa [resultNoInstall, valuesNoInstall] using bodyOk, lastOk⟩

/-- A let binding preserves the invariant when its bindings and body do. -/
theorem evaluate_let_noInstall_step {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (env : List ClosSem.Value)
    (state next : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (envOk : valuesNoInstall env = true)
    (bindingsIH : ∀ (last : ClosSem.State C F) (bindingResult : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate bindings env state = (bindingResult, last) → resultNoInstall bindingResult ∧ evalStateNoInstall last)
    (bodyIH : ∀ (bodyEnv : List ClosSem.Value) (start final : ClosSem.State C F)
      (bodyResult : Result (List ClosSem.Value) ClosSem.Value), start.clock ≤ state.clock →
      valuesNoInstall bodyEnv = true → evalStateNoInstall start →
      ClosSem.evaluate [body] bodyEnv start = (bodyResult, final) → resultNoInstall bodyResult ∧ evalStateNoInstall final)
    (run : ClosSem.evaluate [.let trace bindings body] env state = (result, next)) :
    resultNoInstall result ∧ evalStateNoInstall next := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
  cases bindingRun : ClosSem.evaluate bindings env state with
  | mk bindingResult last =>
    have bound : last.clock ≤ state.clock := by
      have clock := ClosSem.evaluate_clock_le bindings env state
      simpa [bindingRun] using clock
    rw [bindingRun] at run
    obtain ⟨bindingOk, lastOk⟩ := bindingsIH last bindingResult bindingRun
    cases bindingResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨bindingOk, lastOk⟩
    | val values =>
      dsimp only at run
      have bodyEnvOk := (valuesNoInstall_append values env).2 ⟨bindingOk, envOk⟩
      exact bodyIH (values ++ env) last next result bound bodyEnvOk lastOk run

/-- An exception handler preserves the invariant when its body and handler do. -/
theorem evaluate_handle_noInstall_step {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (env : List ClosSem.Value)
    (state next : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (envOk : valuesNoInstall env = true)
    (bodyIH : ∀ (last : ClosSem.State C F) (bodyResult : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [body] env state = (bodyResult, last) → resultNoInstall bodyResult ∧ evalStateNoInstall last)
    (handlerIH : ∀ (value : ClosSem.Value) (start final : ClosSem.State C F)
      (handlerResult : Result (List ClosSem.Value) ClosSem.Value), start.clock ≤ state.clock →
      valueNoInstall value = true → valuesNoInstall (value :: env) = true → evalStateNoInstall start →
      ClosSem.evaluate [handler] (value :: env) start = (handlerResult, final) →
      resultNoInstall handlerResult ∧ evalStateNoInstall final)
    (run : ClosSem.evaluate [.handle trace body handler] env state = (result, next)) :
    resultNoInstall result ∧ evalStateNoInstall next := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
  cases bodyRun : ClosSem.evaluate [body] env state with
  | mk bodyResult last =>
    have bound : last.clock ≤ state.clock := by
      have clock := ClosSem.evaluate_clock_le [body] env state
      simpa [bodyRun] using clock
    rw [bodyRun] at run
    obtain ⟨bodyOk, lastOk⟩ := bodyIH last bodyResult bodyRun
    cases bodyResult with
    | val values =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨bodyOk, lastOk⟩
    | err error =>
      cases error with
      | abort reason =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨bodyOk, lastOk⟩
      | raise value =>
        dsimp only at run
        have valueOk : valueNoInstall value = true := bodyOk
        have handlerEnvOk : valuesNoInstall (value :: env) = true := by simp [valuesNoInstall, valueOk, envOk]
        exact handlerIH value last next result bound valueOk handlerEnvOk lastOk run

/-- A conditional preserves the invariant when its test and selected branch do. -/
theorem evaluate_if_noInstall_step {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (env : List ClosSem.Value)
    (state next : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (conditionIH : ∀ (last : ClosSem.State C F) (testResult : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [condition] env state = (testResult, last) → resultNoInstall testResult ∧ evalStateNoInstall last)
    (branchIH : ∀ (choice : Bool) (start final : ClosSem.State C F)
      (branchResult : Result (List ClosSem.Value) ClosSem.Value), start.clock ≤ state.clock → evalStateNoInstall start →
      ClosSem.evaluate [if choice then yes else no] env start = (branchResult, final) →
      resultNoInstall branchResult ∧ evalStateNoInstall final)
    (run : ClosSem.evaluate [.ifThenElse trace condition yes no] env state = (result, next)) :
    resultNoInstall result ∧ evalStateNoInstall next := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
  cases conditionRun : ClosSem.evaluate [condition] env state with
  | mk testResult last =>
    have bound : last.clock ≤ state.clock := by
      have clock := ClosSem.evaluate_clock_le [condition] env state
      simpa [conditionRun] using clock
    rw [conditionRun] at run
    obtain ⟨testOk, lastOk⟩ := conditionIH last testResult conditionRun
    cases testResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨testOk, lastOk⟩
    | val values =>
      obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value condition env state last values conditionRun
      dsimp only at run
      cases boolRun : ClosSem.asBool value with
      | none =>
        simp [boolRun] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨trivial, lastOk⟩
      | some choice =>
        cases choice <;> simp [boolRun] at run
        · exact branchIH false last next result bound lastOk run
        · exact branchIH true last next result bound lastOk run

/-- Variable evaluation preserves a safe environment and state. -/
theorem evaluate_var_noInstall {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (env : List ClosSem.Value) (state next : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (envOk : valuesNoInstall env = true) (stateOk : evalStateNoInstall state)
    (run : ClosSem.evaluate [.var trace index] env state = (result, next)) :
    resultNoInstall result ∧ evalStateNoInstall next := by
  rw [ClosSem.evaluate] at run
  cases found : env[index]? with
  | none =>
    simp [found] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨trivial, stateOk⟩
  | some value =>
    simp [found] at run
    rcases run with ⟨rfl, rfl⟩
    have valueOk := valuesNoInstall_lookup env index value envOk found
    exact ⟨by simp [resultNoInstall, valuesNoInstall, valueOk], stateOk⟩

/-- Ticking either times out or evaluates the body at a smaller clock. -/
theorem evaluate_tick_noInstall_step {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (env : List ClosSem.Value) (state next : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value) (stateOk : evalStateNoInstall state)
    (bodyIH : ∀ (start final : ClosSem.State C F) (bodyResult : Result (List ClosSem.Value) ClosSem.Value),
      start.clock < state.clock → evalStateNoInstall start →
      ClosSem.evaluate [body] env start = (bodyResult, final) → resultNoInstall bodyResult ∧ evalStateNoInstall final)
    (run : ClosSem.evaluate [.tick trace body] env state = (result, next)) :
    resultNoInstall result ∧ evalStateNoInstall next := by
  rw [ClosSem.evaluate] at run
  split at run
  · simp at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨trivial, stateOk⟩
  · have smaller : (ClosSem.decClock 1 state).clock < state.clock := by
      simp [ClosSem.decClock]; omega
    have startOk : evalStateNoInstall (ClosSem.decClock 1 state) := by
      simpa [evalStateNoInstall, ClosSem.decClock] using stateOk
    exact bodyIH _ next result smaller startOk run

/-- Constructing a closure from safe code and a safe environment is safe. -/
theorem evaluate_fn_noInstall {C F : Type} (name : Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp)
    (env : List ClosSem.Value) (state next : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value) (bodyOk : ClosLang.hasInstall body = false)
    (envOk : valuesNoInstall env = true) (stateOk : evalStateNoInstall state)
    (run : ClosSem.evaluate [.fn name location selected arity body] env state = (result, next)) :
    resultNoInstall result ∧ evalStateNoInstall next := by
  by_cases arityOk : arity ≤ state.maxApp ∧ arity ≠ 0
  · cases selected with
    | none =>
      simp [ClosSem.evaluate.eq_def, arityOk] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨by simp [resultNoInstall, valuesNoInstall, valueNoInstall, bodyOk, envOk], stateOk⟩
    | some names =>
      cases captured : ClosSem.lookupVars names env with
      | none =>
        simp [ClosSem.evaluate.eq_def, arityOk, captured] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨trivial, stateOk⟩
      | some values =>
        simp [ClosSem.evaluate.eq_def, arityOk, captured] at run
        rcases run with ⟨rfl, rfl⟩
        have capturedOk := lookupVars_noInstall names env values envOk captured
        exact ⟨by simp [resultNoInstall, valuesNoInstall, valueNoInstall, bodyOk, capturedOk], stateOk⟩
  · simp [ClosSem.evaluate.eq_def, arityOk] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨trivial, stateOk⟩

/-- A recursive binding constructs a safe closure bundle before evaluating
its body. -/
theorem evaluate_letrec_noInstall_step {C F : Type} (names : List Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat)) (functions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (env : List ClosSem.Value) (state next : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (functionsOk : ClosLang.hasInstallFuns functions = false)
    (envOk : valuesNoInstall env = true) (stateOk : evalStateNoInstall state)
    (bodyIH : ∀ (bodyEnv : List ClosSem.Value), valuesNoInstall bodyEnv = true →
      ClosSem.evaluate [body] bodyEnv state = (result, next) → resultNoInstall result ∧ evalStateNoInstall next)
    (run : ClosSem.evaluate [.letrec names location selected functions body] env state = (result, next)) :
    resultNoInstall result ∧ evalStateNoInstall next := by
  by_cases good : functions.all (fun (arity, _) => arity ≤ state.maxApp && arity != 0) = true
  · cases selected with
    | none =>
      rw [ClosSem.evaluate.eq_def] at run
      dsimp only at run
      rw [if_pos good] at run
      apply bodyIH _ ?_ run
      apply (valuesNoInstall_append _ _).2
      exact ⟨recursiveClosure_bundle_noInstall location env functions envOk functionsOk, envOk⟩
    | some selected =>
      cases captured : ClosSem.lookupVars selected env with
      | none =>
        rw [ClosSem.evaluate.eq_def] at run
        dsimp only at run
        rw [if_pos good, captured] at run
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨trivial, stateOk⟩
      | some values =>
        rw [ClosSem.evaluate.eq_def] at run
        dsimp only at run
        rw [if_pos good, captured] at run
        dsimp only at run
        have capturedOk := lookupVars_noInstall selected env values envOk captured
        apply bodyIH _ ?_ run
        apply (valuesNoInstall_append _ _).2
        exact ⟨recursiveClosure_bundle_noInstall location values functions capturedOk functionsOk, envOk⟩
  · rw [ClosSem.evaluate.eq_def] at run
    dsimp only at run
    rw [if_neg good] at run
    simp at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨trivial, stateOk⟩

/-- An application expression preserves the invariant when its arguments,
function, and closure application do. -/
theorem evaluate_app_noInstall_step {C F : Type} (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (state next : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (stateOk : evalStateNoInstall state)
    (argsIH : ∀ (last : ClosSem.State C F) (argResult : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate args env state = (argResult, last) → resultNoInstall argResult ∧ evalStateNoInstall last)
    (functionIH : ∀ (start final : ClosSem.State C F) (functionResult : Result (List ClosSem.Value) ClosSem.Value),
      start.clock ≤ state.clock → evalStateNoInstall start →
      ClosSem.evaluate [function] env start = (functionResult, final) →
      resultNoInstall functionResult ∧ evalStateNoInstall final)
    (appIH : ∀ (value : ClosSem.Value) (arguments : List ClosSem.Value) (start final : ClosSem.State C F)
      (appResult : Result (List ClosSem.Value) ClosSem.Value), start.clock ≤ state.clock →
      valueNoInstall value = true → valuesNoInstall arguments = true → evalStateNoInstall start →
      ClosSem.evaluateApp location value arguments start = (appResult, final) →
      resultNoInstall appResult ∧ evalStateNoInstall final)
    (run : ClosSem.evaluate [.app trace location function args] env state = (result, next)) :
    resultNoInstall result ∧ evalStateNoInstall next := by
  rw [ClosSem.evaluate] at run
  split at run
  · simp at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨trivial, stateOk⟩
  · rw [ClosSem.fixClock_evaluate] at run
    cases argsRun : ClosSem.evaluate args env state with
    | mk argResult last =>
      have bound : last.clock ≤ state.clock := by
        have clock := ClosSem.evaluate_clock_le args env state
        simpa [argsRun] using clock
      rw [argsRun] at run
      obtain ⟨argOk, lastOk⟩ := argsIH last argResult argsRun
      cases argResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨argOk, lastOk⟩
      | val arguments =>
        dsimp only at run
        rw [ClosSem.fixClock_evaluate] at run
        cases functionRun : ClosSem.evaluate [function] env last with
        | mk functionResult final =>
          have functionBound : final.clock ≤ last.clock := by
            have clock := ClosSem.evaluate_clock_le [function] env last
            simpa [functionRun] using clock
          rw [functionRun] at run
          obtain ⟨functionOk, finalOk⟩ := functionIH last final functionResult bound lastOk functionRun
          cases functionResult with
          | err error =>
            simp at run
            rcases run with ⟨rfl, rfl⟩
            exact ⟨functionOk, finalOk⟩
          | val values =>
            obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value function env last final values functionRun
            dsimp only at run
            have valueOk : valueNoInstall value = true := by
              simpa [resultNoInstall, valuesNoInstall] using functionOk
            exact appIH value arguments final next result (by omega) valueOk argOk finalOk run

end Flapjack.Compiler.Backend.ClosInterp
