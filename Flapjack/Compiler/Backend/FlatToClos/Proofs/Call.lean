import Flapjack.Compiler.Backend.FlatToClos.Proofs.Recursive
import Flapjack.Compiler.Backend.Semantics.FlatSem.Operations
import Flapjack.Compiler.Backend.Semantics.ClosSem.Call
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock
import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases

/-! Unary closure-call prerequisites for the flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.AstHOL Flapjack.Basis.Pure.MlString Flapjack.SemanticPrimitivesHOL

/-- A successful flat call of related function and argument values selects
the translated body and a related closure environment. This proof-side result
awaits correspondence review of the semantic carriers. -/
theorem doOpApp_related (function : FlatSem.Value) (targetFunction : ClosSem.Value)
    (argument : FlatSem.Value) (targetArgument : ClosSem.Value)
    (maxApp : Nat) (nextEnv : FlatSem.Environment FlatSem.Value) (body : FlatLang.Exp)
    (functionRel : ValueRel function targetFunction) (argumentRel : ValueRel argument targetArgument)
    (positive : 1 ≤ maxApp) (applied : FlatSem.doOpApp [function, argument] = some (nextEnv, body)) :
    ∃ names targetEnv,
      ClosSem.destClosure maxApp none targetFunction [targetArgument] =
        some (.fullApp (compileExp names body) targetEnv []) ∧
      EnvRel nextEnv names targetEnv ∧ FlatProps.noMat body = true := by
  cases functionRel with
  | closure environments safe =>
    simp [FlatSem.doOpApp] at applied
    rcases applied with ⟨rfl, rfl⟩
    refine ⟨_, _, ?_, envRel_cons environments argumentRel, safe⟩
    simp [ClosSem.destClosure, ClosSem.checkLoc, positive]
  | recclosure bound environments distinct safe =>
    rename_i env names values funs index
    have found := findRecFun_get _ _ bound distinct
    simp [FlatSem.doOpApp, distinct, found] at applied
    rcases applied with ⟨rfl, rfl⟩
    let compiled := compileFuns (funs.map (fun f => some f.1) ++ names) funs
    let recursive := (List.range compiled.length).map (fun i => ClosSem.Value.recclosure none [] values compiled i)
    refine ⟨some (funs[index]'bound).2.1 :: (funs.map (fun f => some f.1) ++ names),
      targetArgument :: (recursive ++ values), ?_, ?_, noMatFuns_get _ _ bound safe⟩
    · simp [ClosSem.destClosure, ClosSem.checkLoc, compileFuns_get _ _ _ bound, positive, recursive, compiled]
    · exact envRel_cons (envRel_rec _ _ _ _ environments distinct safe) argumentRel
  | loc | int | char | string | word8 | word64 | float64 | tuple | con | vector =>
    simp [FlatSem.doOpApp] at applied

/-- A full unary call consumes one clock unit and evaluates its body; zero
clock produces the ordinary timeout without changing the state. -/
theorem evaluateApp_unary {C F : Type} (function argument : ClosSem.Value)
    (state : ClosSem.State C F) (body : ClosLang.Exp) (env : List ClosSem.Value)
    (call : ClosSem.destClosure state.maxApp none function [argument] = some (.fullApp body env [])) :
    ClosSem.evaluateApp none function [argument] state =
      if state.clock = 0 then (.err (.abort .timeoutError), state)
      else ClosSem.evaluate [body] env (ClosSem.decClock 1 state) := by
  rw [ClosSem.evaluateApp]
  split <;> simp_all
  by_cases zero : state.clock = 0
  · simp [zero]
    cases state
    simp_all
  · simp only [↓reduceIte, zero]
    rw [ClosSem.fixClock_evaluate]
    cases run : ClosSem.evaluate [body] env (ClosSem.decClock 1 state) with
    | mk result next =>
      cases result with
      | err error => rfl
      | val values =>
        cases values with
        | nil => rfl
        | cons first rest =>
          cases rest with
          | nil => simp [ClosSem.evaluateApp]
          | cons second tail => rfl

/-- A successful unary flat call is simulated by the corresponding closure
call, given the induction hypothesis for its selected body. -/
theorem evaluate_call_related {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (function : FlatSem.Value) (targetFunction : ClosSem.Value)
    (argument : FlatSem.Value) (targetArgument : ClosSem.Value)
    (nextEnv : FlatSem.Environment FlatSem.Value) (body : FlatLang.Exp)
    (states : StateRel source target) (functionRel : ValueRel function targetFunction)
    (argumentRel : ValueRel argument targetArgument)
    (applied : FlatSem.doOpApp [function, argument] = some (nextEnv, body))
    (bodySim : ∀ (names : List (Option MlString)) (env : List ClosSem.Value),
      source.clock ≠ 0 → EnvRel nextEnv names env → FlatProps.noMat body = true →
      StateRel (FlatSem.decClock source) (ClosSem.decClock 1 target) →
      (FlatSem.evaluate nextEnv (FlatSem.decClock source) [body]).2 ≠ .err (.abort .typeError) →
      EvalSim nextEnv names env (FlatSem.decClock source) (ClosSem.decClock 1 target) [body])
    (notTypeError : (if source.clock = 0 then (source, .err (.abort .timeoutError)) else
      FlatSem.evaluate nextEnv (FlatSem.decClock source) [body]).2 ≠ .err (.abort .typeError)) :
    let sourceResult := if source.clock = 0 then (source, .err (.abort .timeoutError)) else
      FlatSem.evaluate nextEnv (FlatSem.decClock source) [body]
    let targetResult := ClosSem.evaluateApp none targetFunction [targetArgument] target
    StateRel sourceResult.1 targetResult.2 ∧ EvalResultRel sourceResult.2 targetResult.1 := by
  obtain ⟨names, env, call, envRel, safe⟩ :=
    doOpApp_related function targetFunction argument targetArgument target.maxApp nextEnv body
      functionRel argumentRel states.1 applied
  rw [evaluateApp_unary _ _ _ _ _ call]
  have clocks := states.2.2.1
  by_cases zero : source.clock = 0
  · have targetZero : target.clock = 0 := by omega
    simp [zero, targetZero, states, EvalResultRel.abort]
  · have targetNonzero : target.clock ≠ 0 := by omega
    simp only [zero, targetNonzero, ↓reduceIte] at notTypeError ⊢
    simpa [EvalSim, compile, compileExps] using
      bodySim names env zero envRel safe (stateRel_decClock states) notTypeError

end Flapjack.Compiler.Backend.FlatToClos
