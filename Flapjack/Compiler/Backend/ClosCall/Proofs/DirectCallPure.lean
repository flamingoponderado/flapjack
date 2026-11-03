import Flapjack.Compiler.Backend.ClosCall.Proofs.DirectCallImpure
import Flapjack.Compiler.Backend.ClosCall.Proofs.Purity

/-! Evaluation of direct-call rewrites that eliminate a pure function expression. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- For successful argument evaluation, a generated direct call and an
application of the corresponding known closure agree, including timeouts.
This is a target-side evaluator fact, not a full pass-correctness theorem. -/
theorem evaluate_pure_rewrite_eq_known_app {C F : Type}
    (trace stubTrace : BackendCommon.Tra) (label address : Nat)
    (args : List ClosLang.Exp) (env values : List ClosSem.Value)
    (functionValue : ClosSem.Value) (state afterArgs : ClosSem.State C F)
    (stubEnv : List ClosSem.Value) (body : ClosLang.Exp)
    (argsRun : evaluate args env state = (.val values, afterArgs))
    (code : afterArgs.code.lookup label = some (values.length, body))
    (closure : destClosure afterArgs.maxApp (some address) functionValue values =
      some (.fullApp (.call stubTrace 0 label (ClosCall.variables stubTrace values.length)) stubEnv [])) :
    evaluate [.call trace args.length label args] env state =
      evaluateApp (some address) functionValue values afterArgs := by
  have lengths := (evaluate_length (C := C) (F := F)).1 args env state afterArgs values argsRun
  have varsRun : evaluate (ClosCall.variables .none values.length) (values ++ env) afterArgs =
      (.val values, afterArgs) := by
    have bound : values.length ≤ (values ++ env).length := by simp
    simpa using evaluate_variables .none values.length (values ++ env) afterArgs bound
  have callEq : evaluate [.call trace args.length label args] env state =
      evaluate [.call trace values.length label (ClosCall.variables .none values.length)]
        (values ++ env) afterArgs := by
    rw [evaluate, fixClock_evaluate, argsRun, evaluate, fixClock_evaluate, varsRun]
    simp [lengths]
  rw [callEq]
  cases clockEq : afterArgs.clock with
  | zero =>
    have nonempty : values ≠ [] := by
      intro empty
      have smaller := destClosure_full_remaining_lt afterArgs.maxApp (some address) functionValue values stubEnv [] _ closure
      simp [empty] at smaller
    rw [evaluate, fixClock_evaluate, varsRun]
    cases values with
    | nil => contradiction
    | cons first rest =>
      rw [evaluateApp, closure]
      simp [findCode, code, clockEq]
  | succ clock =>
    let previous := { afterArgs with clock := clock }
    have bound : values.length ≤ (values ++ env).length := by simp
    have previousVars : evaluate (ClosCall.variables .none values.length) (values ++ env)
        previous = (.val values, previous) := by
      simpa using evaluate_variables .none values.length (values ++ env) previous bound
    have code' : previous.code.lookup label = some (values.length, body) := by simpa [previous] using code
    have closure' : destClosure previous.maxApp (some address) functionValue values =
        some (.fullApp (.call stubTrace 0 label (ClosCall.variables stubTrace values.length)) stubEnv []) := by
      simpa [previous] using closure
    have eq := evaluate_rewritten_call_eq_known_app_all trace stubTrace label address
      (ClosCall.variables .none values.length) (values ++ env) values stubEnv functionValue
      previous previous body previousVars code' closure'
    have restore : { previous with clock := previous.clock + 1 } = afterArgs := by
      cases afterArgs
      simp_all [previous]
    simpa only [restore] using eq

/-- A successful traversal emits a direct call for a pure function at a known
location, and the discarded transformed function remains pure. This is a
Lean-side executable traversal case, not the complete pass simulation. -/
theorem callsFuel_app_pure_shape (fuel : Nat) (trace : BackendCommon.Tra) (address : Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.app trace (some address) function args) initial = some (out, final))
    (known : (sptLookup address final.1).isSome = true) (pure : ClosLang.pure function = true) :
    ∃ targetArgs targetFunction middle,
      callsListFuel fuel args initial = some (targetArgs, middle) ∧
      callsFuel fuel function middle = some (targetFunction, final) ∧
      ClosLang.pure targetFunction = true ∧
      out = .call trace targetArgs.length (address + 1) targetArgs := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
  obtain ⟨⟨targetArgs, middle⟩, argsRun, ⟨targetFunction, afterFn⟩, fnRun, rest⟩ := run
  by_cases found : (sptLookup address afterFn.1).isSome
  · simp [found, pure] at rest
    obtain ⟨rfl, rfl⟩ := rest
    exact ⟨targetArgs, targetFunction, middle, argsRun, fnRun,
      (callsFuel_purity fuel).1 function middle targetFunction afterFn pure fnRun, rfl⟩
  · simp [found] at rest
    obtain ⟨_, rfl⟩ := rest
    simp [found] at known

/-- The generated pure direct call propagates an argument error. -/
theorem callsFuel_app_pure_args_error {C F : Type} (fuel : Nat) (trace : BackendCommon.Tra)
    (address : Nat) (function : ClosLang.Exp) (args : List ClosLang.Exp) (initial final : State)
    (out : ClosLang.Exp) (env : List ClosSem.Value) (state after : ClosSem.State C F)
    (error : ErrorResult ClosSem.Value)
    (run : callsFuel (fuel + 1) (.app trace (some address) function args) initial = some (out, final))
    (known : (sptLookup address final.1).isSome = true) (pure : ClosLang.pure function = true)
    (argsRun : ∀ targetArgs middle, callsListFuel fuel args initial = some (targetArgs, middle) →
      evaluate targetArgs env state = (.err error, after)) :
    evaluate [out] env state = (.err error, after) := by
  obtain ⟨targetArgs, _, middle, argsTraversal, _, _, rfl⟩ :=
    callsFuel_app_pure_shape fuel trace address function args initial final out run known pure
  rw [evaluate, fixClock_evaluate, argsRun targetArgs middle argsTraversal]

/-- When the transformed arguments evaluate successfully and the related
function is the generated closure, the actual traversal output agrees with
the corresponding application. This local case does not establish that the
related closure exists; that remains part of the source simulation. -/
theorem callsFuel_app_pure_eq_known_app {C F : Type} (fuel : Nat) (trace stubTrace : BackendCommon.Tra)
    (address : Nat) (function : ClosLang.Exp) (args : List ClosLang.Exp) (initial final : State)
    (out : ClosLang.Exp) (env values : List ClosSem.Value) (functionValue : ClosSem.Value)
    (state afterArgs : ClosSem.State C F) (stubEnv : List ClosSem.Value) (body : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.app trace (some address) function args) initial = some (out, final))
    (known : (sptLookup address final.1).isSome = true) (pure : ClosLang.pure function = true)
    (argsRun : ∀ targetArgs middle, callsListFuel fuel args initial = some (targetArgs, middle) →
      evaluate targetArgs env state = (.val values, afterArgs))
    (code : afterArgs.code.lookup (address + 1) = some (values.length, body))
    (closure : destClosure afterArgs.maxApp (some address) functionValue values =
      some (.fullApp (.call stubTrace 0 (address + 1) (ClosCall.variables stubTrace values.length)) stubEnv [])) :
    evaluate [out] env state = evaluateApp (some address) functionValue values afterArgs := by
  obtain ⟨targetArgs, _, middle, argsTraversal, _, _, rfl⟩ :=
    callsFuel_app_pure_shape fuel trace address function args initial final out run known pure
  exact evaluate_pure_rewrite_eq_known_app trace stubTrace (address + 1) address targetArgs env values
    functionValue state afterArgs stubEnv body (argsRun targetArgs middle argsTraversal) code closure

end Flapjack.Compiler.Backend.ClosCall
