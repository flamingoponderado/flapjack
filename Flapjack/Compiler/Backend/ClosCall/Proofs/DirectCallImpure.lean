import Flapjack.Compiler.Backend.ClosCall.Proofs.DirectCallClock

/-! Evaluation of direct-call rewrites that retain an impure function expression. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL

/-- A successful list evaluation followed by another successful evaluation
combines their values in order. This Lean-side structural helper has no
standalone HOL declaration. -/
theorem evaluate_append_success {C F : Type} (xs ys : List ClosLang.Exp) (env : List ClosSem.Value)
    (state middle final : ClosSem.State C F) (values tailValues : List ClosSem.Value)
    (firstRun : evaluate xs env state = (.val values, middle))
    (secondRun : evaluate ys env middle = (.val tailValues, final)) :
    evaluate (xs ++ ys) env state = (.val (values ++ tailValues), final) := by
  induction xs generalizing state middle values with
  | nil =>
    simp [evaluate] at firstRun
    obtain ⟨rfl, rfl⟩ := firstRun.symm
    simpa using secondRun
  | cons first rest ih =>
    cases h : evaluate [first] env state with
    | mk result afterFirst =>
      cases result with
      | err error =>
        have failed := ClosProps.evaluate_cons_error first rest env state afterFirst error h
        rw [firstRun] at failed
        cases congrArg Prod.fst failed
      | val firstValues =>
        obtain ⟨value, rfl⟩ := evaluate_singleton_value first env state afterFirst firstValues h
        have whole := ClosProps.evaluate_cons_value first rest env state afterFirst value h
        cases tail : evaluate rest env afterFirst with
        | mk tailResult afterTail =>
          cases tailResult with
          | err error =>
            simp [tail] at whole
            rw [firstRun] at whole
            cases congrArg Prod.fst whole
          | val restValues =>
            simp [tail] at whole
            rw [firstRun] at whole
            simp only [Prod.mk.injEq, Result.val.injEq] at whole
            obtain ⟨rfl, rfl⟩ := whole
            have combined := ih afterFirst middle restValues tail secondRun
            change evaluate (first :: (rest ++ ys)) env state = _
            rw [ClosProps.evaluate_cons_value first (rest ++ ys) env state afterFirst value h, combined]
            rfl

/-- On successful arguments and function evaluation, the let introduced for an
impure function executes the generated call with the same arguments, after the
function's effects. This local Lean-side evaluator fact has no standalone HOL
declaration and does not establish the pass simulation. -/
theorem evaluate_impure_rewritten_let {C F : Type} (trace : BackendCommon.Tra) (label : Nat)
    (args : List ClosLang.Exp) (function : ClosLang.Exp) (env values : List ClosSem.Value)
    (functionValue : ClosSem.Value) (state afterArgs afterFunction : ClosSem.State C F)
    (body : ClosLang.Exp)
    (argsRun : evaluate args env state = (.val values, afterArgs))
    (functionRun : evaluate [function] env afterArgs = (.val [functionValue], afterFunction))
    (code : afterFunction.code.lookup label = some (values.length, body)) :
    evaluate [.let (BackendCommon.mkCons trace 0) (args ++ [function])
      (.call (BackendCommon.mkCons trace 1) args.length label (ClosCall.variables .none args.length))] env state =
      if afterFunction.clock < values.length + 1 then
        (.err (.abort .timeoutError), { afterFunction with clock := 0 })
      else evaluate [body] values (decClock (values.length + 1) afterFunction) := by
  have lengths := (evaluate_length (C := C) (F := F)).1 args env state afterArgs values argsRun
  have bindings := evaluate_append_success args [function] env state afterArgs afterFunction values [functionValue]
    argsRun functionRun
  have variablesRun : evaluate (ClosCall.variables .none args.length) (values ++ [functionValue] ++ env) afterFunction =
      (.val values, afterFunction) := by
    have bound : args.length ≤ (values ++ [functionValue] ++ env).length := by simp [← lengths]
    have result := evaluate_variables .none args.length (values ++ [functionValue] ++ env) afterFunction bound
    simpa [← lengths] using result
  rw [evaluate, fixClock_evaluate, bindings]
  simp only
  rw [evaluate, fixClock_evaluate, variablesRun]
  simp [findCode, code, lengths]

/-- The successful impure rewrite agrees exactly with applying the evaluated
function when that function contains the generated direct-call stub. This
local target-side equality has no standalone HOL declaration and is not the
full source-to-target simulation. -/
theorem evaluate_impure_rewrite_eq_known_app {C F : Type}
    (trace stubTrace : BackendCommon.Tra) (label address : Nat)
    (args : List ClosLang.Exp) (function : ClosLang.Exp) (env values : List ClosSem.Value)
    (functionValue : ClosSem.Value) (state afterArgs afterFunction : ClosSem.State C F)
    (stubEnv : List ClosSem.Value) (body : ClosLang.Exp)
    (argsRun : evaluate args env state = (.val values, afterArgs))
    (functionRun : evaluate [function] env afterArgs = (.val [functionValue], afterFunction))
    (code : afterFunction.code.lookup label = some (values.length, body))
    (closure : destClosure afterFunction.maxApp (some address) functionValue values =
      some (.fullApp (.call stubTrace 0 label (ClosCall.variables stubTrace values.length)) stubEnv [])) :
    evaluate [.let (BackendCommon.mkCons trace 0) (args ++ [function])
      (.call (BackendCommon.mkCons trace 1) args.length label (ClosCall.variables .none args.length))] env state =
      evaluateApp (some address) functionValue values afterFunction := by
  have lengths := (evaluate_length (C := C) (F := F)).1 args env state afterArgs values argsRun
  have bindings := evaluate_append_success args [function] env state afterArgs afterFunction values [functionValue]
    argsRun functionRun
  have letEq : evaluate [.let (BackendCommon.mkCons trace 0) (args ++ [function])
      (.call (BackendCommon.mkCons trace 1) args.length label (ClosCall.variables .none args.length))] env state =
      evaluate [.call (BackendCommon.mkCons trace 1) values.length label (ClosCall.variables .none values.length)]
        (values ++ [functionValue] ++ env) afterFunction := by
    rw [evaluate, fixClock_evaluate, bindings]
    simp [lengths]
  rw [letEq]
  cases clockEq : afterFunction.clock with
  | zero =>
    have nonempty : values ≠ [] := by
      intro empty
      have smaller := destClosure_full_remaining_lt afterFunction.maxApp (some address) functionValue values stubEnv [] _ closure
      simp [empty] at smaller
    have varsRun : evaluate (ClosCall.variables .none values.length) (values ++ [functionValue] ++ env)
        afterFunction = (.val values, afterFunction) := by
      have bound : values.length ≤ (values ++ [functionValue] ++ env).length := by simp
      simpa using evaluate_variables .none values.length (values ++ [functionValue] ++ env) afterFunction bound
    rw [evaluate, fixClock_evaluate, varsRun]
    cases values with
    | nil => contradiction
    | cons first rest =>
      rw [evaluateApp, closure]
      simp [findCode, code, clockEq]
  | succ clock =>
    let previous := { afterFunction with clock := clock }
    have bound : values.length ≤ (values ++ [functionValue] ++ env).length := by simp
    have varsRun : evaluate (ClosCall.variables .none values.length) (values ++ [functionValue] ++ env)
        previous = (.val values, previous) := by
      simpa using evaluate_variables .none values.length (values ++ [functionValue] ++ env) previous bound
    have code' : previous.code.lookup label = some (values.length, body) := by simpa [previous] using code
    have closure' : destClosure previous.maxApp (some address) functionValue values =
        some (.fullApp (.call stubTrace 0 label (ClosCall.variables stubTrace values.length)) stubEnv []) := by
      simpa [previous] using closure
    have eq := evaluate_rewritten_call_eq_known_app_all (BackendCommon.mkCons trace 1) stubTrace label address
      (ClosCall.variables .none values.length) (values ++ [functionValue] ++ env) values stubEnv functionValue
      previous previous body varsRun code' closure'
    have restore : { previous with clock := previous.clock + 1 } = afterFunction := by
      cases afterFunction
      simp_all [previous]
    simpa only [restore] using eq

/-- A successful impure application traversal at a known location emits the
let-and-direct-call form, retaining the evaluated function. This Lean-side
case connects the executable traversal to the local evaluator equality. -/
theorem callsFuel_app_impure_shape (fuel : Nat) (trace : BackendCommon.Tra) (address : Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.app trace (some address) function args) initial = some (out, final))
    (known : (sptLookup address final.1).isSome = true) (impure : ClosLang.pure function = false) :
    ∃ targetArgs targetFunction middle,
      callsListFuel fuel args initial = some (targetArgs, middle) ∧
      callsFuel fuel function middle = some (targetFunction, final) ∧
      out = .let (BackendCommon.mkCons trace 0) (targetArgs ++ [targetFunction])
        (.call (BackendCommon.mkCons trace 1) targetArgs.length (address + 1)
          (ClosCall.variables .none targetArgs.length)) := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
  obtain ⟨⟨targetArgs, middle⟩, argsRun, ⟨targetFunction, afterFn⟩, fnRun, rest⟩ := run
  by_cases found : (sptLookup address afterFn.1).isSome
  · simp [found, impure] at rest
    obtain ⟨rfl, rfl⟩ := rest
    exact ⟨targetArgs, targetFunction, middle, argsRun, fnRun, rfl⟩
  · simp [found] at rest
    obtain ⟨_, rfl⟩ := rest
    simp [found] at known

/-- The actual impure direct-call traversal output has the same target-side
behavior as applying the evaluated function when the generated stub is
installed. This does not yet establish the cross-state source simulation. -/
theorem callsFuel_app_impure_target_eq {C F : Type} (fuel : Nat) (trace stubTrace : BackendCommon.Tra)
    (address : Nat) (function : ClosLang.Exp) (args : List ClosLang.Exp) (initial final : State)
    (out : ClosLang.Exp) (env values : List ClosSem.Value) (functionValue : ClosSem.Value)
    (state afterArgs afterFunction : ClosSem.State C F) (stubEnv : List ClosSem.Value) (body : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.app trace (some address) function args) initial = some (out, final))
    (known : (sptLookup address final.1).isSome = true) (impure : ClosLang.pure function = false)
    (argsRun : ∀ targetArgs middle, callsListFuel fuel args initial = some (targetArgs, middle) →
      evaluate targetArgs env state = (.val values, afterArgs))
    (functionRun : ∀ targetFunction middle, callsFuel fuel function middle = some (targetFunction, final) →
      evaluate [targetFunction] env afterArgs = (.val [functionValue], afterFunction))
    (code : afterFunction.code.lookup (address + 1) = some (values.length, body))
    (closure : destClosure afterFunction.maxApp (some address) functionValue values =
      some (.fullApp (.call stubTrace 0 (address + 1) (ClosCall.variables stubTrace values.length)) stubEnv [])) :
    evaluate [out] env state = evaluateApp (some address) functionValue values afterFunction := by
  obtain ⟨targetArgs, targetFunction, middle, argsTraversal, functionTraversal, rfl⟩ :=
    callsFuel_app_impure_shape fuel trace address function args initial final out run known impure
  exact evaluate_impure_rewrite_eq_known_app trace stubTrace (address + 1) address targetArgs targetFunction
    env values functionValue state afterArgs afterFunction stubEnv body (argsRun targetArgs middle argsTraversal)
    (functionRun targetFunction middle functionTraversal) code closure

end Flapjack.Compiler.Backend.ClosCall
