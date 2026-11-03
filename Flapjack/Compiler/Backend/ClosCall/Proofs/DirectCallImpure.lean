import Flapjack.Compiler.Backend.ClosCall.Proofs.DirectCallClock

/-! Evaluation of direct-call rewrites that retain an impure function expression. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

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

/-- An error while evaluating a prefix prevents evaluation of an appended
suffix. This Lean-side list-evaluation helper has no standalone HOL original. -/
theorem evaluate_append_prefix_error {C F : Type} (xs ys : List ClosLang.Exp) (env : List ClosSem.Value)
    (state final : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : evaluate xs env state = (.err error, final)) :
    evaluate (xs ++ ys) env state = (.err error, final) := by
  induction xs generalizing state final with
  | nil => simp [evaluate] at run
  | cons first rest ih =>
    cases h : evaluate [first] env state with
    | mk result afterFirst =>
      cases result with
      | err firstError =>
        have whole := ClosProps.evaluate_cons_error first rest env state afterFirst firstError h
        rw [run] at whole
        cases whole
        exact ClosProps.evaluate_cons_error first (rest ++ ys) env state final error h
      | val firstValues =>
        obtain ⟨value, rfl⟩ := evaluate_singleton_value first env state afterFirst firstValues h
        have whole := ClosProps.evaluate_cons_value first rest env state afterFirst value h
        cases tail : evaluate rest env afterFirst with
        | mk tailResult afterTail =>
          cases tailResult with
          | val restValues =>
            simp [tail] at whole
            rw [run] at whole
            cases congrArg Prod.fst whole
          | err tailError =>
            simp [tail] at whole
            rw [run] at whole
            cases whole
            have appended := ih afterFirst final tail
            change evaluate (first :: (rest ++ ys)) env state = _
            rw [ClosProps.evaluate_cons_value first (rest ++ ys) env state afterFirst value h, appended]

/-- A successful prefix followed by an error propagates that error without
introducing values. This Lean-side helper has no standalone HOL declaration. -/
theorem evaluate_append_suffix_error {C F : Type} (xs ys : List ClosLang.Exp) (env : List ClosSem.Value)
    (state middle final : ClosSem.State C F) (values : List ClosSem.Value) (error : ErrorResult ClosSem.Value)
    (firstRun : evaluate xs env state = (.val values, middle))
    (secondRun : evaluate ys env middle = (.err error, final)) :
    evaluate (xs ++ ys) env state = (.err error, final) := by
  induction xs generalizing state middle values with
  | nil =>
    simp [evaluate] at firstRun
    obtain ⟨rfl, rfl⟩ := firstRun.symm
    simpa using secondRun
  | cons first rest ih =>
    cases h : evaluate [first] env state with
    | mk result afterFirst =>
      cases result with
      | err firstError =>
        have whole := ClosProps.evaluate_cons_error first rest env state afterFirst firstError h
        rw [firstRun] at whole
        cases congrArg Prod.fst whole
      | val firstValues =>
        obtain ⟨value, rfl⟩ := evaluate_singleton_value first env state afterFirst firstValues h
        have whole := ClosProps.evaluate_cons_value first rest env state afterFirst value h
        cases tail : evaluate rest env afterFirst with
        | mk tailResult afterTail =>
          cases tailResult with
          | err tailError =>
            simp [tail] at whole
            rw [firstRun] at whole
            cases congrArg Prod.fst whole
          | val restValues =>
            simp [tail] at whole
            rw [firstRun] at whole
            simp only [Prod.mk.injEq, Result.val.injEq] at whole
            obtain ⟨rfl, rfl⟩ := whole
            have appended := ih afterFirst middle restValues tail secondRun
            change evaluate (first :: (rest ++ ys)) env state = _
            rw [ClosProps.evaluate_cons_value first (rest ++ ys) env state afterFirst value h, appended]

/-- The generated impure let propagates an error from the argument prefix.
This is a local evaluation fact, not the complete pass simulation. -/
theorem evaluate_impure_rewrite_args_error {C F : Type} (trace : BackendCommon.Tra) (label : Nat)
    (args : List ClosLang.Exp) (function : ClosLang.Exp) (env : List ClosSem.Value)
    (state final : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : evaluate args env state = (.err error, final)) :
    evaluate [.let (BackendCommon.mkCons trace 0) (args ++ [function])
      (.call (BackendCommon.mkCons trace 1) args.length label (ClosCall.variables .none args.length))] env state =
      (.err error, final) := by
  have appended := evaluate_append_prefix_error args [function] env state final error run
  rw [evaluate, fixClock_evaluate, appended]

/-- The generated impure let propagates an error from function evaluation
once its argument prefix succeeds. This is a local evaluation fact. -/
theorem evaluate_impure_rewrite_function_error {C F : Type} (trace : BackendCommon.Tra) (label : Nat)
    (args : List ClosLang.Exp) (function : ClosLang.Exp) (env values : List ClosSem.Value)
    (state middle final : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (argsRun : evaluate args env state = (.val values, middle))
    (functionRun : evaluate [function] env middle = (.err error, final)) :
    evaluate [.let (BackendCommon.mkCons trace 0) (args ++ [function])
      (.call (BackendCommon.mkCons trace 1) args.length label (ClosCall.variables .none args.length))] env state =
      (.err error, final) := by
  have appended := evaluate_append_suffix_error args [function] env state middle final values error argsRun functionRun
  rw [evaluate, fixClock_evaluate, appended]

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

/-- The actual impure traversal output propagates an argument-evaluation error.
This is a local target-side case, not the full source simulation. -/
theorem callsFuel_app_impure_args_error {C F : Type} (fuel : Nat) (trace : BackendCommon.Tra)
    (address : Nat) (function : ClosLang.Exp) (args : List ClosLang.Exp) (initial final : State)
    (out : ClosLang.Exp) (env : List ClosSem.Value) (state after : ClosSem.State C F)
    (error : ErrorResult ClosSem.Value)
    (run : callsFuel (fuel + 1) (.app trace (some address) function args) initial = some (out, final))
    (known : (sptLookup address final.1).isSome = true) (impure : ClosLang.pure function = false)
    (argsRun : ∀ targetArgs middle, callsListFuel fuel args initial = some (targetArgs, middle) →
      evaluate targetArgs env state = (.err error, after)) :
    evaluate [out] env state = (.err error, after) := by
  obtain ⟨targetArgs, targetFunction, middle, argsTraversal, _, rfl⟩ :=
    callsFuel_app_impure_shape fuel trace address function args initial final out run known impure
  exact evaluate_impure_rewrite_args_error trace (address + 1) targetArgs targetFunction env state after error
    (argsRun targetArgs middle argsTraversal)

/-- The actual impure traversal output propagates a function-evaluation error
after successful arguments. This is a local target-side case. -/
theorem callsFuel_app_impure_function_error {C F : Type} (fuel : Nat) (trace : BackendCommon.Tra)
    (address : Nat) (function : ClosLang.Exp) (args : List ClosLang.Exp) (initial final : State)
    (out : ClosLang.Exp) (env values : List ClosSem.Value) (state afterArgs afterFunction : ClosSem.State C F)
    (error : ErrorResult ClosSem.Value)
    (run : callsFuel (fuel + 1) (.app trace (some address) function args) initial = some (out, final))
    (known : (sptLookup address final.1).isSome = true) (impure : ClosLang.pure function = false)
    (argsRun : ∀ targetArgs middle, callsListFuel fuel args initial = some (targetArgs, middle) →
      evaluate targetArgs env state = (.val values, afterArgs))
    (functionRun : ∀ targetFunction middle, callsFuel fuel function middle = some (targetFunction, final) →
      evaluate [targetFunction] env afterArgs = (.err error, afterFunction)) :
    evaluate [out] env state = (.err error, afterFunction) := by
  obtain ⟨targetArgs, targetFunction, middle, argsTraversal, functionTraversal, rfl⟩ :=
    callsFuel_app_impure_shape fuel trace address function args initial final out run known impure
  exact evaluate_impure_rewrite_function_error trace (address + 1) targetArgs targetFunction env values
    state afterArgs afterFunction error (argsRun targetArgs middle argsTraversal)
    (functionRun targetFunction middle functionTraversal)

/-- The actual impure direct-call traversal output has the same target-side
behavior as applying the evaluated function when the generated stub is
installed. This does not yet establish the cross-state source simulation. -/
theorem callsFuel_app_impure_target_eq {C F : Type} (fuel : Nat) (trace stubTrace : BackendCommon.Tra)
    (address : Nat) (function : ClosLang.Exp) (args : List ClosLang.Exp) (initial final : State)
    (out targetExp : ClosLang.Exp) (targetArgs : List ClosLang.Exp) (middle : State)
    (env values : List ClosSem.Value) (functionValue : ClosSem.Value)
    (state afterArgs afterFunction : ClosSem.State C F) (stubEnv : List ClosSem.Value) (body : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.app trace (some address) function args) initial = some (out, final))
    (known : (sptLookup address final.1).isSome = true) (impure : ClosLang.pure function = false)
    (argsTraversal : callsListFuel fuel args initial = some (targetArgs, middle))
    (functionTraversal : callsFuel fuel function middle = some (targetExp, final))
    (argsRun : evaluate targetArgs env state = (.val values, afterArgs))
    (functionRun : evaluate [targetExp] env afterArgs = (.val [functionValue], afterFunction))
    (code : afterFunction.code.lookup (address + 1) = some (values.length, body))
    (closure : destClosure afterFunction.maxApp (some address) functionValue values =
      some (.fullApp (.call stubTrace 0 (address + 1) (ClosCall.variables stubTrace values.length)) stubEnv [])) :
    evaluate [out] env state = evaluateApp (some address) functionValue values afterFunction := by
  obtain ⟨actualArgs, actualFunction, actualMiddle, actualArgsRun, actualFunctionRun, outEq⟩ :=
    callsFuel_app_impure_shape fuel trace address function args initial final out run known impure
  have argsEq := Option.some.inj (argsTraversal.symm.trans actualArgsRun)
  cases argsEq
  have functionEq := Option.some.inj (functionTraversal.symm.trans actualFunctionRun)
  cases functionEq
  rw [outEq]
  exact evaluate_impure_rewrite_eq_known_app trace stubTrace (address + 1) address targetArgs targetExp
    env values functionValue state afterArgs afterFunction stubEnv body argsRun functionRun code closure

/-- A successful location-annotated closure lookup cannot be a partial
application: the location check requires exact arity and no saved arguments.
This Lean-side helper has no standalone HOL declaration. -/
theorem destClosure_known_not_partial (maxApp address : Nat) (function : ClosSem.Value)
    (args : List ClosSem.Value) (partialValue : ClosSem.Value) :
    destClosure maxApp (some address) function args ≠ some (.partialApp partialValue) := by
  intro h
  cases function <;> simp only [destClosure] at h <;> try contradiction
  case closure location supplied env arity body =>
    split at h
    · rename_i valid
      simp only [Bool.and_eq_true, decide_eq_true_eq, checkLoc] at valid
      split at h
      · rename_i short
        omega
      · simp at h
    · simp at h
  case recclosure location supplied env functions index =>
    cases entry : functions[index]? with
    | none => simp [entry] at h
    | some pair =>
      obtain ⟨arity, body⟩ := pair
      simp only [entry] at h
      split at h
      · rename_i valid
        simp only [Bool.and_eq_true, decide_eq_true_eq, checkLoc] at valid
        split at h
        · rename_i short
          omega
        · simp at h
      · simp at h

/-- Nonempty, non-type-error application at a known location has a full
closure decomposition. This follows from the evaluator and location check and
is not a separate HOL declaration. -/
theorem evaluateApp_known_full {C F : Type} (address : Nat) (function : ClosSem.Value)
    (args : List ClosSem.Value) (state final : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (nonempty : args ≠ []) (run : evaluateApp (some address) function args state = (result, final))
    (notType : result ≠ .err (.abort .typeError)) :
    ∃ body bodyEnv rest, destClosure state.maxApp (some address) function args = some (.fullApp body bodyEnv rest) := by
  cases args with
  | nil => contradiction
  | cons first tail =>
    cases closure : destClosure state.maxApp (some address) function (first :: tail) with
    | none =>
      rw [evaluateApp, closure] at run
      have bad : result = .err (.abort .typeError) := by
        simpa using congrArg Prod.fst run.symm
      exact False.elim (notType bad)
    | some kind =>
      cases kind with
      | partialApp partialValue => exact False.elim (destClosure_known_not_partial state.maxApp address function _ partialValue closure)
      | fullApp body bodyEnv rest => exact ⟨body, bodyEnv, rest, rfl⟩

/-- A location known to an earlier traversal state cannot belong to the
open set when the later state extends it and has disjoint known locations.
This is Lean-side infrastructure for discharging the direct-call side condition. -/
theorem known_location_not_allowed (before after : State) (allowed : Set Nat) (address : Nat)
    (known : (sptLookup address before.1).isSome = true) (growth : stateExtends before after)
    (disjoint : Disjoint allowed (sptDomain after.1)) : address ∉ allowed := by
  intro member
  have earlier : sptMem address before.1 := by simpa [sptMem, sptDomain] using known
  have later := (growth.1 address earlier).1
  exact (Set.disjoint_left.mp disjoint) member later

/-- A known impure direct-call rewrite simulates a source full application
once the argument and function traversals have produced related values. The
body simulation remains an induction input; the source closure decomposition
is derived. This Lean-side case is not HOL's complete growing-state theorem. -/
theorem callsFuel_app_impure_full_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (address : Nat) (function : ClosLang.Exp) (args : List ClosLang.Exp)
    (initial final middle : State) (out targetExp : ClosLang.Exp) (targetArgs : List ClosLang.Exp)
    (env targetValues : List ClosSem.Value)
    (sourceFunction targetFunction : ClosSem.Value) (sourceValues : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target afterArgs afterFunction : ClosSem.State C F)
    (sourceResult : Result (List ClosSem.Value) ClosSem.Value) (sourceFinal : ClosSem.State (NumSet × C) F)
    (run : callsFuel (fuel + 1) (.app trace (some address) function args) initial = some (out, final))
    (known : (sptLookup address final.1).isSome = true) (impure : ClosLang.pure function = false)
    (argsTraversal : callsListFuel fuel args initial = some (targetArgs, middle))
    (functionTraversal : callsFuel fuel function middle = some (targetExp, final))
    (argsRun : evaluate targetArgs env target = (.val targetValues, afterArgs))
    (functionRun : evaluate [targetExp] env afterArgs = (.val [targetFunction], afterFunction))
    (sourceRun : evaluateApp (some address) sourceFunction sourceValues source = (sourceResult, sourceFinal))
    (notType : sourceResult ≠ .err (.abort .typeError))
    (nonempty : sourceValues ≠ [])
    (functions : ValueRelFuel fuel g allowed afterFunction.code sourceFunction targetFunction)
    (values : List.Forall₂ (ValueRelFuel fuel g allowed afterFunction.code) sourceValues targetValues)
    (states : StateRelFuel fuel g allowed source afterFunction)
    (notAllowed : address ∉ allowed) (distinct : (g.2.map Prod.fst).Nodup)
    (bodyIH : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (left right : ClosLang.Exp) (location : Nat) (leftFns rightFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code location leftFns rightFns →
      leftFns[index]? = some (arity, left) → rightFns[index]? = some (arity, right) →
      ExprSimFuel (C := C) (F := F) fuel g allowed left right) :
    ∃ targetResult targetFinal,
      evaluate [out] env target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel g allowed targetFinal.code))
        (ValueRelFuel fuel g allowed targetFinal.code) sourceResult targetResult ∧
      StateRelFuel fuel g allowed sourceFinal targetFinal ∧
      (∀ key value, afterFunction.code.lookup key = some value → targetFinal.code.lookup key = some value) := by
  obtain ⟨sourceBody, sourceBodyEnv, sourceRest, sourceClosure⟩ :=
    evaluateApp_known_full address sourceFunction sourceValues source sourceFinal sourceResult nonempty sourceRun notType
  have sourceClosure' : destClosure afterFunction.maxApp (some address) sourceFunction sourceValues =
      some (.fullApp sourceBody sourceBodyEnv sourceRest) := by
    simpa [← states.2.2.1] using sourceClosure
  obtain ⟨stubTrace, stubEnv, convertedBody, _, _, _, _, _, _, targetClosure, _, found, _, _, _, _, _⟩ :=
    destClosure_known_direct fuel g allowed afterFunction.code afterFunction.maxApp address sourceFunction targetFunction
      sourceValues targetValues sourceBody sourceBodyEnv sourceRest sourceClosure' functions values notAllowed
  have code : afterFunction.code.lookup (address + 1) = some (targetValues.length, convertedBody) := by
    unfold findCode at found
    cases h : afterFunction.code.lookup (address + 1) with
    | none => simp [h] at found
    | some entry =>
      rcases entry with ⟨arity, expression⟩
      simp only [h, bind, Option.bind_some] at found
      split at found
      · rename_i same
        simp only [Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨_, rfl⟩ := found
        rw [same]
      · simp at found
  have targetClosure' : destClosure afterFunction.maxApp (some address) targetFunction targetValues =
      some (.fullApp (.call stubTrace 0 (address + 1) (ClosCall.variables stubTrace targetValues.length)) stubEnv []) := by
    simpa [values.length_eq] using targetClosure
  have targetEq := callsFuel_app_impure_target_eq fuel trace stubTrace address function args initial final out
    targetExp targetArgs middle env targetValues targetFunction target afterArgs afterFunction stubEnv convertedBody
    run known impure argsTraversal functionTraversal argsRun functionRun code targetClosure'
  obtain ⟨targetResult, targetFinal, targetRun, results, finalStates, growth⟩ :=
    appSimFuel_of_bodies fuel g allowed (some address) distinct bodyIH sourceFunction targetFunction sourceValues targetValues
      source afterFunction sourceResult sourceFinal sourceRun notType functions values states
  exact ⟨targetResult, targetFinal, targetEq.trans targetRun, results, finalStates, growth⟩

end Flapjack.Compiler.Backend.ClosCall
