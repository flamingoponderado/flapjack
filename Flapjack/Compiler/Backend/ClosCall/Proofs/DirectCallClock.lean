import Flapjack.Compiler.Backend.ClosCall.Proofs.DirectCallLookup
import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateApplication
import Flapjack.Compiler.Backend.ClosCall.Proofs.ValueWellformed
import Flapjack.Compiler.Backend.Semantics.ClosSem.AppClockShift
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateEventsClockFull
import Flapjack.Compiler.Backend.Semantics.ClosProps.PureEvaluate

/-! Clock and argument behavior of generated direct calls. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

private theorem lookupVars_append {A : Type} (xs ys : List Nat) (env : List A) :
    lookupVars (xs ++ ys) env = (do
      let left ← lookupVars xs env
      let right ← lookupVars ys env
      pure (left ++ right)) := by
  induction xs with
  | nil => simp [lookupVars]
  | cons first rest ih =>
    simp only [List.cons_append, lookupVars, ih]
    cases env[first]? <;> simp
    case some value =>
      cases lookupVars rest env with
      | none => simp
      | some values => cases lookupVars ys env <;> rfl

/-- Looking up an initial range of variables retrieves the corresponding
environment prefix. -/
theorem lookupVars_range {A : Type} (env : List A) (count : Nat) (bound : count ≤ env.length) :
    lookupVars (List.range count) env = some (env.take count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have previous : count ≤ env.length := by omega
    have atIndex : count < env.length := by omega
    rw [List.range_succ, lookupVars_append, ih previous]
    rw [List.take_succ_eq_append_getElem atIndex]
    simp only [lookupVars, List.getElem?_eq_getElem atIndex]
    rfl

/-- Evaluating variable expressions in order agrees with the corresponding
environment lookup and does not change the state. -/
theorem evaluate_variables_lookup {C F : Type} (trace : BackendCommon.Tra)
    (indices : List Nat) (env : List ClosSem.Value) (state : ClosSem.State C F) (values : List ClosSem.Value)
    (lookup : lookupVars indices env = some values) :
    evaluate (indices.map (.var trace)) env state = (.val values, state) := by
  induction indices generalizing values with
  | nil => simp [lookupVars] at lookup; subst values; simp [evaluate]
  | cons index rest ih =>
    simp only [lookupVars, Bind.bind, Option.bind_eq_some_iff, Option.some.injEq] at lookup
    obtain ⟨value, found, tail, tailFound, rfl⟩ := lookup
    have firstRun : evaluate [.var trace index] env state = (.val [value], state) := by
      simp [evaluate, found]
    have tailRun := ih tail tailFound
    simp only [List.map_cons, ClosProps.evaluate_cons_value _ _ _ _ _ _ firstRun, tailRun]

/-- The generated variable list evaluates to the argument prefix without
consuming clock or changing any other state. -/
theorem evaluate_variables {C F : Type} (trace : BackendCommon.Tra) (count : Nat)
    (env : List ClosSem.Value) (state : ClosSem.State C F) (bound : count ≤ env.length) :
    evaluate (ClosCall.variables trace count) env state = (.val (env.take count), state) := by
  exact evaluate_variables_lookup trace (List.range count) env state (env.take count) (lookupVars_range env count bound)

/-- A generated stub with one extra starting tick executes the installed
body at the original clock, using the selected argument prefix. -/
theorem evaluate_generated_stub {C F : Type} (trace : BackendCommon.Tra) (label arity : Nat)
    (body : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (bound : arity ≤ env.length) (code : state.code.lookup label = some (arity, body)) :
    evaluate [.call trace 0 label (ClosCall.variables trace arity)] env
      { state with clock := state.clock + 1 } = evaluate [body] (env.take arity) state := by
  rw [evaluate]
  rw [fixClock_evaluate, evaluate_variables trace arity env _ bound]
  simp [findCode, code, List.length_take, Nat.min_eq_left bound, decClock]

/-- A rewritten direct call spends its extra tick as part of the call cost.
This is a local evaluator fact; it does not establish the pass simulation. -/
theorem evaluate_rewritten_call {C F : Type} (trace : BackendCommon.Tra) (label : Nat)
    (args : List ClosLang.Exp) (env values : List ClosSem.Value)
    (state afterArgs : ClosSem.State C F) (body : ClosLang.Exp)
    (argsRun : evaluate args env state = (.val values, afterArgs))
    (code : afterArgs.code.lookup label = some (values.length, body)) :
    evaluate [.call trace values.length label args] env { state with clock := state.clock + 1 } =
      if afterArgs.clock < values.length then
        (.err (.abort .timeoutError), { afterArgs with clock := 0 })
      else evaluate [body] values (decClock values.length afterArgs) := by
  have shifted := (evaluate_addClock (C := C) (F := F)).1 args env state afterArgs
    (.val values) 1 argsRun (by simp)
  rw [evaluate, fixClock_evaluate, shifted]
  by_cases enough : values.length ≤ afterArgs.clock
  · have notShort : ¬ afterArgs.clock < values.length := by omega
    simp [findCode, code, notShort, decClock, Nat.add_sub_add_right]
  · have short : afterArgs.clock < values.length := by omega
    simp [findCode, code, short]

/-- Once the argument cost is available, the rewritten call and the generated
closure stub enter the same installed body with the same arguments and state.
This connects the local call and stub clock facts, not the full pass proof. -/
theorem evaluate_rewritten_call_eq_stub {C F : Type}
    (trace stubTrace : BackendCommon.Tra) (label : Nat)
    (args : List ClosLang.Exp) (env values stubEnv : List ClosSem.Value)
    (state afterArgs : ClosSem.State C F) (body : ClosLang.Exp)
    (argsRun : evaluate args env state = (.val values, afterArgs))
    (code : afterArgs.code.lookup label = some (values.length, body))
    (enough : values.length ≤ afterArgs.clock)
    (bound : values.length ≤ stubEnv.length)
    (prefixEq : stubEnv.take values.length = values) :
    evaluate [.call trace values.length label args] env { state with clock := state.clock + 1 } =
      evaluate [.call stubTrace 0 label (ClosCall.variables stubTrace values.length)] stubEnv
        { decClock values.length afterArgs with clock := (decClock values.length afterArgs).clock + 1 } := by
  rw [evaluate_rewritten_call trace label args env values state afterArgs body argsRun code]
  rw [if_neg (Nat.not_lt.mpr enough)]
  rw [evaluate_generated_stub stubTrace label values.length body stubEnv _ bound]
  · rw [prefixEq]
  · simpa [decClock] using code

/-- A successful known-location full application puts exactly the supplied
arguments at the front of its body environment and leaves no over-application. -/
theorem destClosure_known_prefix (maxApp address : Nat) (function : ClosSem.Value)
    (args env rest : List ClosSem.Value) (body : ClosLang.Exp)
    (run : destClosure maxApp (some address) function args = some (.fullApp body env rest)) :
    ∃ captured, env = args ++ captured ∧ rest = [] := by
  have takeRev : (args.reverse.take args.length).reverse = args := by
    simpa only [List.length_reverse, List.reverse_reverse] using
      congrArg List.reverse (List.take_length (l := args.reverse))
  cases function <;> simp only [destClosure] at run <;> try contradiction
  case closure location supplied captured arity expression =>
    split at run
    · rename_i valid
      have facts : arity = args.length ∧ supplied.length = 0 := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, checkLoc] at valid
        exact ⟨valid.1.1, valid.1.2.1⟩
      obtain ⟨arityEq, suppliedEq⟩ := facts
      have suppliedNil : supplied = [] := by cases supplied <;> simp_all
      subst supplied
      split at run
      · simp at run
      · simp [arityEq] at run
        obtain ⟨_, rfl, rfl⟩ := run
        exact ⟨captured, by rw [takeRev], by simp⟩
    · simp at run
  case recclosure location supplied captured functions index =>
    split at run
    · simp at run
    · rename_i arity expression found
      split at run
      · rename_i valid
        have facts : arity = args.length ∧ supplied.length = 0 := by
          simp only [Bool.and_eq_true, decide_eq_true_eq, checkLoc] at valid
          exact ⟨valid.1.1, valid.1.2.1⟩
        obtain ⟨arityEq, suppliedEq⟩ := facts
        have suppliedNil : supplied = [] := by cases supplied <;> simp_all
        subst supplied
        split at run
        · simp at run
        · simp [arityEq] at run
          obtain ⟨_, rfl, rfl⟩ := run
          exact ⟨(List.range functions.length).map
            (fun i => ClosSem.Value.recclosure location [] captured functions i) ++ captured,
            by rw [takeRev], by simp⟩
      · simp at run

/-- The environment condition for the call/stub comparison follows from
successful known-location closure decomposition. -/
theorem evaluate_rewritten_call_eq_known_stub {C F : Type}
    (trace stubTrace : BackendCommon.Tra) (label maxApp address : Nat)
    (args : List ClosLang.Exp) (env values stubEnv : List ClosSem.Value)
    (function : ClosSem.Value) (state afterArgs : ClosSem.State C F) (body : ClosLang.Exp)
    (argsRun : evaluate args env state = (.val values, afterArgs))
    (code : afterArgs.code.lookup label = some (values.length, body))
    (enough : values.length ≤ afterArgs.clock)
    (closure : destClosure maxApp (some address) function values =
      some (.fullApp (.call stubTrace 0 label (ClosCall.variables stubTrace values.length)) stubEnv [])) :
    evaluate [.call trace values.length label args] env { state with clock := state.clock + 1 } =
      evaluate [.call stubTrace 0 label (ClosCall.variables stubTrace values.length)] stubEnv
        { decClock values.length afterArgs with clock := (decClock values.length afterArgs).clock + 1 } := by
  obtain ⟨captured, rfl, _⟩ := destClosure_known_prefix maxApp address function values stubEnv [] _ closure
  apply evaluate_rewritten_call_eq_stub trace stubTrace label args env values (values ++ captured)
    state afterArgs body argsRun code enough
  · simp
  · simp

/-- A known-location application of a generated stub agrees with its
rewritten direct call when the argument cost is available. The application
starts after argument evaluation, with the same one-tick allowance. -/
theorem evaluate_rewritten_call_eq_known_app {C F : Type}
    (trace stubTrace : BackendCommon.Tra) (label address : Nat)
    (args : List ClosLang.Exp) (env values stubEnv : List ClosSem.Value)
    (function : ClosSem.Value) (state afterArgs : ClosSem.State C F) (body : ClosLang.Exp)
    (argsRun : evaluate args env state = (.val values, afterArgs))
    (code : afterArgs.code.lookup label = some (values.length, body))
    (enough : values.length ≤ afterArgs.clock)
    (closure : destClosure afterArgs.maxApp (some address) function values =
      some (.fullApp (.call stubTrace 0 label (ClosCall.variables stubTrace values.length)) stubEnv [])) :
    evaluate [.call trace values.length label args] env { state with clock := state.clock + 1 } =
      evaluateApp (some address) function values { afterArgs with clock := afterArgs.clock + 1 } := by
  have nonempty : values ≠ [] := by
    intro empty
    have smaller := destClosure_full_remaining_lt afterArgs.maxApp (some address) function values stubEnv [] _ closure
    simp [empty] at smaller
  have shift : afterArgs.clock + 1 - values.length = afterArgs.clock - values.length + 1 := by omega
  have stateEq : decClock values.length { afterArgs with clock := afterArgs.clock + 1 } =
      { decClock values.length afterArgs with clock := (decClock values.length afterArgs).clock + 1 } := by
    simp [decClock, shift]
  rw [evaluate_rewritten_call_eq_known_stub trace stubTrace label afterArgs.maxApp address args env values
    stubEnv function state afterArgs body argsRun code enough closure]
  cases values with
  | nil => contradiction
  | cons first rest =>
    rw [evaluateApp]
    rw [closure]
    simp only [List.length_cons, List.length_nil, Nat.sub_zero]
    have enough' : ¬ afterArgs.clock + 1 < rest.length + 1 := by simp only [List.length_cons] at enough; omega
    simp only [enough', ↓reduceIte, fixClock_evaluate]
    simp only [List.length_cons] at stateEq
    rw [stateEq]
    cases run : evaluate [.call stubTrace 0 label (ClosCall.variables stubTrace (first :: rest).length)] stubEnv
        { decClock (first :: rest).length afterArgs with
          clock := (decClock (first :: rest).length afterArgs).clock + 1 } with
    | mk result final =>
      cases result with
      | err error => rfl
      | val resultValues =>
        obtain ⟨value, rfl⟩ := evaluate_singleton_value _ _ _ _ resultValues run
        simp [evaluateApp]

/-- The known-stub comparison also covers insufficient clock, including the
boundary where application reaches the stub with no tick left. -/
theorem evaluate_rewritten_call_eq_known_app_all {C F : Type}
    (trace stubTrace : BackendCommon.Tra) (label address : Nat)
    (args : List ClosLang.Exp) (env values stubEnv : List ClosSem.Value)
    (function : ClosSem.Value) (state afterArgs : ClosSem.State C F) (body : ClosLang.Exp)
    (argsRun : evaluate args env state = (.val values, afterArgs))
    (code : afterArgs.code.lookup label = some (values.length, body))
    (closure : destClosure afterArgs.maxApp (some address) function values =
      some (.fullApp (.call stubTrace 0 label (ClosCall.variables stubTrace values.length)) stubEnv [])) :
    evaluate [.call trace values.length label args] env { state with clock := state.clock + 1 } =
      evaluateApp (some address) function values { afterArgs with clock := afterArgs.clock + 1 } := by
  by_cases enough : values.length ≤ afterArgs.clock
  · exact evaluate_rewritten_call_eq_known_app trace stubTrace label address args env values stubEnv
      function state afterArgs body argsRun code enough closure
  · have short : afterArgs.clock < values.length := by omega
    obtain ⟨captured, stubEq, _⟩ := destClosure_known_prefix afterArgs.maxApp address function values stubEnv [] _ closure
    have bound : values.length ≤ stubEnv.length := by rw [stubEq]; simp
    have zeroStub : evaluate [.call stubTrace 0 label (ClosCall.variables stubTrace values.length)] stubEnv
        { afterArgs with clock := 0 } = (.err (.abort .timeoutError), { afterArgs with clock := 0 }) := by
      rw [evaluate, fixClock_evaluate, evaluate_variables stubTrace values.length stubEnv _ bound]
      simp [findCode, code, List.length_take, Nat.min_eq_left bound]
    rw [evaluate_rewritten_call trace label args env values state afterArgs body argsRun code]
    simp only [short, ↓reduceIte]
    cases values with
    | nil => simp at short
    | cons first rest =>
      rw [evaluateApp, closure]
      simp only [List.length_cons, List.length_nil, Nat.sub_zero]
      by_cases timeout : afterArgs.clock + 1 < rest.length + 1
      · simp [timeout]
      · have zero : afterArgs.clock + 1 - (rest.length + 1) = 0 := by
          simp only [List.length_cons] at short
          omega
        simp only [timeout, ↓reduceIte, fixClock_evaluate]
        simp only [decClock, zero]
        simp only [List.length_cons] at zeroStub
        rw [zeroStub]

/-- A related known-location closure supplies the installed stub and code
entry needed by the direct-call/application comparison. This is still a
local target-side equality, not a source-to-target pass simulation. -/
theorem related_known_app_eq_rewritten_call {C F : Type}
    (fuel : Nat) (g : State) (allowed : Set Nat) (trace : BackendCommon.Tra) (address : Nat)
    (source target : ClosSem.Value) (sourceValues targetValues : List ClosSem.Value)
    (sourceBody : ClosLang.Exp) (sourceBodyEnv sourceRest : List ClosSem.Value)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (state afterArgs : ClosSem.State C F)
    (argsRun : evaluate args env state = (.val targetValues, afterArgs))
    (sourceClosure : destClosure afterArgs.maxApp (some address) source sourceValues =
      some (.fullApp sourceBody sourceBodyEnv sourceRest))
    (functions : ValueRelFuel fuel g allowed afterArgs.code source target)
    (values : List.Forall₂ (ValueRelFuel fuel g allowed afterArgs.code) sourceValues targetValues)
    (notAllowed : address ∉ allowed) :
    evaluate [.call trace targetValues.length (address + 1) args] env
        { state with clock := state.clock + 1 } =
      evaluateApp (some address) target targetValues { afterArgs with clock := afterArgs.clock + 1 } := by
  obtain ⟨stubTrace, stubEnv, convertedBody, _, _, _, _, _, _, targetClosure, _, found, _, _, _, _, _⟩ :=
    destClosure_known_direct fuel g allowed afterArgs.code afterArgs.maxApp address source target
      sourceValues targetValues sourceBody sourceBodyEnv sourceRest sourceClosure functions values notAllowed
  have code : afterArgs.code.lookup (address + 1) = some (targetValues.length, convertedBody) := by
    unfold findCode at found
    cases h : afterArgs.code.lookup (address + 1) with
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
  have targetClosure' : destClosure afterArgs.maxApp (some address) target targetValues =
      some (.fullApp (.call stubTrace 0 (address + 1) (ClosCall.variables stubTrace targetValues.length)) stubEnv []) := by
    simpa [values.length_eq] using targetClosure
  exact evaluate_rewritten_call_eq_known_app_all trace stubTrace (address + 1) address args env targetValues
    stubEnv target state afterArgs convertedBody argsRun code targetClosure'

/-- A non-timeout source application is simulated by the rewritten call
with one extra target tick. The stated body induction hypothesis and the
fuel-aware relations are proof infrastructure, not the complete HOL result. -/
theorem known_app_to_rewritten_call_fuel {C F : Type}
    (fuel : Nat) (g : State) (allowed : Set Nat) (trace : BackendCommon.Tra) (address : Nat)
    (sourceFun targetFun : ClosSem.Value) (sourceValues targetValues : List ClosSem.Value)
    (sourceBody : ClosLang.Exp) (sourceBodyEnv sourceRest : List ClosSem.Value)
    (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target afterArgs : ClosSem.State C F)
    (sourceResult : Result (List ClosSem.Value) ClosSem.Value) (sourceFinal : ClosSem.State (NumSet × C) F)
    (argsRun : evaluate args env target = (.val targetValues, afterArgs))
    (sourceRun : evaluateApp (some address) sourceFun sourceValues source = (sourceResult, sourceFinal))
    (notType : sourceResult ≠ .err (.abort .typeError))
    (notTimeout : sourceResult ≠ .err (.abort .timeoutError))
    (sourceClosure : destClosure source.maxApp (some address) sourceFun sourceValues =
      some (.fullApp sourceBody sourceBodyEnv sourceRest))
    (functions : ValueRelFuel fuel g allowed afterArgs.code sourceFun targetFun)
    (values : List.Forall₂ (ValueRelFuel fuel g allowed afterArgs.code) sourceValues targetValues)
    (states : StateRelFuel fuel g allowed source afterArgs)
    (notAllowed : address ∉ allowed) (distinct : (g.2.map Prod.fst).Nodup)
    (bodyIH : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (left right : ClosLang.Exp) (location : Nat) (leftFns rightFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code location leftFns rightFns →
      leftFns[index]? = some (arity, left) → rightFns[index]? = some (arity, right) →
      ExprSimFuel (C := C) (F := F) fuel g allowed left right) :
    ∃ targetResult targetFinal,
      evaluate [.call trace targetValues.length (address + 1) args] env
          { target with clock := target.clock + 1 } =
        (targetResult, { targetFinal with clock := targetFinal.clock + 1 }) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel g allowed targetFinal.code))
        (ValueRelFuel fuel g allowed targetFinal.code) sourceResult targetResult ∧
      StateRelFuel fuel g allowed sourceFinal targetFinal ∧
      (∀ key value, afterArgs.code.lookup key = some value → targetFinal.code.lookup key = some value) := by
  obtain ⟨targetResult, targetFinal, targetRun, results, finalStates, growth⟩ :=
    appSimFuel_of_bodies fuel g allowed (some address) distinct bodyIH sourceFun targetFun sourceValues targetValues
      source afterArgs sourceResult sourceFinal sourceRun notType functions values states
  have targetNotTimeout : targetResult ≠ .err (.abort .timeoutError) := by
    intro bad
    subst targetResult
    cases sourceResult with
    | val value => simp [resultRel] at results
    | err error =>
      cases error with
      | raise value => simp [resultRel, excRel] at results
      | abort reason =>
        simp [resultRel, excRel] at results
        subst reason
        exact notTimeout rfl
  have shifted := (evaluate_addClock (C := C) (F := F)).2 (some address) targetFun targetValues
    afterArgs targetFinal targetResult 1 targetRun targetNotTimeout
  have sourceClosure' : destClosure afterArgs.maxApp (some address) sourceFun sourceValues =
      some (.fullApp sourceBody sourceBodyEnv sourceRest) := by
    simpa [← states.2.2.1] using sourceClosure
  have direct := related_known_app_eq_rewritten_call fuel g allowed trace address sourceFun targetFun
    sourceValues targetValues sourceBody sourceBodyEnv sourceRest args env target afterArgs argsRun
    sourceClosure' functions values notAllowed
  exact ⟨targetResult, targetFinal, direct.trans shifted, results, finalStates, growth⟩

/-- The source application's event trace is a prefix of the rewritten
call's trace, including when the source times out. The extra target tick may
let the call continue, so this does not claim equality of timeout results. -/
theorem known_app_rewritten_call_events_fuel {C F : Type}
    (fuel : Nat) (g : State) (allowed : Set Nat) (trace : BackendCommon.Tra) (address : Nat)
    (sourceFun targetFun : ClosSem.Value) (sourceValues targetValues : List ClosSem.Value)
    (sourceBody : ClosLang.Exp) (sourceBodyEnv sourceRest : List ClosSem.Value)
    (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target afterArgs : ClosSem.State C F)
    (sourceResult : Result (List ClosSem.Value) ClosSem.Value) (sourceFinal : ClosSem.State (NumSet × C) F)
    (argsRun : evaluate args env target = (.val targetValues, afterArgs))
    (sourceRun : evaluateApp (some address) sourceFun sourceValues source = (sourceResult, sourceFinal))
    (notType : sourceResult ≠ .err (.abort .typeError))
    (sourceClosure : destClosure source.maxApp (some address) sourceFun sourceValues =
      some (.fullApp sourceBody sourceBodyEnv sourceRest))
    (functions : ValueRelFuel fuel g allowed afterArgs.code sourceFun targetFun)
    (values : List.Forall₂ (ValueRelFuel fuel g allowed afterArgs.code) sourceValues targetValues)
    (states : StateRelFuel fuel g allowed source afterArgs)
    (notAllowed : address ∉ allowed) (distinct : (g.2.map Prod.fst).Nodup)
    (bodyIH : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (left right : ClosLang.Exp) (location : Nat) (leftFns rightFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code location leftFns rightFns →
      leftFns[index]? = some (arity, left) → rightFns[index]? = some (arity, right) →
      ExprSimFuel (C := C) (F := F) fuel g allowed left right) :
    sourceFinal.ffi.ioEvents <+:
      (evaluate [.call trace targetValues.length (address + 1) args] env
        { target with clock := target.clock + 1 }).2.ffi.ioEvents := by
  obtain ⟨targetResult, targetFinal, targetRun, _, finalStates, _⟩ :=
    appSimFuel_of_bodies fuel g allowed (some address) distinct bodyIH sourceFun targetFun sourceValues targetValues
      source afterArgs sourceResult sourceFinal sourceRun notType functions values states
  have sourceClosure' : destClosure afterArgs.maxApp (some address) sourceFun sourceValues =
      some (.fullApp sourceBody sourceBodyEnv sourceRest) := by
    simpa [← states.2.2.1] using sourceClosure
  have direct := related_known_app_eq_rewritten_call fuel g allowed trace address sourceFun targetFun
    sourceValues targetValues sourceBody sourceBodyEnv sourceRest args env target afterArgs argsRun
    sourceClosure' functions values notAllowed
  have events := (evaluate_addClock_ioEvents_prefix (C := C) (F := F)).2
    (some address) targetFun targetValues afterArgs 1
  rw [targetRun, ← direct] at events
  simpa only [finalStates.1] using events

/-- A pure function expression can be evaluated in a constructed related
environment to obtain a related closure value without changing target state.
The fuel-aware well-formedness invariant is still proof-side infrastructure. -/
theorem pure_function_valueRelFuel {C F : Type}
    (fuel : Nat) (g : State) (allowed : Set Nat)
    (sourceFn targetFn : ClosLang.Exp) (sourceEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceValue : ClosSem.Value)
    (sourceRun : evaluate [sourceFn] sourceEnv source = (.val [sourceValue], source))
    (targetPure : ClosLang.pure targetFn = true)
    (wf : ValuesWellFormedFuel fuel g allowed target.code sourceEnv)
    (states : StateRelFuel fuel g allowed source target)
    (fnIH : ExprSimFuel (C := C) (F := F) fuel g allowed sourceFn targetFn) :
    ∃ targetValue, ValueRelFuel fuel g allowed target.code sourceValue targetValue := by
  obtain ⟨targetEnv, _, envs⟩ := envRelFuel_exists_of_wellFormed fuel g allowed target.code sourceEnv wf
  obtain ⟨targetResult, targetFinal, targetRun, results, _, _⟩ :=
    fnIH sourceEnv targetEnv source target (.val [sourceValue]) source sourceRun (by simp)
      (envs 0 [(0, targetFn)]) states
  have notType : targetResult ≠ .err (.abort .typeError) := by
    intro error
    subst targetResult
    simp [resultRel] at results
  have pureList : ClosLang.pureList [targetFn] = true := by simp [ClosLang.pureList, targetPure]
  obtain ⟨targetValues, rfl, rfl⟩ := ClosProps.evaluate_pure [targetFn] targetEnv target targetFinal
    targetResult pureList targetRun notType
  cases results with
  | cons head tail =>
    cases tail
    exact ⟨_, head⟩

end Flapjack.Compiler.Backend.ClosCall
