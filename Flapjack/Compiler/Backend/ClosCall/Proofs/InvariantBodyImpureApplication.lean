import Flapjack.Compiler.Backend.ClosCall.Proofs.InvariantBodyPureApplication

/-! Impure direct-call simulation with invariant-aware closure bodies. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- A known impure direct-call rewrite simulates a source full application
once the argument and function traversals have produced related values. The
body simulation remains an induction input; the source closure decomposition
is derived. This Lean-side case is not HOL's complete growing-state theorem. -/
theorem callsFuel_app_impure_full_invariant_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
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
    (functionWf : ValueWellFormedFuel fuel g allowed afterFunction.code sourceFunction)
    (argsWf : ValuesWellFormedFuel fuel g allowed afterFunction.code sourceValues)
    (sourceWf : StateWellFormedFuel fuel g allowed afterFunction.code source)
    (states : StateRelFuel fuel g allowed source afterFunction)
    (notAllowed : address ∉ allowed) (distinct : (g.2.map Prod.fst).Nodup)
    (bodyIH : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (left right : ClosLang.Exp) (location : Nat) (leftFns rightFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code location leftFns rightFns →
      leftFns[index]? = some (arity, left) → rightFns[index]? = some (arity, right) →
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed left right)
    (bodyWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (body targetBody : ClosLang.Exp) (location : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code location sourceFns targetFns →
      sourceFns[index]? = some (arity, body) → targetFns[index]? = some (arity, targetBody) →
      ∀ (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
        ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
        EvalWellFormedFuel fuel g allowed code (evaluate [body] env state)) :
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
    appSimFuelInvariant_of_bodies fuel g allowed (some address) distinct bodyIH bodyWf sourceFunction targetFunction sourceValues targetValues
      source afterFunction sourceResult sourceFinal sourceRun notType functions values functionWf argsWf sourceWf states
  exact ⟨targetResult, targetFinal, targetEq.trans targetRun, results, finalStates, growth⟩

/-- The actual impure known-location traversal case composes argument and
invariant-aware function and argument simulations with the extracted direct call.
Argument evaluation must preserve source well-formedness. The body simulation and
fixed compiler-state relation are induction infrastructure; this is not the
complete HOL growing-state or oracle theorem. -/
theorem callsFuel_app_impure_invariant_bodies_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (address : Nat) (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.app trace (some address) sourceFn sourceArgs) initial = some (out, final))
    (known : (sptLookup address final.1).isSome = true) (impure : ClosLang.pure sourceFn = false)
    (notAllowed : address ∉ allowed) (distinct : (g.2.map Prod.fst).Nodup)
    (argsIH : ∀ targetArgs middle, callsListFuel fuel sourceArgs initial = some (targetArgs, middle) →
      ExprsSimFuelInvariant (C := C) (F := F) fuel g allowed sourceArgs targetArgs)
    (argsWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
      EvalWellFormedFuel fuel g allowed code (evaluate sourceArgs env state))
    (fnIH : ∀ targetFn middle, callsFuel fuel sourceFn middle = some (targetFn, final) →
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed sourceFn targetFn)
    (fnWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
      EvalWellFormedFuel fuel g allowed code (evaluate [sourceFn] env state))
    (bodyIH : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (sourceBody targetBody : ClosLang.Exp) (location : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code location sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed sourceBody targetBody)
    (bodyWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (body targetBody : ClosLang.Exp) (location : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code location sourceFns targetFns →
      sourceFns[index]? = some (arity, body) → targetFns[index]? = some (arity, targetBody) →
      ∀ (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
        ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
        EvalWellFormedFuel fuel g allowed code (evaluate [body] env state)) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed (.app trace (some address) sourceFn sourceArgs) out := by
  obtain ⟨targetArgs, targetFn, middle, argsTraversal, fnTraversal, outEq⟩ :=
    callsFuel_app_impure_shape fuel trace address sourceFn sourceArgs initial final out run known impure
  intro sourceEnv targetEnv source target sourceResult sourceFinal sourceRun notType envs envWf sourceWf states
  have bindingEnv : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0
      ((targetArgs ++ [targetFn]).map (0, ·)) := by
    apply envRelFuel_let_bindings (BackendCommon.mkCons trace 0) (targetArgs ++ [targetFn])
      (.call (BackendCommon.mkCons trace 1) targetArgs.length (address + 1)
        (ClosCall.variables .none targetArgs.length))
    simpa [outEq] using envs
  have argsEnv : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0 (targetArgs.map (0, ·)) := by
    apply envRelFuel_subset bindingEnv
    intro item member
    simp only [List.map_append, List.mem_append]
    exact Or.inl member
  have fnEnv : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0 [(0, targetFn)] := by
    apply envRelFuel_subset bindingEnv
    intro item member
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at member ⊢
    exact Or.inr member
  cases sourceArgs with
  | nil =>
    have bad : sourceResult = .err (.abort .typeError) := by
      simpa [evaluate] using congrArg Prod.fst sourceRun.symm
    exact False.elim (notType bad)
  | cons first rest =>
    rw [evaluate] at sourceRun
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate] at sourceRun
    cases sourceArgsRun : evaluate (first :: rest) sourceEnv source with
    | mk argsResult argsFinal =>
      have argsNotType : argsResult ≠ .err (.abort .typeError) := by
        intro bad
        subst argsResult
        have : sourceResult = .err (.abort .typeError) := by
          simpa [sourceArgsRun] using congrArg Prod.fst sourceRun.symm
        exact notType this
      obtain ⟨targetArgsResult, targetArgsFinal, targetArgsRun, argsRel, argsStates, argsGrowth⟩ :=
        argsIH targetArgs middle argsTraversal sourceEnv targetEnv source target argsResult argsFinal
          sourceArgsRun argsNotType argsEnv envWf sourceWf states
      cases argsResult with
      | err error =>
        cases targetArgsResult with
        | val values => simp [resultRel] at argsRel
        | err targetError =>
          have sourceEq : sourceResult = .err error ∧ sourceFinal = argsFinal := by
            simpa [sourceArgsRun] using sourceRun.symm
          obtain ⟨rfl, rfl⟩ := sourceEq
          refine ⟨.err targetError, targetArgsFinal, ?_, argsRel, argsStates, argsGrowth⟩
          rw [outEq]
          exact evaluate_impure_rewrite_args_error trace (address + 1) targetArgs targetFn targetEnv target targetArgsFinal targetError targetArgsRun
      | val sourceValues =>
        cases targetArgsResult with
        | err error => simp [resultRel] at argsRel
        | val targetValues =>
          have valuesRel : List.Forall₂ (ValueRelFuel fuel g allowed targetArgsFinal.code) sourceValues targetValues := argsRel
          have fnEnv' : EnvRelFuel fuel g allowed targetArgsFinal.code sourceEnv targetEnv 0 [(0, targetFn)] :=
            envRelFuel_mono fnEnv (stateExtends_refl g distinct) Set.Subset.rfl argsGrowth
          have fnEnvWf := valuesWellFormedFuel_mono envWf (stateExtends_refl g distinct) Set.Subset.rfl argsGrowth
          have argsStateWf : StateWellFormedFuel fuel g allowed targetArgsFinal.code argsFinal := by
            have well := argsWf target.code sourceEnv source envWf sourceWf
            rw [sourceArgsRun] at well
            exact stateWellFormedFuel_mono well.2 (stateExtends_refl g distinct) Set.Subset.rfl argsGrowth
          cases sourceFnRun : evaluate [sourceFn] sourceEnv argsFinal with
          | mk fnResult fnFinal =>
            have fnNotType : fnResult ≠ .err (.abort .typeError) := by
              intro bad
              subst fnResult
              have : sourceResult = .err (.abort .typeError) := by
                simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using congrArg Prod.fst sourceRun.symm
              exact notType this
            obtain ⟨targetFnResult, targetFnFinal, targetFnRun, fnRel, fnStates, fnGrowth⟩ :=
              fnIH targetFn middle fnTraversal sourceEnv targetEnv argsFinal targetArgsFinal fnResult fnFinal
                sourceFnRun fnNotType fnEnv' fnEnvWf argsStateWf argsStates
            cases fnResult with
            | err error =>
              cases targetFnResult with
              | val values => simp [resultRel] at fnRel
              | err targetError =>
                have sourceEq : sourceResult = .err error ∧ sourceFinal = fnFinal := by
                  simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using sourceRun.symm
                obtain ⟨rfl, rfl⟩ := sourceEq
                refine ⟨.err targetError, targetFnFinal, ?_, fnRel, fnStates, ?_⟩
                · rw [outEq]
                  exact evaluate_impure_rewrite_function_error trace (address + 1) targetArgs targetFn targetEnv
                    targetValues target targetArgsFinal targetFnFinal targetError targetArgsRun targetFnRun
                · intro key item lookup
                  exact fnGrowth key item (argsGrowth key item lookup)
            | val fnValues =>
              obtain ⟨fnValue, rfl⟩ := evaluate_singleton_value sourceFn sourceEnv argsFinal fnFinal fnValues sourceFnRun
              cases targetFnResult with
              | err error => simp [resultRel] at fnRel
              | val targetFnValues =>
                obtain ⟨targetFnValue, rfl⟩ :=
                  evaluate_singleton_value targetFn targetEnv targetArgsFinal targetFnFinal targetFnValues targetFnRun
                have functionRel : ValueRelFuel fuel g allowed targetFnFinal.code fnValue targetFnValue := by
                  simpa [resultRel] using fnRel
                have valuesRel' : List.Forall₂ (ValueRelFuel fuel g allowed targetFnFinal.code) sourceValues targetValues :=
                  List.Forall₂.imp (fun _ _ h => valueRelFuel_mono h (stateExtends_refl g distinct) Set.Subset.rfl fnGrowth) valuesRel
                have appRun : evaluateApp (some address) fnValue sourceValues fnFinal = (sourceResult, sourceFinal) := by
                  simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using sourceRun
                have nonempty : sourceValues ≠ [] := by
                  have len := (evaluate_length (C := NumSet × C) (F := F)).1 (first :: rest) sourceEnv source argsFinal sourceValues sourceArgsRun
                  intro empty
                  simp [empty] at len
                have argumentWf : ValuesWellFormedFuel fuel g allowed targetFnFinal.code sourceValues := by
                  have well := argsWf target.code sourceEnv source envWf sourceWf
                  rw [sourceArgsRun] at well
                  exact valuesWellFormedFuel_mono well.1 (stateExtends_refl g distinct) Set.Subset.rfl
                    (fun key item lookup => fnGrowth key item (argsGrowth key item lookup))
                have functionWf : ValueWellFormedFuel fuel g allowed targetFnFinal.code fnValue := by
                  have well := fnWf targetArgsFinal.code sourceEnv argsFinal fnEnvWf argsStateWf
                  rw [sourceFnRun] at well
                  have valueWf : ValueWellFormedFuel fuel g allowed targetArgsFinal.code fnValue := by
                    cases well.1 with
                    | cons head tail => exact head
                  exact valueWellFormedFuel_mono valueWf (stateExtends_refl g distinct) Set.Subset.rfl fnGrowth
                have afterFunctionWf : StateWellFormedFuel fuel g allowed targetFnFinal.code fnFinal := by
                  have well := fnWf targetArgsFinal.code sourceEnv argsFinal fnEnvWf argsStateWf
                  rw [sourceFnRun] at well
                  exact stateWellFormedFuel_mono well.2 (stateExtends_refl g distinct) Set.Subset.rfl fnGrowth
                obtain ⟨result, finalTarget, targetRun, results, finalStates, growth⟩ :=
                  callsFuel_app_impure_full_invariant_sim fuel g allowed trace address sourceFn (first :: rest)
                    initial final middle out targetFn targetArgs targetEnv targetValues fnValue targetFnValue sourceValues
                    fnFinal target targetArgsFinal targetFnFinal sourceResult sourceFinal run known impure
                    argsTraversal fnTraversal targetArgsRun targetFnRun appRun notType nonempty functionRel valuesRel'
                    functionWf argumentWf afterFunctionWf fnStates notAllowed distinct bodyIH bodyWf
                refine ⟨result, finalTarget, targetRun, results, finalStates, ?_⟩
                intro key item lookup
                exact growth key item (fnGrowth key item (argsGrowth key item lookup))

/-- The actual application traversal is simulated for every location and
purity branch, assuming invariant-aware children, argument well-formedness
preservation, and closure-body simulations. This is not the full pass theorem. -/
theorem callsFuel_app_all_invariant_bodies_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (location : Option Nat) (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.app trace location sourceFn sourceArgs) initial = some (out, final))
    (notAllowed : ∀ address, location = some address →
      (sptLookup address final.1).isSome = true → address ∉ allowed) (distinct : (g.2.map Prod.fst).Nodup)
    (argsIH : ∀ targetArgs middle, callsListFuel fuel sourceArgs initial = some (targetArgs, middle) →
      ExprsSimFuelInvariant (C := C) (F := F) fuel g allowed sourceArgs targetArgs)
    (argsWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
      EvalWellFormedFuel fuel g allowed code (evaluate sourceArgs env state))
    (fnIH : ∀ targetFn middle, callsFuel fuel sourceFn middle = some (targetFn, final) →
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed sourceFn targetFn)
    (fnWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
      EvalWellFormedFuel fuel g allowed code (evaluate [sourceFn] env state))
    (bodyIH : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (sourceBody targetBody : ClosLang.Exp) (location : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code location sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed sourceBody targetBody)
    (bodyWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (body targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, body) → targetFns[index]? = some (arity, targetBody) →
      ∀ (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
        ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
        EvalWellFormedFuel fuel g allowed code (evaluate [body] env state)) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed (.app trace location sourceFn sourceArgs) out := by
  cases location with
  | none =>
    obtain ⟨targetFn, targetArgs, rfl, sim⟩ :=
      callsFuel_app_none_invariant_bodies_sim fuel g allowed trace sourceFn sourceArgs initial final out
        run distinct argsIH argsWf fnIH fnWf bodyIH bodyWf
    exact sim
  | some address =>
    cases found : sptLookup address final.1 with
    | none =>
      obtain ⟨targetFn, targetArgs, rfl, sim⟩ :=
        callsFuel_app_unknown_invariant_bodies_sim fuel g allowed trace address sourceFn sourceArgs initial final out
          run found distinct argsIH argsWf fnIH fnWf bodyIH bodyWf
      exact sim
    | some value =>
      have known : (sptLookup address final.1).isSome = true := by simp [found]
      cases purity : ClosLang.pure sourceFn with
      | false =>
        exact callsFuel_app_impure_invariant_bodies_sim fuel g allowed trace address sourceFn sourceArgs initial final out
          run known purity (notAllowed address rfl known) distinct argsIH argsWf fnIH fnWf bodyIH bodyWf
      | true =>
        exact callsFuel_app_pure_invariant_bodies_sim fuel g allowed trace address sourceFn sourceArgs initial final out
          run known purity (notAllowed address rfl known) distinct argsIH argsWf fnIH fnWf bodyIH bodyWf

end Flapjack.Compiler.Backend.ClosCall
