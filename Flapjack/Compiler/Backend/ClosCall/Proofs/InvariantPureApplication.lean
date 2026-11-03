import Flapjack.Compiler.Backend.ClosCall.Proofs.InvariantListSimulation

/-! Pure direct-call simulation with invariant-aware subexpressions. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- A pure source function has a related target value when its simulation
requires well-formed source environment and state. The target environment is
constructed from the source invariant. This is Lean-side infrastructure. -/
theorem pure_function_valueRelFuel_invariant {C F : Type}
    (fuel : Nat) (g : State) (allowed : Set Nat)
    (sourceFn targetFn : ClosLang.Exp) (sourceEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceValue : ClosSem.Value)
    (sourceRun : evaluate [sourceFn] sourceEnv source = (.val [sourceValue], source))
    (targetPure : ClosLang.pure targetFn = true)
    (wf : ValuesWellFormedFuel fuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel fuel g allowed target.code source)
    (states : StateRelFuel fuel g allowed source target)
    (fnIH : ExprSimFuelInvariant (C := C) (F := F) fuel g allowed sourceFn targetFn) :
    ∃ targetValue, ValueRelFuel fuel g allowed target.code sourceValue targetValue := by
  obtain ⟨targetEnv, _, envs⟩ := envRelFuel_exists_of_wellFormed fuel g allowed target.code sourceEnv wf
  obtain ⟨targetResult, targetFinal, targetRun, results, _, _⟩ :=
    fnIH sourceEnv targetEnv source target (.val [sourceValue]) source sourceRun (by simp)
      (envs 0 [(0, targetFn)]) wf sourceWf states
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

/-- Source simulation for the pure known-location case, assuming the source
environment is well formed and the recursive simulations hold. The explicit
environment invariant is needed because the optimized expression omits the
function's free variables. Argument and function simulations may themselves
require well-formedness; argument evaluation must preserve it. This is not the complete growing-state HOL result. -/
theorem callsFuel_app_pure_invariant_children_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (address : Nat) (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.app trace (some address) sourceFn sourceArgs) initial = some (out, final))
    (known : (sptLookup address final.1).isSome = true) (pure : ClosLang.pure sourceFn = true)
    (notAllowed : address ∉ allowed) (distinct : (g.2.map Prod.fst).Nodup)
    (argsIH : ∀ targetArgs middle, callsListFuel fuel sourceArgs initial = some (targetArgs, middle) →
      ExprsSimFuelInvariant (C := C) (F := F) fuel g allowed sourceArgs targetArgs)
    (argsWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
      EvalWellFormedFuel fuel g allowed code (evaluate sourceArgs env state))
    (fnIH : ∀ targetFn middle, callsFuel fuel sourceFn middle = some (targetFn, final) →
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed sourceFn targetFn)
    (bodyIH : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (sourceBody targetBody : ClosLang.Exp) (location : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code location sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      ExprSimFuel (C := C) (F := F) fuel g allowed sourceBody targetBody)
    (sourceEnv targetEnv : List ClosSem.Value) (source : ClosSem.State (NumSet × C) F)
    (target : ClosSem.State C F) (sourceResult : Result (List ClosSem.Value) ClosSem.Value)
    (sourceFinal : ClosSem.State (NumSet × C) F)
    (sourceRun : evaluate [.app trace (some address) sourceFn sourceArgs] sourceEnv source = (sourceResult, sourceFinal))
    (notType : sourceResult ≠ .err (.abort .typeError))
    (envs : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0 [(0, out)])
    (wf : ValuesWellFormedFuel fuel g allowed target.code sourceEnv)
    (sourceWf : StateWellFormedFuel fuel g allowed target.code source)
    (states : StateRelFuel fuel g allowed source target) :
    ∃ targetResult targetFinal,
      evaluate [out] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel g allowed targetFinal.code))
        (ValueRelFuel fuel g allowed targetFinal.code) sourceResult targetResult ∧
      StateRelFuel fuel g allowed sourceFinal targetFinal ∧
      (∀ key value, target.code.lookup key = some value → targetFinal.code.lookup key = some value) := by
  obtain ⟨targetArgs, targetFn, middle, argsTraversal, fnTraversal, targetPure, outEq⟩ :=
    callsFuel_app_pure_shape fuel trace address sourceFn sourceArgs initial final out run known pure
  have argsEnv : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0 (targetArgs.map (0, ·)) := by
    apply envRelFuel_call_args trace targetArgs.length (address + 1) targetArgs
    simpa [outEq] using envs
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
          sourceArgsRun argsNotType argsEnv wf sourceWf states
      cases argsResult with
      | err error =>
        cases targetArgsResult with
        | val values => simp [resultRel] at argsRel
        | err targetError =>
          have sourceEq : sourceResult = .err error ∧ sourceFinal = argsFinal := by
            simpa [sourceArgsRun] using sourceRun.symm
          obtain ⟨rfl, rfl⟩ := sourceEq
          refine ⟨.err targetError, targetArgsFinal, ?_, argsRel, argsStates, argsGrowth⟩
          rw [outEq, evaluate, fixClock_evaluate, targetArgsRun]
      | val sourceValues =>
        cases targetArgsResult with
        | err error => simp [resultRel] at argsRel
        | val targetValues =>
          have valuesRel : List.Forall₂ (ValueRelFuel fuel g allowed targetArgsFinal.code) sourceValues targetValues := argsRel
          cases sourceFnRun : evaluate [sourceFn] sourceEnv argsFinal with
          | mk fnResult fnFinal =>
            have fnNotType : fnResult ≠ .err (.abort .typeError) := by
              intro bad
              subst fnResult
              have : sourceResult = .err (.abort .typeError) := by
                simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using congrArg Prod.fst sourceRun.symm
              exact notType this
            have sourcePure : ClosLang.pureList [sourceFn] = true := by simp [ClosLang.pureList, pure]
            obtain ⟨fnValues, resultEq, finalEq⟩ :=
              ClosProps.evaluate_pure [sourceFn] sourceEnv argsFinal fnFinal fnResult sourcePure sourceFnRun fnNotType
            subst fnResult
            subst fnFinal
            obtain ⟨fnValue, rfl⟩ := evaluate_singleton_value sourceFn sourceEnv argsFinal argsFinal fnValues sourceFnRun
            have wf' : ValuesWellFormedFuel fuel g allowed targetArgsFinal.code sourceEnv :=
              valuesWellFormedFuel_mono wf (stateExtends_refl g distinct) Set.Subset.rfl argsGrowth
            have argsStateWf : StateWellFormedFuel fuel g allowed targetArgsFinal.code argsFinal := by
              have well := argsWf target.code sourceEnv source wf sourceWf
              rw [sourceArgsRun] at well
              exact stateWellFormedFuel_mono well.2 (stateExtends_refl g distinct) Set.Subset.rfl argsGrowth
            obtain ⟨targetFnValue, functionRel⟩ := pure_function_valueRelFuel_invariant fuel g allowed sourceFn targetFn
              sourceEnv argsFinal targetArgsFinal fnValue sourceFnRun targetPure wf' argsStateWf argsStates
              (fnIH targetFn middle fnTraversal)
            have appRun : evaluateApp (some address) fnValue sourceValues argsFinal = (sourceResult, sourceFinal) := by
              simpa [sourceArgsRun, sourceFnRun, fixClock_evaluate] using sourceRun
            have nonempty : sourceValues ≠ [] := by
              have len := (evaluate_length (C := NumSet × C) (F := F)).1 (first :: rest) sourceEnv source argsFinal sourceValues sourceArgsRun
              intro empty
              simp [empty] at len
            obtain ⟨sourceBody, sourceBodyEnv, sourceRest, sourceClosure⟩ :=
              evaluateApp_known_full address fnValue sourceValues argsFinal sourceFinal sourceResult nonempty appRun notType
            have sourceClosure' : destClosure targetArgsFinal.maxApp (some address) fnValue sourceValues =
                some (.fullApp sourceBody sourceBodyEnv sourceRest) := by
              simpa [← argsStates.2.2.1] using sourceClosure
            obtain ⟨stubTrace, stubEnv, convertedBody, _, _, _, _, _, _, targetClosure, _, found, _, _, _, _, _⟩ :=
              destClosure_known_direct fuel g allowed targetArgsFinal.code targetArgsFinal.maxApp address fnValue targetFnValue
                sourceValues targetValues sourceBody sourceBodyEnv sourceRest sourceClosure' functionRel valuesRel notAllowed
            have code : targetArgsFinal.code.lookup (address + 1) = some (targetValues.length, convertedBody) := by
              unfold findCode at found
              cases h : targetArgsFinal.code.lookup (address + 1) with
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
            have targetClosure' : destClosure targetArgsFinal.maxApp (some address) targetFnValue targetValues =
                some (.fullApp (.call stubTrace 0 (address + 1) (ClosCall.variables stubTrace targetValues.length)) stubEnv []) := by
              simpa [valuesRel.length_eq] using targetClosure
            have targetEq := evaluate_pure_rewrite_eq_known_app trace stubTrace (address + 1) address targetArgs
              targetEnv targetValues targetFnValue target targetArgsFinal stubEnv convertedBody targetArgsRun code targetClosure'
            obtain ⟨result, finalTarget, targetRun, results, finalStates, growth⟩ :=
              appSimFuel_of_bodies fuel g allowed (some address) distinct bodyIH fnValue targetFnValue sourceValues targetValues
                argsFinal targetArgsFinal sourceResult sourceFinal appRun notType functionRel valuesRel argsStates
            refine ⟨result, finalTarget, ?_, results, finalStates, ?_⟩
            · simpa [outEq] using targetEq.trans targetRun
            · intro key item lookup
              exact growth key item (argsGrowth key item lookup)

/-- The pure known-call traversal yields an invariant-aware simulation,
with invariant-aware argument and function induction hypotheses. -/
theorem callsFuel_app_pure_invariant_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (address : Nat) (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.app trace (some address) sourceFn sourceArgs) initial = some (out, final))
    (known : (sptLookup address final.1).isSome = true) (pure : ClosLang.pure sourceFn = true)
    (notAllowed : address ∉ allowed) (distinct : (g.2.map Prod.fst).Nodup)
    (argsIH : ∀ targetArgs middle, callsListFuel fuel sourceArgs initial = some (targetArgs, middle) →
      ExprsSimFuelInvariant (C := C) (F := F) fuel g allowed sourceArgs targetArgs)
    (argsWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
      EvalWellFormedFuel fuel g allowed code (evaluate sourceArgs env state))
    (fnIH : ∀ targetFn middle, callsFuel fuel sourceFn middle = some (targetFn, final) →
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed sourceFn targetFn)
    (bodyIH : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (sourceBody targetBody : ClosLang.Exp) (location : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code location sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      ExprSimFuel (C := C) (F := F) fuel g allowed sourceBody targetBody)
 :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed (.app trace (some address) sourceFn sourceArgs) out := by
  intro sourceEnv targetEnv source target result sourceFinal sourceRun notType envs envWf sourceWf states
  exact callsFuel_app_pure_invariant_children_sim fuel g allowed trace address sourceFn sourceArgs initial final out
    run known pure notAllowed distinct argsIH argsWf fnIH bodyIH sourceEnv targetEnv source target result sourceFinal
    sourceRun notType envs envWf sourceWf states

end Flapjack.Compiler.Backend.ClosCall
