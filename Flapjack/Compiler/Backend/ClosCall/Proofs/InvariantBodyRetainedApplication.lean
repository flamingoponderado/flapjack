import Flapjack.Compiler.Backend.ClosCall.Proofs.InvariantClosureApplication

/-! Retained application simulation with invariant-aware closure bodies. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- An application retained by the pass simulates under the source invariant when its argument list,
function expression, and selected closure bodies simulate. The separate
direct-call rewrite is not covered by this case. -/
theorem exprSimFuelInvariant_app_invariant_bodies {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (loc : Option Nat) (sourceFn targetFn : ClosLang.Exp)
    (sourceArgs targetArgs : List ClosLang.Exp) (length : sourceArgs.length = targetArgs.length)
    (distinct : (g.2.map Prod.fst).Nodup)
    (argsIH : ExprsSimFuelInvariant (C := C) (F := F) fuel g allowed sourceArgs targetArgs)
    (argsWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
      EvalWellFormedFuel fuel g allowed code (evaluate sourceArgs env state))
    (fnIH : ExprSimFuelInvariant (C := C) (F := F) fuel g allowed sourceFn targetFn)
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
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed
      (.app trace loc sourceFn sourceArgs) (.app trace loc targetFn targetArgs) := by
  intro sourceEnv targetEnv source target sourceResult sourceFinal run notType envs envWf sourceWf states
  obtain ⟨fnEnv, argsEnv⟩ := envRelFuel_app_parts trace loc targetFn targetArgs envs
  cases sourceArgs with
  | nil =>
    have bad : sourceResult = .err (.abort .typeError) := by
      simpa [evaluate] using congrArg Prod.fst run.symm
    exact False.elim (notType bad)
  | cons first rest =>
    have targetNonempty : targetArgs ≠ [] := by
      intro empty
      simp [empty] at length
    have targetNotEmpty : targetArgs.isEmpty = false := by
      cases targetArgs with
      | nil => exact False.elim (targetNonempty rfl)
      | cons head tail => rfl
    rw [evaluate] at run
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate] at run
    cases argsRun : evaluate (first :: rest) sourceEnv source with
    | mk argsResult argsFinal =>
      have argsNotType : argsResult ≠ .err (.abort .typeError) := by
        intro bad
        subst argsResult
        have : sourceResult = .err (.abort .typeError) := by
          simpa [argsRun] using congrArg Prod.fst run.symm
        exact notType this
      obtain ⟨targetArgsResult, targetArgsFinal, targetArgsRun, argsRel, argsStates, argsGrowth⟩ :=
        argsIH sourceEnv targetEnv source target argsResult argsFinal argsRun argsNotType argsEnv envWf sourceWf states
      cases argsResult with
      | err error =>
        cases targetArgsResult with
        | val values => simp [resultRel] at argsRel
        | err targetError =>
          have sourceEq : sourceResult = .err error ∧ sourceFinal = argsFinal := by
            simpa [argsRun] using run.symm
          obtain ⟨rfl, rfl⟩ := sourceEq
          refine ⟨.err targetError, targetArgsFinal, ?_, argsRel, argsStates, argsGrowth⟩
          rw [evaluate]
          simp only [targetNotEmpty, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate]
          rw [targetArgsRun]
      | val values =>
        cases targetArgsResult with
        | err error => simp [resultRel] at argsRel
        | val targetValues =>
          have valuesRel : List.Forall₂ (ValueRelFuel fuel g allowed targetArgsFinal.code) values targetValues := argsRel
          have fnEnv' : EnvRelFuel fuel g allowed targetArgsFinal.code sourceEnv targetEnv 0 [(0, targetFn)] :=
            envRelFuel_mono fnEnv (stateExtends_refl g distinct) Set.Subset.rfl argsGrowth
          have fnEnvWf := valuesWellFormedFuel_mono envWf (stateExtends_refl g distinct) Set.Subset.rfl argsGrowth
          have argsStateWf : StateWellFormedFuel fuel g allowed targetArgsFinal.code argsFinal := by
            have well := argsWf target.code sourceEnv source envWf sourceWf
            rw [argsRun] at well
            exact stateWellFormedFuel_mono well.2 (stateExtends_refl g distinct) Set.Subset.rfl argsGrowth
          cases fnRun : evaluate [sourceFn] sourceEnv argsFinal with
          | mk fnResult fnFinal =>
            have fnNotType : fnResult ≠ .err (.abort .typeError) := by
              intro bad
              subst fnResult
              have : sourceResult = .err (.abort .typeError) := by
                simpa [argsRun, fnRun, fixClock_evaluate] using congrArg Prod.fst run.symm
              exact notType this
            obtain ⟨targetFnResult, targetFnFinal, targetFnRun, fnRel, fnStates, fnGrowth⟩ :=
              fnIH sourceEnv targetEnv argsFinal targetArgsFinal fnResult fnFinal fnRun fnNotType fnEnv' fnEnvWf argsStateWf argsStates
            cases fnResult with
            | err error =>
              cases targetFnResult with
              | val vs => simp [resultRel] at fnRel
              | err targetError =>
                have sourceEq : sourceResult = .err error ∧ sourceFinal = fnFinal := by
                  simpa [argsRun, fnRun, fixClock_evaluate] using run.symm
                obtain ⟨rfl, rfl⟩ := sourceEq
                refine ⟨.err targetError, targetFnFinal, ?_, fnRel, fnStates, ?_⟩
                · rw [evaluate]
                  simp only [targetNotEmpty, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate]
                  rw [targetArgsRun, targetFnRun]
                · intro key item lookup
                  exact fnGrowth key item (argsGrowth key item lookup)
            | val fnValues =>
              obtain ⟨fnValue, rfl⟩ := evaluate_singleton_value sourceFn sourceEnv argsFinal fnFinal fnValues fnRun
              cases targetFnResult with
              | err error => simp [resultRel] at fnRel
              | val targetFnValues =>
                obtain ⟨targetFnValue, rfl⟩ :=
                  evaluate_singleton_value targetFn targetEnv targetArgsFinal targetFnFinal targetFnValues targetFnRun
                have functionRel : ValueRelFuel fuel g allowed targetFnFinal.code fnValue targetFnValue := by
                  simpa [resultRel] using fnRel
                have valuesRel' : List.Forall₂ (ValueRelFuel fuel g allowed targetFnFinal.code) values targetValues :=
                  List.Forall₂.imp (fun _ _ h => valueRelFuel_mono h (stateExtends_refl g distinct) Set.Subset.rfl fnGrowth) valuesRel
                have appRun : evaluateApp loc fnValue values fnFinal = (sourceResult, sourceFinal) := by
                  simpa [argsRun, fnRun, fixClock_evaluate] using run
                have argumentWf : ValuesWellFormedFuel fuel g allowed targetFnFinal.code values := by
                  have well := argsWf target.code sourceEnv source envWf sourceWf
                  rw [argsRun] at well
                  exact valuesWellFormedFuel_mono well.1 (stateExtends_refl g distinct) Set.Subset.rfl
                    (fun key item lookup => fnGrowth key item (argsGrowth key item lookup))
                have functionWf : ValueWellFormedFuel fuel g allowed targetFnFinal.code fnValue := by
                  have well := fnWf targetArgsFinal.code sourceEnv argsFinal fnEnvWf argsStateWf
                  rw [fnRun] at well
                  have valueWf : ValueWellFormedFuel fuel g allowed targetArgsFinal.code fnValue := by
                    cases well.1 with
                    | cons head tail => exact head
                  exact valueWellFormedFuel_mono valueWf (stateExtends_refl g distinct) Set.Subset.rfl fnGrowth
                have afterFunctionWf : StateWellFormedFuel fuel g allowed targetFnFinal.code fnFinal := by
                  have well := fnWf targetArgsFinal.code sourceEnv argsFinal fnEnvWf argsStateWf
                  rw [fnRun] at well
                  exact stateWellFormedFuel_mono well.2 (stateExtends_refl g distinct) Set.Subset.rfl fnGrowth
                obtain ⟨result, final, targetRun, results, finalStates, growth⟩ :=
                  appSimFuelInvariant_of_bodies fuel g allowed loc distinct bodyIH bodyWf fnValue targetFnValue values targetValues
                    fnFinal targetFnFinal sourceResult sourceFinal appRun notType functionRel valuesRel' functionWf argumentWf afterFunctionWf fnStates
                refine ⟨result, final, ?_, results, finalStates, ?_⟩
                · rw [evaluate]
                  simp only [targetNotEmpty, Bool.false_eq_true, ↓reduceIte, fixClock_evaluate]
                  rw [targetArgsRun, targetFnRun]
                  simpa using targetRun
                · intro key item lookup
                  exact growth key item (fnGrowth key item (argsGrowth key item lookup))

/-- A location-free application stays an application in the direct-call pass.
Successful sub-traversals and their induction hypotheses yield its evaluation
simulation; known-location rewrites are a separate case. -/
theorem callsFuel_app_none_invariant_bodies_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.app trace none sourceFn sourceArgs) initial = some (out, final))
    (distinct : (g.2.map Prod.fst).Nodup)
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
    ∃ targetFn targetArgs, out = .app trace none targetFn targetArgs ∧
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed (.app trace none sourceFn sourceArgs)
        (.app trace none targetFn targetArgs) := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetArgs, middle⟩, argsRun, ⟨targetFn, next⟩, fnRun, rfl, rfl⟩ := run
  have length := callsListFuel_length fuel sourceArgs initial middle targetArgs argsRun
  refine ⟨targetFn, targetArgs, rfl, ?_⟩
  exact exprSimFuelInvariant_app_invariant_bodies fuel g allowed trace none sourceFn targetFn sourceArgs targetArgs length.symm distinct
    (argsIH targetArgs middle argsRun) argsWf (fnIH targetFn middle fnRun) fnWf bodyIH bodyWf

/-- A location-annotated application also remains an application when its
location is absent from the pass state after visiting its arguments and
function. This is Lean-side case composition, not a standalone HOL theorem. -/
theorem callsFuel_app_unknown_invariant_bodies_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (loc : Nat) (sourceFn : ClosLang.Exp) (sourceArgs : List ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.app trace (some loc) sourceFn sourceArgs) initial = some (out, final))
    (unknown : sptLookup loc final.1 = none)
    (distinct : (g.2.map Prod.fst).Nodup)
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
    ∃ targetFn targetArgs, out = .app trace (some loc) targetFn targetArgs ∧
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed (.app trace (some loc) sourceFn sourceArgs)
        (.app trace (some loc) targetFn targetArgs) := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
  obtain ⟨⟨targetArgs, middle⟩, argsRun, ⟨targetFn, afterFn⟩, fnRun, rest⟩ := run
  by_cases found : (sptLookup loc afterFn.1).isSome
  · simp [found] at rest
    split at rest <;> simp_all
  · simp [found] at rest
    obtain ⟨rfl, rfl⟩ := rest
    have length := callsListFuel_length fuel sourceArgs initial middle targetArgs argsRun
    refine ⟨targetFn, targetArgs, rfl, ?_⟩
    exact exprSimFuelInvariant_app_invariant_bodies fuel g allowed trace (some loc) sourceFn targetFn sourceArgs targetArgs length.symm distinct
      (argsIH targetArgs middle argsRun) argsWf (fnIH targetFn middle fnRun) fnWf bodyIH bodyWf

end Flapjack.Compiler.Backend.ClosCall
