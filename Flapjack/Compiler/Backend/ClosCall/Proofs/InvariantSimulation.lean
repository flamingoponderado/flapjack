import Flapjack.Compiler.Backend.ClosCall.Proofs.ApplicationSimulation
import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateControlWellformed

/-! Simulations that carry source value and state well-formedness. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- A source-driven expression simulation whose source environment and state
are well formed. This Lean-side relation makes explicit the invariant needed
by the pure direct-call rewrite; it is not the full HOL simulation relation. -/
def ExprSimFuelInvariant {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (sourceExp targetExp : ClosLang.Exp) : Prop :=
  ∀ (sourceEnv targetEnv : List ClosSem.Value) (source : ClosSem.State (NumSet × C) F)
    (target : ClosSem.State C F) (sourceResult : Result (List ClosSem.Value) ClosSem.Value)
    (sourceFinal : ClosSem.State (NumSet × C) F),
    evaluate [sourceExp] sourceEnv source = (sourceResult, sourceFinal) →
    sourceResult ≠ .err (.abort .typeError) →
    EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0 [(0, targetExp)] →
    ValuesWellFormedFuel fuel g allowed target.code sourceEnv →
    StateWellFormedFuel fuel g allowed target.code source →
    StateRelFuel fuel g allowed source target →
    ∃ targetResult targetFinal,
      evaluate [targetExp] targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel g allowed targetFinal.code))
        (ValueRelFuel fuel g allowed targetFinal.code) sourceResult targetResult ∧
      StateRelFuel fuel g allowed sourceFinal targetFinal ∧
      (∀ key value, target.code.lookup key = some value → targetFinal.code.lookup key = some value)

/-- An unconditional fuel-aware simulation is also an invariant simulation. -/
theorem exprSimFuel_to_invariant {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {source target : ClosLang.Exp} (sim : ExprSimFuel (C := C) (F := F) fuel g allowed source target) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed source target := by
  intro sourceEnv targetEnv sourceState targetState result final run notType envs _ _ states
  exact sim sourceEnv targetEnv sourceState targetState result final run notType envs states

/-- All application traversal branches satisfy the invariant simulation when
their recursive simulations and known-location condition hold. -/
theorem callsFuel_app_invariant_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (location : Option Nat) (sourceFn : ClosLang.Exp)
    (sourceArgs : List ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.app trace location sourceFn sourceArgs) initial = some (out, final))
    (notAllowed : ∀ address, location = some address →
      (sptLookup address final.1).isSome = true → address ∉ allowed)
    (distinct : (g.2.map Prod.fst).Nodup)
    (argsIH : ∀ targetArgs middle, callsListFuel fuel sourceArgs initial = some (targetArgs, middle) →
      ExprsSimFuel (C := C) (F := F) fuel g allowed sourceArgs targetArgs)
    (fnIH : ∀ targetFn middle, callsFuel fuel sourceFn middle = some (targetFn, final) →
      ExprSimFuel (C := C) (F := F) fuel g allowed sourceFn targetFn)
    (bodyIH : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (sourceBody targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      ExprSimFuel (C := C) (F := F) fuel g allowed sourceBody targetBody) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed (.app trace location sourceFn sourceArgs) out := by
  intro sourceEnv targetEnv source target result sourceFinal sourceRun notType envs wf _ states
  exact callsFuel_app_sim fuel g allowed trace location sourceFn sourceArgs initial final out run notAllowed
    distinct argsIH fnIH bodyIH sourceEnv targetEnv source target result sourceFinal sourceRun notType envs wf states

/-- A let body can use invariant simulation: the source binding evaluator
establishes well-formed values and state, and target code growth transports
those invariants to the body. This is conditional composition, not a full
pass theorem. -/
theorem exprSimFuelInvariant_let {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (sourceBindings targetBindings : List ClosLang.Exp)
    (sourceBody targetBody : ClosLang.Exp) (distinct : (g.2.map Prod.fst).Nodup)
    (bindingsIH : ExprsSimFuel (C := C) (F := F) fuel g allowed sourceBindings targetBindings)
    (bindingsWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
      EvalWellFormedFuel fuel g allowed code (evaluate sourceBindings env state))
    (bodyIH : ExprSimFuelInvariant (C := C) (F := F) fuel g allowed sourceBody targetBody) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed
      (.let trace sourceBindings sourceBody) (.let trace targetBindings targetBody) := by
  intro sourceEnv targetEnv source target sourceResult sourceFinal run notType envs envWf stateWf states
  have bindingsEnv := envRelFuel_let_bindings trace targetBindings targetBody envs
  have bindingWf := bindingsWf target.code sourceEnv source envWf stateWf
  cases bindingRun : evaluate sourceBindings sourceEnv source with
  | mk bindingResult bindingFinal =>
    rw [bindingRun] at bindingWf
    have bindingNotType : bindingResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bindingResult
      have : sourceResult = .err (.abort .typeError) := by
        simpa [evaluate, bindingRun, fixClock] using congrArg Prod.fst run.symm
      exact notType this
    obtain ⟨targetBindingResult, targetBindingFinal, targetBindingRun, bindingRel, bindingStates, bindingGrowth⟩ :=
      bindingsIH sourceEnv targetEnv source target bindingResult bindingFinal bindingRun bindingNotType bindingsEnv states
    let sourceNext := (fixClock source ((), bindingFinal)).2
    let targetNext := (fixClock target ((), targetBindingFinal)).2
    have nextStates : StateRelFuel fuel g allowed sourceNext targetNext :=
      stateRelFuel_fixClock source target () () states.2.1 bindingStates
    have nextGrowth : ∀ key item, target.code.lookup key = some item →
        targetNext.code.lookup key = some item := bindingGrowth
    cases bindingResult with
    | err error =>
      cases targetBindingResult with
      | val values => simp [resultRel] at bindingRel
      | err targetError =>
        have sourceEq : sourceResult = .err error ∧ sourceFinal = sourceNext := by
          simpa [evaluate, bindingRun, fixClock, sourceNext] using run.symm
        obtain ⟨rfl, rfl⟩ := sourceEq
        refine ⟨.err targetError, targetNext, ?_, bindingRel, nextStates, nextGrowth⟩
        simp [evaluate, targetBindingRun, fixClock, targetNext]
    | val sourceValues =>
      cases targetBindingResult with
      | err error => simp [resultRel] at bindingRel
      | val targetValues =>
        have valueRel : List.Forall₂ (ValueRelFuel fuel g allowed targetNext.code) sourceValues targetValues := bindingRel
        have valuesLength : sourceValues.length = targetBindings.length := by
          have targetLength := (evaluate_length (C := C) (F := F)).1 targetBindings targetEnv target
            targetBindingFinal targetValues targetBindingRun
          exact valueRel.length_eq.trans targetLength
        have outerEnv := envRelFuel_let_body_outer trace targetBindings targetBody envs
        have outerEnv' := envRelFuel_mono outerEnv (stateExtends_refl g distinct) Set.Subset.rfl nextGrowth
        have bodyEnv : EnvRelFuel fuel g allowed targetNext.code (sourceValues ++ sourceEnv)
            (targetValues ++ targetEnv) 0 [(0, targetBody)] := by
          apply envRelFuel_prepend valueRel
          simpa [valuesLength] using outerEnv'
        have bodyEnvWf : ValuesWellFormedFuel fuel g allowed targetNext.code (sourceValues ++ sourceEnv) :=
          valuesWellFormedFuel_mono (valuesWellFormedFuel_append bindingWf.1 envWf)
            (stateExtends_refl g distinct) Set.Subset.rfl nextGrowth
        have bodyStateWf : StateWellFormedFuel fuel g allowed targetNext.code sourceNext := by
          apply stateWellFormedFuel_mono _ (stateExtends_refl g distinct) Set.Subset.rfl nextGrowth
          simpa [sourceNext, fixClock] using
            stateWellFormedFuel_clock bindingWf.2 (min source.clock bindingFinal.clock)
        have bodyRun : evaluate [sourceBody] (sourceValues ++ sourceEnv) sourceNext = (sourceResult, sourceFinal) := by
          simpa [evaluate, bindingRun, fixClock, sourceNext] using run
        obtain ⟨result, final, targetRun, results, finalStates, growth⟩ :=
          bodyIH _ _ sourceNext targetNext sourceResult sourceFinal bodyRun notType bodyEnv bodyEnvWf bodyStateWf nextStates
        refine ⟨result, final, ?_, results, finalStates, ?_⟩
        · simpa [evaluate, targetBindingRun, fixClock, targetNext] using targetRun
        · intro key item lookup
          exact growth key item (nextGrowth key item lookup)

/-- The actual let traversal composes an invariant body simulation with the
simulation and well-formedness preservation of its binding list. -/
theorem callsFuel_let_invariant_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (bindings : List ClosLang.Exp) (body : ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.let trace bindings body) initial = some (out, final))
    (distinct : (g.2.map Prod.fst).Nodup)
    (bindingsIH : ∀ target middle, callsListFuel fuel bindings initial = some (target, middle) →
      ExprsSimFuel (C := C) (F := F) fuel g allowed bindings target)
    (bindingsWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
      EvalWellFormedFuel fuel g allowed code (evaluate bindings env state))
    (bodyIH : ∀ target middle, callsFuel fuel body middle = some (target, final) →
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed body target) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed (.let trace bindings body) out := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetBindings, middle⟩, bindingsRun, ⟨targetBody, next⟩, bodyRun, rfl, rfl⟩ := run
  exact exprSimFuelInvariant_let fuel g allowed trace bindings targetBindings body targetBody distinct
    (bindingsIH targetBindings middle bindingsRun) bindingsWf (bodyIH targetBody middle bodyRun)

end Flapjack.Compiler.Backend.ClosCall
