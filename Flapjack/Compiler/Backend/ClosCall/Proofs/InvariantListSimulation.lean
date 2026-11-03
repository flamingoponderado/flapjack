import Flapjack.Compiler.Backend.ClosCall.Proofs.InvariantSimulation

/-! Invariant-aware sequential expression-list simulation. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- Source-driven list simulation for well-formed source environments and states. -/
def ExprsSimFuelInvariant {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (sourceExps targetExps : List ClosLang.Exp) : Prop :=
  ∀ (sourceEnv targetEnv : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceResult : Result (List ClosSem.Value) ClosSem.Value)
    (sourceFinal : ClosSem.State (NumSet × C) F),
    evaluate sourceExps sourceEnv source = (sourceResult, sourceFinal) →
    sourceResult ≠ .err (.abort .typeError) →
    EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0 (targetExps.map (0, ·)) →
    ValuesWellFormedFuel fuel g allowed target.code sourceEnv →
    StateWellFormedFuel fuel g allowed target.code source →
    StateRelFuel fuel g allowed source target →
    ∃ targetResult targetFinal,
      evaluate targetExps targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel g allowed targetFinal.code))
        (ValueRelFuel fuel g allowed targetFinal.code) sourceResult targetResult ∧
      StateRelFuel fuel g allowed sourceFinal targetFinal ∧
      (∀ key value, target.code.lookup key = some value → targetFinal.code.lookup key = some value)

/-- Invariant-aware expression simulations compose in evaluation order when source head evaluations preserve well-formedness. This is Lean-side proof infrastructure. -/
theorem exprsSimFuelInvariant_of_forall₂ {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    {sourceExps targetExps : List ClosLang.Exp}
    (distinct : (g.2.map Prod.fst).Nodup)
    (sims : List.Forall₂ (fun source target =>
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed source target ∧
      ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
        ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
        EvalWellFormedFuel fuel g allowed code (evaluate [source] env state)) sourceExps targetExps) :
    ExprsSimFuelInvariant (C := C) (F := F) fuel g allowed sourceExps targetExps := by
  induction sims with
  | nil =>
    intro sourceEnv targetEnv source target sourceResult sourceFinal run _ _ _ _ states
    have sourceEq : sourceResult = .val [] ∧ sourceFinal = source := by
      simpa [evaluate] using run.symm
    obtain ⟨rfl, rfl⟩ := sourceEq
    exact ⟨.val [], target, by simp [evaluate], .nil, states, fun _ _ h => h⟩
  | @cons sourceHead targetHead sourceTail targetTail headIH tailSims tailIH =>
    intro sourceEnv targetEnv source target sourceResult sourceFinal run notType envs envWf stateWf states
    obtain ⟨headSim, headWf⟩ := headIH
    have headEnv : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0 [(0, targetHead)] := by
      apply envRelFuel_subset envs
      intro item member
      simp only [List.mem_singleton] at member
      subst item
      simp
    cases headRun : evaluate [sourceHead] sourceEnv source with
    | mk headResult headFinal =>
      have headNotType : headResult ≠ .err (.abort .typeError) := by
        intro bad
        subst headResult
        have outer := ClosProps.evaluate_cons_error sourceHead sourceTail sourceEnv source headFinal (.abort .typeError) headRun
        have : sourceResult = .err (.abort .typeError) := by rw [run] at outer; exact (Prod.mk.inj outer).1
        exact notType this
      obtain ⟨targetHeadResult, targetHeadFinal, targetHeadRun, headRel, headStates, headGrowth⟩ :=
        headSim sourceEnv targetEnv source target headResult headFinal headRun headNotType headEnv envWf stateWf states
      cases headResult with
      | err error =>
        cases targetHeadResult with
        | val values => simp [resultRel] at headRel
        | err targetError =>
          have sourceEq : sourceResult = .err error ∧ sourceFinal = headFinal := by
            have outer := ClosProps.evaluate_cons_error sourceHead sourceTail sourceEnv source headFinal error headRun
            rw [run] at outer
            exact Prod.mk.inj outer
          obtain ⟨rfl, rfl⟩ := sourceEq
          exact ⟨.err targetError, targetHeadFinal,
            ClosProps.evaluate_cons_error targetHead targetTail targetEnv target targetHeadFinal targetError targetHeadRun,
            headRel, headStates, headGrowth⟩
      | val values =>
        obtain ⟨value, rfl⟩ := evaluate_singleton_value sourceHead sourceEnv source headFinal values headRun
        cases targetHeadResult with
        | err error => simp [resultRel] at headRel
        | val targetValues =>
          obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value targetHead targetEnv target targetHeadFinal targetValues targetHeadRun
          have valuesRel : ValueRelFuel fuel g allowed targetHeadFinal.code value targetValue := by
            simpa [resultRel] using headRel
          have tailEnv : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0
              (targetTail.map (0, ·)) := by
            apply envRelFuel_subset envs
            intro item member
            simp only [List.map_cons, List.mem_cons]
            exact Or.inr member
          have tailEnv' := envRelFuel_mono tailEnv (stateExtends_refl g distinct) Set.Subset.rfl headGrowth
          have headStateWf : StateWellFormedFuel fuel g allowed targetHeadFinal.code headFinal := by
            have well := headWf target.code sourceEnv source envWf stateWf
            rw [headRun] at well
            exact stateWellFormedFuel_mono well.2 (stateExtends_refl g distinct) Set.Subset.rfl headGrowth
          have tailEnvWf := valuesWellFormedFuel_mono envWf (stateExtends_refl g distinct) Set.Subset.rfl headGrowth
          cases tailRun : evaluate sourceTail sourceEnv headFinal with
          | mk tailResult tailFinal =>
            have sourceOuter := ClosProps.evaluate_cons_value sourceHead sourceTail sourceEnv source headFinal value headRun
            rw [run, tailRun] at sourceOuter
            have tailNotType : tailResult ≠ .err (.abort .typeError) := by
              intro bad
              subst tailResult
              simp only at sourceOuter
              exact notType (Prod.mk.inj sourceOuter).1
            obtain ⟨targetTailResult, targetFinal, targetTailRun, tailRel, finalStates, tailGrowth⟩ :=
              tailIH sourceEnv targetEnv headFinal targetHeadFinal tailResult tailFinal tailRun tailNotType tailEnv' tailEnvWf headStateWf headStates
            have targetOuter := ClosProps.evaluate_cons_value targetHead targetTail targetEnv target targetHeadFinal targetValue targetHeadRun
            rw [targetTailRun] at targetOuter
            cases tailResult with
            | err error =>
              cases targetTailResult with
              | val vs => simp [resultRel] at tailRel
              | err targetError =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj sourceOuter
                exact ⟨.err targetError, targetFinal, targetOuter, tailRel, finalStates,
                  fun key item lookup => tailGrowth key item (headGrowth key item lookup)⟩
            | val tailValues =>
              cases targetTailResult with
              | err error => simp [resultRel] at tailRel
              | val targetTailValues =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj sourceOuter
                have grownValue := valueRelFuel_mono valuesRel (stateExtends_refl g distinct) Set.Subset.rfl tailGrowth
                exact ⟨.val (targetValue :: targetTailValues), targetFinal, targetOuter,
                  .cons grownValue tailRel, finalStates,
                  fun key item lookup => tailGrowth key item (headGrowth key item lookup)⟩

/-- A let body can use invariant simulation: the source binding evaluator
establishes well-formed values and state, and target code growth transports
those invariants to the body. This is conditional composition, not a full
pass theorem. -/
theorem exprSimFuelInvariant_let_with_invariant_bindings {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (sourceBindings targetBindings : List ClosLang.Exp)
    (sourceBody targetBody : ClosLang.Exp) (distinct : (g.2.map Prod.fst).Nodup)
    (bindingsIH : ExprsSimFuelInvariant (C := C) (F := F) fuel g allowed sourceBindings targetBindings)
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
      bindingsIH sourceEnv targetEnv source target bindingResult bindingFinal bindingRun bindingNotType bindingsEnv envWf stateWf states
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

/-- An actual list traversal composes invariant-aware expression simulations
and their source well-formedness preservation in evaluation order. -/
theorem callsListFuel_invariant_sim {C F : Type} (fuel relationFuel : Nat) (g : State) (allowed : Set Nat)
    (source target : List ClosLang.Exp) (initial final : State)
    (run : callsListFuel fuel source initial = some (target, final))
    (distinct : (g.2.map Prod.fst).Nodup)
    (exprIH : ∀ depth expression output before after,
      callsFuel depth expression before = some (output, after) →
      ExprSimFuelInvariant (C := C) (F := F) relationFuel g allowed expression output ∧
      ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
        ValuesWellFormedFuel relationFuel g allowed code env → StateWellFormedFuel relationFuel g allowed code state →
        EvalWellFormedFuel relationFuel g allowed code (evaluate [expression] env state)) :
    ExprsSimFuelInvariant (C := C) (F := F) relationFuel g allowed source target := by
  apply exprsSimFuelInvariant_of_forall₂ relationFuel g allowed distinct
  induction fuel generalizing source target initial final with
  | zero =>
    cases source with
    | nil => simp [callsListFuel] at run; obtain ⟨rfl, _⟩ := run; exact .nil
    | cons e es => simp [callsListFuel] at run
  | succ fuel ih =>
    cases source with
    | nil => simp [callsListFuel] at run; obtain ⟨rfl, _⟩ := run; exact .nil
    | cons e es =>
      simp only [callsListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨e', middle⟩, headRun, ⟨es', next⟩, tailRun, rfl, rfl⟩ := run
      exact .cons (exprIH fuel e e' initial middle headRun) (ih es es' middle _ tailRun)

/-- The executed let traversal can use invariant-aware simulations for both
its binding list and body, given binding evaluation well-formedness. -/
theorem callsFuel_let_invariant_bindings_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (bindings : List ClosLang.Exp) (body : ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.let trace bindings body) initial = some (out, final))
    (distinct : (g.2.map Prod.fst).Nodup)
    (bindingsIH : ∀ target middle, callsListFuel fuel bindings initial = some (target, middle) →
      ExprsSimFuelInvariant (C := C) (F := F) fuel g allowed bindings target)
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
  exact exprSimFuelInvariant_let_with_invariant_bindings fuel g allowed trace bindings targetBindings
    body targetBody distinct (bindingsIH targetBindings middle bindingsRun) bindingsWf (bodyIH targetBody middle bodyRun)

end Flapjack.Compiler.Backend.ClosCall
