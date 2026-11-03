import Flapjack.Compiler.Backend.ClosCall.Proofs.InvariantBodyImpureApplication

/-! Invariant-aware simulation through closure-language control flow. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- Matching ticks simulate by the induction hypothesis for their bodies. -/
theorem exprSimFuelInvariant_tick {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (sourceBody targetBody : ClosLang.Exp)
    (bodyIH : ExprSimFuelInvariant (C := C) (F := F) fuel g allowed sourceBody targetBody) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed (.tick trace sourceBody) (.tick trace targetBody) := by
  intro sourceEnv targetEnv source target sourceResult sourceFinal run notType envs envWf sourceWf states
  have clocks := states.2.1
  by_cases zero : source.clock = 0
  · have targetZero : target.clock = 0 := by omega
    have sourceEq : sourceResult = .err (.abort .timeoutError) ∧ sourceFinal = source := by
      simpa [evaluate, zero] using run.symm
    obtain ⟨rfl, rfl⟩ := sourceEq
    refine ⟨.err (.abort .timeoutError), target, ?_, ?_, states, fun _ _ h => h⟩
    · simp [evaluate, targetZero]
    · rfl
  · have targetNonzero : target.clock ≠ 0 := by omega
    have bodyRun : evaluate [sourceBody] sourceEnv (decClock 1 source) = (sourceResult, sourceFinal) := by
      simpa [evaluate, zero] using run
    have bodyEnv : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0 [(0, targetBody)] := by
      apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
      have h := (envRelFuel_iff fuel g allowed target.code sourceEnv targetEnv 0
        [(0, .tick trace targetBody)]).mp envs
      simpa [envRel, ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp] using h
    obtain ⟨targetResult, targetFinal, targetRun, results, finalStates, codeGrowth⟩ :=
      bodyIH sourceEnv targetEnv (decClock 1 source) (decClock 1 target)
        sourceResult sourceFinal bodyRun notType bodyEnv envWf (stateWellFormedFuel_clock sourceWf _) (stateRelFuel_decClock states 1)
    refine ⟨targetResult, targetFinal, ?_, results, finalStates, codeGrowth⟩
    simpa [evaluate, targetNonzero] using targetRun

/-- Matching raises simulate when their bodies simulate. -/
theorem exprSimFuelInvariant_raise {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (sourceBody targetBody : ClosLang.Exp)
    (bodyIH : ExprSimFuelInvariant (C := C) (F := F) fuel g allowed sourceBody targetBody) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed (.raise trace sourceBody) (.raise trace targetBody) := by
  intro sourceEnv targetEnv source target sourceResult sourceFinal run notType envs envWf sourceWf states
  have bodyEnv : EnvRelFuel fuel g allowed target.code sourceEnv targetEnv 0 [(0, targetBody)] := by
    apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
    have h := (envRelFuel_iff fuel g allowed target.code sourceEnv targetEnv 0
      [(0, .raise trace targetBody)]).mp envs
    simpa [envRel, ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp] using h
  cases bodyRun : evaluate [sourceBody] sourceEnv source with
  | mk bodyResult bodyFinal =>
    have bodyNotType : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      have : sourceResult = .err (.abort .typeError) := by
        simpa [evaluate, bodyRun] using congrArg Prod.fst run.symm
      exact notType this
    obtain ⟨targetResult, targetFinal, targetRun, results, finalStates, codeGrowth⟩ :=
      bodyIH sourceEnv targetEnv source target bodyResult bodyFinal bodyRun bodyNotType bodyEnv envWf sourceWf states
    cases bodyResult with
    | err error =>
      cases targetResult with
      | val values => simp [resultRel] at results
      | err targetError =>
        have sourceEq : sourceResult = .err error ∧ sourceFinal = bodyFinal := by
          simpa [evaluate, bodyRun] using run.symm
        obtain ⟨rfl, rfl⟩ := sourceEq
        refine ⟨.err targetError, targetFinal, ?_, results, finalStates, codeGrowth⟩
        simp [evaluate, targetRun]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value sourceBody sourceEnv source bodyFinal values bodyRun
      cases targetResult with
      | err error => simp [resultRel] at results
      | val targetValues =>
        obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value targetBody targetEnv target targetFinal targetValues targetRun
        have sourceEq : sourceResult = .err (.raise value) ∧ sourceFinal = bodyFinal := by
          simpa [evaluate, bodyRun] using run.symm
        obtain ⟨rfl, rfl⟩ := sourceEq
        have valuesRel : ValueRelFuel fuel g allowed targetFinal.code value targetValue := by
          simpa [resultRel] using results
        refine ⟨.err (.raise targetValue), targetFinal, ?_, ?_, finalStates, codeGrowth⟩
        · simp [evaluate, targetRun]
        · exact valuesRel

/-- A conditional simulates when its condition and both branches simulate.
The compiler state is well formed, as required by the enclosing HOL theorem. -/
theorem exprSimFuelInvariant_if {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (sc sy sn tc ty tn : ClosLang.Exp)
    (distinct : (g.2.map Prod.fst).Nodup)
    (conditionIH : ExprSimFuelInvariant (C := C) (F := F) fuel g allowed sc tc)
    (conditionWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
      EvalWellFormedFuel fuel g allowed code (evaluate [sc] env state))
    (yesIH : ExprSimFuelInvariant (C := C) (F := F) fuel g allowed sy ty)
    (noIH : ExprSimFuelInvariant (C := C) (F := F) fuel g allowed sn tn) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed
      (.ifThenElse trace sc sy sn) (.ifThenElse trace tc ty tn) := by
  intro sourceEnv targetEnv source target sourceResult sourceFinal run notType envs envWf sourceWf states
  have conditionEnv := envRelFuel_if_part trace tc ty tn tc (Or.inl rfl) envs
  cases condRun : evaluate [sc] sourceEnv source with
  | mk condResult condFinal =>
    have condNotType : condResult ≠ .err (.abort .typeError) := by
      intro bad
      subst condResult
      have : sourceResult = .err (.abort .typeError) := by
        simpa [evaluate, condRun, fixClock] using congrArg Prod.fst run.symm
      exact notType this
    obtain ⟨targetCondResult, targetCondFinal, targetCondRun, condRel, condStates, condGrowth⟩ :=
      conditionIH sourceEnv targetEnv source target condResult condFinal condRun condNotType conditionEnv envWf sourceWf states
    cases condResult with
    | err error =>
      cases targetCondResult with
      | val values => simp [resultRel] at condRel
      | err targetError =>
        have sourceEq : sourceResult = .err error ∧
            sourceFinal = (fixClock source ((), condFinal)).2 := by
          simpa [evaluate, condRun, fixClock] using run.symm
        obtain ⟨rfl, rfl⟩ := sourceEq
        refine ⟨.err targetError, (fixClock target ((), targetCondFinal)).2, ?_,
          condRel, stateRelFuel_fixClock source target () () states.2.1 condStates,
          condGrowth⟩
        simp [evaluate, targetCondRun, fixClock]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value sc sourceEnv source condFinal values condRun
      cases targetCondResult with
      | err error => simp [resultRel] at condRel
      | val targetValues =>
        obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value tc targetEnv target targetCondFinal targetValues targetCondRun
        have valueRel : ValueRelFuel fuel g allowed targetCondFinal.code value targetValue := by
          simpa [resultRel] using condRel
        have boolEq := valueRelFuel_asBool valueRel
        cases boolRun : asBool value with
        | none =>
          have : sourceResult = .err (.abort .typeError) := by
            simpa [evaluate, condRun, fixClock, boolRun] using congrArg Prod.fst run.symm
          exact False.elim (notType this)
        | some choice =>
          have targetBool : asBool targetValue = some choice := boolEq.symm.trans boolRun
          let sourceNext := (fixClock source ((), condFinal)).2
          let targetNext := (fixClock target ((), targetCondFinal)).2
          have nextStates : StateRelFuel fuel g allowed sourceNext targetNext :=
            stateRelFuel_fixClock source target () () states.2.1 condStates
          have nextGrowth : ∀ key item, target.code.lookup key = some item →
              targetNext.code.lookup key = some item := condGrowth
          have branchEnvWf := valuesWellFormedFuel_mono envWf (stateExtends_refl g distinct) Set.Subset.rfl nextGrowth
          have branchStateWf : StateWellFormedFuel fuel g allowed targetNext.code sourceNext := by
            have well := conditionWf target.code sourceEnv source envWf sourceWf
            rw [condRun] at well
            apply stateWellFormedFuel_mono _ (stateExtends_refl g distinct) Set.Subset.rfl nextGrowth
            simpa [sourceNext, fixClock] using stateWellFormedFuel_clock well.2 (min source.clock condFinal.clock)
          cases choice with
          | false =>
            have branchEnv := envRelFuel_if_part trace tc ty tn tn (Or.inr (Or.inr rfl)) envs
            have branchEnv' : EnvRelFuel fuel g allowed targetNext.code sourceEnv targetEnv 0 [(0, tn)] :=
              envRelFuel_mono branchEnv (stateExtends_refl g distinct) Set.Subset.rfl nextGrowth
            have branchRun : evaluate [sn] sourceEnv sourceNext = (sourceResult, sourceFinal) := by
              simpa [evaluate, condRun, fixClock, boolRun, sourceNext] using run
            obtain ⟨result, final, targetRun, resultRel, finalStates, growth⟩ :=
              noIH sourceEnv targetEnv sourceNext targetNext sourceResult sourceFinal branchRun notType branchEnv' branchEnvWf branchStateWf nextStates
            refine ⟨result, final, ?_, resultRel, finalStates, ?_⟩
            · simpa [evaluate, targetCondRun, fixClock, targetBool, targetNext] using targetRun
            · intro key item lookup
              exact growth key item (nextGrowth key item lookup)
          | true =>
            have branchEnv := envRelFuel_if_part trace tc ty tn ty (Or.inr (Or.inl rfl)) envs
            have branchEnv' : EnvRelFuel fuel g allowed targetNext.code sourceEnv targetEnv 0 [(0, ty)] :=
              envRelFuel_mono branchEnv (stateExtends_refl g distinct) Set.Subset.rfl nextGrowth
            have branchRun : evaluate [sy] sourceEnv sourceNext = (sourceResult, sourceFinal) := by
              simpa [evaluate, condRun, fixClock, boolRun, sourceNext] using run
            obtain ⟨result, final, targetRun, resultRel, finalStates, growth⟩ :=
              yesIH sourceEnv targetEnv sourceNext targetNext sourceResult sourceFinal branchRun notType branchEnv' branchEnvWf branchStateWf nextStates
            refine ⟨result, final, ?_, resultRel, finalStates, ?_⟩
            · simpa [evaluate, targetCondRun, fixClock, targetBool, targetNext] using targetRun
            · intro key item lookup
              exact growth key item (nextGrowth key item lookup)

/-- Matching handlers simulate protected evaluation and, on a raised value,
continue with related payloads in their extended environments. -/
theorem exprSimFuelInvariant_handle {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (sb sh tb th : ClosLang.Exp)
    (distinct : (g.2.map Prod.fst).Nodup)
    (bodyIH : ExprSimFuelInvariant (C := C) (F := F) fuel g allowed sb tb)
    (bodyWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
      EvalWellFormedFuel fuel g allowed code (evaluate [sb] env state))
    (handlerIH : ExprSimFuelInvariant (C := C) (F := F) fuel g allowed sh th) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed (.handle trace sb sh) (.handle trace tb th) := by
  intro sourceEnv targetEnv source target sourceResult sourceFinal run notType envs envWf sourceWf states
  have bodyEnv := envRelFuel_handle_body trace tb th envs
  cases bodyRun : evaluate [sb] sourceEnv source with
  | mk bodyResult bodyFinal =>
    have bodyNotType : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      have : sourceResult = .err (.abort .typeError) := by
        simpa [evaluate, bodyRun, fixClock] using congrArg Prod.fst run.symm
      exact notType this
    obtain ⟨targetBodyResult, targetBodyFinal, targetBodyRun, bodyRel, bodyStates, bodyGrowth⟩ :=
      bodyIH sourceEnv targetEnv source target bodyResult bodyFinal bodyRun bodyNotType bodyEnv envWf sourceWf states
    let sourceNext := (fixClock source ((), bodyFinal)).2
    let targetNext := (fixClock target ((), targetBodyFinal)).2
    have nextStates : StateRelFuel fuel g allowed sourceNext targetNext :=
      stateRelFuel_fixClock source target () () states.2.1 bodyStates
    have nextGrowth : ∀ key item, target.code.lookup key = some item →
        targetNext.code.lookup key = some item := bodyGrowth
    cases bodyResult with
    | val sourceValues =>
      cases targetBodyResult with
      | err error => simp [resultRel] at bodyRel
      | val targetValues =>
        have sourceEq : sourceResult = .val sourceValues ∧ sourceFinal = sourceNext := by
          simpa [evaluate, bodyRun, fixClock, sourceNext] using run.symm
        obtain ⟨rfl, rfl⟩ := sourceEq
        refine ⟨.val targetValues, targetNext, ?_, bodyRel, nextStates, nextGrowth⟩
        simp [evaluate, targetBodyRun, fixClock, targetNext]
    | err sourceError =>
      cases targetBodyResult with
      | val values => simp [resultRel] at bodyRel
      | err targetError =>
        cases sourceError with
        | abort sourceAbort =>
          cases targetError with
          | raise value => simp [resultRel, excRel] at bodyRel
          | abort targetAbort =>
            have sourceEq : sourceResult = .err (.abort sourceAbort) ∧ sourceFinal = sourceNext := by
              simpa [evaluate, bodyRun, fixClock, sourceNext] using run.symm
            obtain ⟨rfl, rfl⟩ := sourceEq
            refine ⟨.err (.abort targetAbort), targetNext, ?_, bodyRel, nextStates, nextGrowth⟩
            simp [evaluate, targetBodyRun, fixClock, targetNext]
        | raise sourceValue =>
          cases targetError with
          | abort error => simp [resultRel, excRel] at bodyRel
          | raise targetValue =>
            have payload : ValueRelFuel fuel g allowed targetNext.code sourceValue targetValue := bodyRel
            have grownEnv : EnvRelFuel fuel g allowed targetNext.code sourceEnv targetEnv 0
                [(0, .handle trace tb th)] :=
              envRelFuel_mono envs (stateExtends_refl g distinct) Set.Subset.rfl nextGrowth
            have handlerEnv := envRelFuel_handle_enter trace tb th grownEnv payload
            have sourceBodyWf := bodyWf target.code sourceEnv source envWf sourceWf
            rw [bodyRun] at sourceBodyWf
            have payloadWf : ValueWellFormedFuel fuel g allowed targetNext.code sourceValue :=
              valueWellFormedFuel_mono sourceBodyWf.1 (stateExtends_refl g distinct) Set.Subset.rfl nextGrowth
            have outerWf := valuesWellFormedFuel_mono envWf (stateExtends_refl g distinct) Set.Subset.rfl nextGrowth
            have handlerStateWf : StateWellFormedFuel fuel g allowed targetNext.code sourceNext := by
              apply stateWellFormedFuel_mono _ (stateExtends_refl g distinct) Set.Subset.rfl nextGrowth
              simpa [sourceNext, fixClock] using stateWellFormedFuel_clock sourceBodyWf.2 (min source.clock bodyFinal.clock)
            have handlerRun : evaluate [sh] (sourceValue :: sourceEnv) sourceNext = (sourceResult, sourceFinal) := by
              simpa [evaluate, bodyRun, fixClock, sourceNext] using run
            obtain ⟨result, final, targetRun, results, finalStates, growth⟩ :=
              handlerIH _ _ sourceNext targetNext sourceResult sourceFinal handlerRun notType handlerEnv (.cons payloadWf outerWf) handlerStateWf nextStates
            refine ⟨result, final, ?_, results, finalStates, ?_⟩
            · simpa [evaluate, targetBodyRun, fixClock, targetNext] using targetRun
            · intro key item lookup
              exact growth key item (nextGrowth key item lookup)

/-- The variable traversal case satisfies the fuel-aware evaluation relation.
This Lean-side case is not the complete HOL simulation theorem. -/
theorem callsFuel_var_invariant_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (index : Nat) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.var trace index) initial = some (out, final)) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed (.var trace index) out := by
  simp [callsFuel] at run
  obtain ⟨rfl, rfl⟩ := run
  exact exprSimFuel_to_invariant (exprSimFuel_var fuel g allowed trace index)

/-- The tick traversal case composes the simulation of its actual child output.
This Lean-side case is not the complete HOL simulation theorem. -/
theorem callsFuel_tick_invariant_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (body : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.tick trace body) initial = some (out, final))
    (bodyIH : ∀ target, callsFuel fuel body initial = some (target, final) →
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed body target) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed (.tick trace body) out := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨target, next⟩, bodyRun, rfl, rfl⟩ := run
  exact exprSimFuelInvariant_tick fuel g allowed trace body target (bodyIH target bodyRun)

/-- The raise traversal case composes the simulation of its actual child output.
This Lean-side case is not the complete HOL simulation theorem. -/
theorem callsFuel_raise_invariant_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (body : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.raise trace body) initial = some (out, final))
    (bodyIH : ∀ target, callsFuel fuel body initial = some (target, final) →
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed body target) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed (.raise trace body) out := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨target, next⟩, bodyRun, rfl, rfl⟩ := run
  exact exprSimFuelInvariant_raise fuel g allowed trace body target (bodyIH target bodyRun)

/-- The handler traversal case composes its two actual child simulations.
This Lean-side case is not the complete HOL simulation theorem. -/
theorem callsFuel_handle_invariant_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (body handler : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.handle trace body handler) initial = some (out, final))
    (distinct : (g.2.map Prod.fst).Nodup)
    (bodyIH : ∀ target middle, callsFuel fuel body initial = some (target, middle) →
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed body target)
    (bodyWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
      EvalWellFormedFuel fuel g allowed code (evaluate [body] env state))
    (handlerIH : ∀ target middle, callsFuel fuel handler middle = some (target, final) →
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed handler target) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed (.handle trace body handler) out := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetBody, middle⟩, bodyRun, ⟨targetHandler, next⟩, handlerRun, rfl, rfl⟩ := run
  exact exprSimFuelInvariant_handle fuel g allowed trace body handler targetBody targetHandler distinct
    (bodyIH targetBody middle bodyRun) bodyWf (handlerIH targetHandler middle handlerRun)

/-- The conditional traversal case composes its three actual child simulations.
This Lean-side case is not the complete HOL simulation theorem. -/
theorem callsFuel_if_invariant_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (condition yes no : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.ifThenElse trace condition yes no) initial = some (out, final))
    (distinct : (g.2.map Prod.fst).Nodup)
    (conditionIH : ∀ target middle, callsFuel fuel condition initial = some (target, middle) →
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed condition target)
    (conditionWf : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code state →
      EvalWellFormedFuel fuel g allowed code (evaluate [condition] env state))
    (yesIH : ∀ target before after, callsFuel fuel yes before = some (target, after) →
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed yes target)
    (noIH : ∀ target middle, callsFuel fuel no middle = some (target, final) →
      ExprSimFuelInvariant (C := C) (F := F) fuel g allowed no target) :
    ExprSimFuelInvariant (C := C) (F := F) fuel g allowed (.ifThenElse trace condition yes no) out := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetCondition, middle1⟩, conditionRun, ⟨targetYes, middle2⟩, yesRun,
    ⟨targetNo, next⟩, noRun, rfl, rfl⟩ := run
  exact exprSimFuelInvariant_if fuel g allowed trace condition yes no targetCondition targetYes targetNo distinct
    (conditionIH targetCondition middle1 conditionRun) conditionWf (yesIH targetYes middle1 middle2 yesRun)
    (noIH targetNo middle2 noRun)

end Flapjack.Compiler.Backend.ClosCall
