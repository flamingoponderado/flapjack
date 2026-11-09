module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateRaise

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section

/-! Conditional evaluation for direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- Each part of a conditional uses a subset of the conditional's free variables. -/
theorem envRelFuel_if_part {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {sourceEnv targetEnv : List ClosSem.Value}
    (trace : BackendCommon.Tra) (condition yes no : ClosLang.Exp)
    (part : ClosLang.Exp) (isPart : part = condition ∨ part = yes ∨ part = no)
    (related : EnvRelFuel fuel g allowed code sourceEnv targetEnv 0
      [(0, .ifThenElse trace condition yes no)]) :
    EnvRelFuel fuel g allowed code sourceEnv targetEnv 0 [(0, part)] := by
  apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
  have h := (envRelFuel_iff _ _ _ _ _ _ _ _).mp related
  unfold envRel at h ⊢
  by_cases same : sourceEnv.length = targetEnv.length
  · simpa [same] using h
  simp only [same, ↓reduceIte] at h ⊢
  intro x used
  apply h x
  simp only [List.mem_singleton, exists_eq_left, Nat.zero_add] at used ⊢
  simp only [ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp] at used ⊢
  rcases isPart with rfl | rfl | rfl <;> tauto

/-- Direct-call related values have the same Boolean observation. -/
theorem valueRelFuel_asBool {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {source target : ClosSem.Value}
    (related : ValueRelFuel fuel g allowed code source target) : asBool source = asBool target := by
  cases related with
  | block values =>
    cases values with
    | nil => rfl
    | cons head tail => simp [asBool]
  | number | word64 | byteVector | refPtr | closure | recclosure => rfl

/-- A conditional simulates when its condition and both branches simulate.
The compiler state is well formed, as required by the enclosing HOL theorem. -/
theorem exprSimFuel_if {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (sc sy sn tc ty tn : ClosLang.Exp)
    (distinct : (g.2.map Prod.fst).Nodup)
    (conditionIH : ExprSimFuel (C := C) (F := F) fuel g allowed sc tc)
    (yesIH : ExprSimFuel (C := C) (F := F) fuel g allowed sy ty)
    (noIH : ExprSimFuel (C := C) (F := F) fuel g allowed sn tn) :
    ExprSimFuel (C := C) (F := F) fuel g allowed
      (.ifThenElse trace sc sy sn) (.ifThenElse trace tc ty tn) := by
  intro sourceEnv targetEnv source target sourceResult sourceFinal run notType envs states
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
      conditionIH sourceEnv targetEnv source target condResult condFinal condRun condNotType conditionEnv states
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
          cases choice with
          | false =>
            have branchEnv := envRelFuel_if_part trace tc ty tn tn (Or.inr (Or.inr rfl)) envs
            have branchEnv' : EnvRelFuel fuel g allowed targetNext.code sourceEnv targetEnv 0 [(0, tn)] :=
              envRelFuel_mono branchEnv (stateExtends_refl g distinct) Set.Subset.rfl nextGrowth
            have branchRun : evaluate [sn] sourceEnv sourceNext = (sourceResult, sourceFinal) := by
              simpa [evaluate, condRun, fixClock, boolRun, sourceNext] using run
            obtain ⟨result, final, targetRun, resultRel, finalStates, growth⟩ :=
              noIH sourceEnv targetEnv sourceNext targetNext sourceResult sourceFinal branchRun notType branchEnv' nextStates
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
              yesIH sourceEnv targetEnv sourceNext targetNext sourceResult sourceFinal branchRun notType branchEnv' nextStates
            refine ⟨result, final, ?_, resultRel, finalStates, ?_⟩
            · simpa [evaluate, targetCondRun, fixClock, targetBool, targetNext] using targetRun
            · intro key item lookup
              exact growth key item (nextGrowth key item lookup)

end Flapjack.Compiler.Backend.ClosCall
