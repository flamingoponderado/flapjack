module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.Pure
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength

@[expose] public section

/-! Purity of proof-side closure expression evaluation. -/
namespace Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

private theorem evaluatePureAux {C F : Type} (expressions : List ClosLang.Exp) (env : List Value)
    (source next : State C F) (result : Result (List Value) Value)
    (pure : ClosLang.pureList expressions = true)
    (run : evaluate expressions env source = (result, next))
    (notType : result ≠ .err (.abort .typeError)) :
    ∃ values, result = .val values ∧ next = source := by
  have all : ∀ weight expressions (env : List Value) (source next : State C F)
      (result : Result (List Value) Value), expsWeight expressions = weight →
      ClosLang.pureList expressions = true → evaluate expressions env source = (result, next) →
      result ≠ .err (.abort .typeError) → ∃ values, result = .val values ∧ next = source := by
    intro weight
    induction weight using Nat.strongRecOn with
    | ind weight ih =>
      intro expressions env source next result measure pure run notType
      have smaller : ∀ expressions (env : List Value) (source next : State C F)
          (result : Result (List Value) Value), expsWeight expressions < weight →
          ClosLang.pureList expressions = true → evaluate expressions env source = (result, next) →
          result ≠ .err (.abort .typeError) → ∃ values, result = .val values ∧ next = source := by
        intro expressions env source next result less
        exact ih (expsWeight expressions) less expressions env source next result rfl
      cases expressions with
      | nil =>
        simp [evaluate] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨[], rfl, rfl⟩
      | cons first rest =>
        cases rest with
        | cons second tail =>
          have pureParts : ClosLang.pureList [first] = true ∧ ClosLang.pureList (second :: tail) = true := by
            simpa [ClosLang.pureList] using pure
          rw [evaluate, fixClock_evaluate] at run
          cases firstRun : evaluate [first] env source with
          | mk firstResult middle =>
            have firstNotType : firstResult ≠ .err (.abort .typeError) := by
              intro bad
              subst firstResult
              rw [firstRun] at run
              cases run
              exact notType rfl
            have firstLess : expsWeight [first] < weight := by simp only [expsWeight] at measure ⊢; omega
            obtain ⟨firstValues, firstEq, middleEq⟩ :=
              smaller [first] env source middle firstResult firstLess pureParts.1 firstRun firstNotType
            subst firstResult
            subst middle
            rw [firstRun] at run
            cases restRun : evaluate (second :: tail) env source with
            | mk restResult last =>
              have restNotType : restResult ≠ .err (.abort .typeError) := by
                intro bad
                subst restResult
                rw [restRun] at run
                cases run
                exact notType rfl
              have restLess : expsWeight (second :: tail) < weight := by simp only [expsWeight] at measure ⊢; omega
              obtain ⟨restValues, restEq, lastEq⟩ :=
                smaller (second :: tail) env source last restResult restLess pureParts.2 restRun restNotType
              subst restResult
              subst last
              rw [restRun] at run
              cases run
              exact ⟨_, rfl, rfl⟩
        | nil =>
          simp only [ClosLang.pureList, Bool.and_true] at pure
          cases first with
          | var trace index =>
            simp only [evaluate] at run
            split at run <;> simp_all
            all_goals aesop
          | fn name location selected arity body =>
            rw [evaluate.eq_def] at run
            dsimp only at run
            repeat' split at run <;> simp_all
            all_goals aesop
          | raise | tick | call | app => simp [ClosLang.pure] at pure
          | ifThenElse trace condition yes no =>
            simp only [ClosLang.pure, Bool.and_eq_true] at pure
            rw [evaluate, fixClock_evaluate] at run
            cases conditionRun : evaluate [condition] env source with
            | mk conditionResult middle =>
              have conditionNotType : conditionResult ≠ .err (.abort .typeError) := by
                intro bad
                subst conditionResult
                rw [conditionRun] at run
                cases run
                exact notType rfl
              have less : expsWeight [condition] < weight := by simp only [expsWeight, expWeight] at measure ⊢; omega
              have condPure : ClosLang.pureList [condition] = true := by simpa [ClosLang.pureList] using pure.1.1
              obtain ⟨values, conditionEq, middleEq⟩ :=
                smaller [condition] env source middle conditionResult less condPure conditionRun conditionNotType
              subst conditionResult
              subst middle
              rw [conditionRun] at run
              dsimp only at run
              split at run
              · cases run; exact False.elim (notType rfl)
              · have less : expsWeight [yes] < weight := by simp only [expsWeight, expWeight] at measure ⊢; omega
                exact smaller [yes] env source next result less (by simpa [ClosLang.pureList] using pure.1.2) run notType
              · have less : expsWeight [no] < weight := by simp only [expsWeight, expWeight] at measure ⊢; omega
                exact smaller [no] env source next result less (by simpa [ClosLang.pureList] using pure.2) run notType
          | «let» trace bindings body =>
            simp only [ClosLang.pure, Bool.and_eq_true] at pure
            rw [evaluate, fixClock_evaluate] at run
            cases bindingsRun : evaluate bindings env source with
            | mk bindingsResult middle =>
              have bindingsNotType : bindingsResult ≠ .err (.abort .typeError) := by
                intro bad
                subst bindingsResult
                rw [bindingsRun] at run
                cases run
                exact notType rfl
              have less : expsWeight bindings < weight := by simp only [expsWeight, expWeight] at measure ⊢; omega
              obtain ⟨values, bindingsEq, middleEq⟩ :=
                smaller bindings env source middle bindingsResult less pure.1 bindingsRun bindingsNotType
              subst bindingsResult
              subst middle
              rw [bindingsRun] at run
              have less : expsWeight [body] < weight := by simp only [expsWeight, expWeight] at measure ⊢; omega
              exact smaller [body] (values ++ env) source next result less
                (by simpa [ClosLang.pureList] using pure.2) run notType
          | handle trace body handler =>
            simp only [ClosLang.pure] at pure
            rw [evaluate, fixClock_evaluate] at run
            cases bodyRun : evaluate [body] env source with
            | mk bodyResult middle =>
              have bodyNotType : bodyResult ≠ .err (.abort .typeError) := by
                intro bad
                subst bodyResult
                rw [bodyRun] at run
                cases run
                exact notType rfl
              have less : expsWeight [body] < weight := by simp only [expsWeight, expWeight] at measure ⊢; omega
              obtain ⟨values, bodyEq, middleEq⟩ := smaller [body] env source middle bodyResult less
                (by simpa [ClosLang.pureList] using pure) bodyRun bodyNotType
              subst bodyResult
              subst middle
              rw [bodyRun] at run
              cases run
              exact ⟨values, rfl, rfl⟩
          | letrec names location selected functions body =>
            simp only [ClosLang.pure] at pure
            rw [evaluate.eq_def] at run
            dsimp only at run
            repeat' split at run
            all_goals try (simp at run; obtain ⟨rfl, rfl⟩ := run; exact False.elim (notType rfl))
            all_goals
              have less : expsWeight [body] < weight := by simp only [expsWeight, expWeight] at measure ⊢; omega
              exact smaller [body] _ source next result less (by simpa [ClosLang.pureList] using pure) run notType
          | op trace op args =>
            simp only [ClosLang.pure, Bool.and_eq_true] at pure
            have notInstall : op ≠ .install := by intro equal; subst op; simp [ClosLang.pureOp] at pure
            have notForce : op ≠ .thunkOp .forceThunk := by intro equal; subst op; simp [ClosLang.pureOp] at pure
            rw [evaluate_ordinaryOp_eq trace op args env source notInstall notForce] at run
            cases argsRun : evaluate args env source with
            | mk argsResult middle =>
              have argsNotType : argsResult ≠ .err (.abort .typeError) := by
                intro bad
                subst argsResult
                rw [argsRun] at run
                cases run
                exact notType rfl
              have less : expsWeight args < weight := by
                have h := opWeight_gt trace op args
                simp only [expsWeight] at measure
                omega
              obtain ⟨values, argsEq, middleEq⟩ := smaller args env source middle argsResult less pure.1 argsRun argsNotType
              subst argsResult
              subst middle
              rw [argsRun] at run
              dsimp only at run
              cases appRun : doApp op values.reverse source with
              | err error =>
                have errorEq := doApp_pure_error op values.reverse source error pure.2 appRun
                subst error
                rw [appRun] at run
                cases run
                exact False.elim (notType rfl)
              | val pair =>
                obtain ⟨value, last⟩ := pair
                have lastEq := doApp_pure_success op values.reverse source last value pure.2 appRun
                subst last
                rw [appRun] at run
                cases run
                exact ⟨[value], rfl, rfl⟩
  exact all (expsWeight expressions) expressions env source next result rfl pure run notType

namespace PureEvaluatePort
/-- Closure states use canonical finite-support maps. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end PureEvaluatePort

/-- Pure expression evaluation either preserves the state and returns one
value per expression, or aborts with a type error. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "EVERY_pure_correct"
  (fmap_as_finite_support := [refs, code])]
theorem everyPureCorrect {C F : Type} :
    ∀ (expressions : List ClosLang.Exp) (env : List Value) (source : State C F),
      (∀ expression ∈ expressions, ClosLang.pure expression = true) →
      match evaluate expressions env source with
      | (.val values, next) => next = source ∧ values.length = expressions.length
      | (.err (.raise _), _) => False
      | (.err (.abort error), _) => error = .typeError := by
  intro expressions env source pure
  have pureList : ClosLang.pureList expressions = true := by
    rw [ClosLang.pureList_eq_all, List.all_eq_true]
    exact pure
  cases run : evaluate expressions env source with
  | mk result next =>
    cases result with
    | val values =>
      obtain ⟨_, resultEq, stateEq⟩ := evaluatePureAux expressions env source next (.val values)
        pureList run (by simp)
      exact ⟨stateEq, (evaluate_length (C := C) (F := F)).1 expressions env source next values run⟩
    | err error =>
      by_cases typeError : error = .abort .typeError
      · subst error; rfl
      · have notType : (Result.err error : Result (List Value) Value) ≠ .err (.abort .typeError) := by
          intro eq
          cases eq
          exact typeError rfl
        obtain ⟨_, impossible, _⟩ := evaluatePureAux expressions env source next (.err error)
          pureList run notType
        cases impossible

/-- Pure evaluation either returns values without changing state or reports
a type error. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_pure"
  (fmap_as_finite_support := [refs, code])]
theorem evaluatePure {C F : Type} (expressions : List ClosLang.Exp) (env : List Value)
    (source : State C F) (result : Result (List Value) Value) (next : State C F)
    (h : evaluate expressions env source = (result, next) ∧
      ∀ expression ∈ expressions, ClosLang.pure expression = true) :
    ∃ values, (result = .val values ∧ next = source) ∨ result = .err (.abort .typeError) := by
  have correct := everyPureCorrect expressions env source h.2
  rw [h.1] at correct
  cases result with
  | val values => exact ⟨values, Or.inl ⟨rfl, correct.1⟩⟩
  | err error =>
    cases error with
    | raise value => exact False.elim correct
    | abort abort => exact ⟨[], Or.inr (by cases correct; rfl)⟩

end Flapjack.Compiler.Backend.ClosProps
