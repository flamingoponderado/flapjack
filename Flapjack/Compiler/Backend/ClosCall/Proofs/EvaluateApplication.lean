import Flapjack.Compiler.Backend.ClosCall.Proofs.FullApplication

/-! Evaluation of direct-call-related closure applications. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- Source-driven application simulation. This fuel-aware interface omits
the full HOL theorem's compiler-oracle and growing-state conclusions. -/
def AppSimFuel {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (requested : Option Nat) (sourceFun targetFun : ClosSem.Value)
    (sourceArgs targetArgs : List ClosSem.Value) : Prop :=
  ∀ (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceResult : Result (List ClosSem.Value) ClosSem.Value) (sourceFinal : ClosSem.State (NumSet × C) F),
    evaluateApp requested sourceFun sourceArgs source = (sourceResult, sourceFinal) →
    sourceResult ≠ .err (.abort .typeError) →
    ValueRelFuel fuel g allowed target.code sourceFun targetFun →
    List.Forall₂ (ValueRelFuel fuel g allowed target.code) sourceArgs targetArgs →
    StateRelFuel fuel g allowed source target →
    ∃ targetResult targetFinal,
      evaluateApp requested targetFun targetArgs target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel g allowed targetFinal.code))
        (ValueRelFuel fuel g allowed targetFinal.code) sourceResult targetResult ∧
      StateRelFuel fuel g allowed sourceFinal targetFinal ∧
      (∀ key value, target.code.lookup key = some value → targetFinal.code.lookup key = some value)

/-- The empty-argument application returns the related function unchanged. -/
theorem appSimFuel_nil {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (requested : Option Nat) (sourceFun targetFun : ClosSem.Value) :
    AppSimFuel (C := C) (F := F) fuel g allowed requested sourceFun targetFun [] [] := by
  intro source target sourceResult sourceFinal run _ functions _ states
  have sourceEq : sourceResult = .val [sourceFun] ∧ sourceFinal = source := by
    simpa [evaluateApp] using run.symm
  obtain ⟨rfl, rfl⟩ := sourceEq
  exact ⟨.val [targetFun], target, by simp [evaluateApp], .cons functions .nil, states, fun _ _ h => h⟩

/-- Full application simulates when the selected body and a subsequent
over-application satisfy their induction hypotheses. -/
theorem evaluateApp_full_fuel {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (requested : Option Nat) (sourceFun targetFun : ClosSem.Value)
    (sourceArgs targetArgs : List ClosSem.Value) (sourceBody : ClosLang.Exp)
    (sourceBodyEnv sourceRest : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceResult : Result (List ClosSem.Value) ClosSem.Value) (sourceFinal : ClosSem.State (NumSet × C) F)
    (nonempty : sourceArgs ≠ [])
    (sourceClosure : destClosure source.maxApp requested sourceFun sourceArgs = some (.fullApp sourceBody sourceBodyEnv sourceRest))
    (sourceRun : evaluateApp requested sourceFun sourceArgs source = (sourceResult, sourceFinal))
    (notType : sourceResult ≠ .err (.abort .typeError))
    (functions : ValueRelFuel fuel g allowed target.code sourceFun targetFun)
    (args : List.Forall₂ (ValueRelFuel fuel g allowed target.code) sourceArgs targetArgs)
    (states : StateRelFuel fuel g allowed source target) (distinct : (g.2.map Prod.fst).Nodup)
    (bodyIH : ∀ (targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed target.code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      ExprSimFuel (C := C) (F := F) fuel g allowed sourceBody targetBody)
    (appIH : ∀ sourceValue targetValue targetRest,
      sourceRest.length < sourceArgs.length →
      AppSimFuel (C := C) (F := F) fuel g allowed requested sourceValue targetValue sourceRest targetRest) :
    ∃ targetResult targetFinal,
      evaluateApp requested targetFun targetArgs target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRelFuel fuel g allowed targetFinal.code))
        (ValueRelFuel fuel g allowed targetFinal.code) sourceResult targetResult ∧
      StateRelFuel fuel g allowed sourceFinal targetFinal ∧
      (∀ key value, target.code.lookup key = some value → targetFinal.code.lookup key = some value) := by
  have targetNonempty : targetArgs ≠ [] := by
    intro empty
    have len := args.length_eq
    simp [empty] at len
    cases sourceArgs with
    | nil => exact nonempty rfl
    | cons head tail => simp at len
  have maxApp := states.2.2.1
  obtain ⟨targetBody, targetBodyEnv, targetRest, loc, sourceFns, targetFns, index, arity,
      targetClosure, bodyEnv, restRel, closure, sourceLookup, targetLookup, _⟩ :=
    destClosure_full_fuel fuel g allowed target.code source.maxApp requested sourceFun targetFun
      sourceArgs targetArgs sourceBody sourceBodyEnv sourceRest sourceClosure functions args
  have targetClosure' : destClosure target.maxApp requested targetFun targetArgs =
      some (.fullApp targetBody targetBodyEnv targetRest) := by simpa [← maxApp] using targetClosure
  have restShort := destClosure_full_remaining_lt source.maxApp requested sourceFun sourceArgs sourceBodyEnv sourceRest
    sourceBody sourceClosure
  have clocks := states.2.1
  have lengths := args.length_eq
  have restLengths := restRel.length_eq
  let cost := sourceArgs.length - sourceRest.length
  have targetCost : targetArgs.length - targetRest.length = cost := by simp [cost, ← lengths, ← restLengths]
  cases sourceArgs with
  | nil => contradiction
  | cons sourceHead sourceTail =>
    cases targetArgs with
    | nil => contradiction
    | cons targetHead targetTail =>
      rw [evaluateApp, sourceClosure] at sourceRun
      have sourceCostEq : sourceTail.length + 1 - sourceRest.length = cost := rfl
      have targetCostEq : targetTail.length + 1 - targetRest.length = cost := targetCost
      simp only [List.length_cons, sourceCostEq] at sourceRun
      by_cases timeout : source.clock < cost
      · have targetTimeout : target.clock < (targetHead :: targetTail).length - targetRest.length := by
          rw [targetCost]; omega
        have sourceEq : sourceResult = .err (.abort .timeoutError) ∧ sourceFinal = { source with clock := 0 } := by
          simpa [timeout] using sourceRun.symm
        obtain ⟨rfl, rfl⟩ := sourceEq
        refine ⟨.err (.abort .timeoutError), { target with clock := 0 }, ?_, ?_, stateRelFuel_zeroClock states, ?_⟩
        · rw [evaluateApp, targetClosure']
          simp only [List.length_cons, targetCostEq]
          have targetTimeout' : target.clock < cost := by omega
          simp [targetTimeout']
        · rfl
        · exact fun _ _ h => h
      · have targetEnough : ¬ target.clock < (targetHead :: targetTail).length - targetRest.length := by
          rw [targetCost]; omega
        let sourceStart := decClock cost source
        let targetStart := decClock cost target
        have startStates : StateRelFuel fuel g allowed sourceStart targetStart := stateRelFuel_decClock states cost
        simp only [if_neg timeout, fixClock_evaluate] at sourceRun
        cases bodyRun : evaluate [sourceBody] sourceBodyEnv sourceStart with
        | mk bodyResult bodyFinal =>
          have bodyNotType : bodyResult ≠ .err (.abort .typeError) := by
            intro bad
            subst bodyResult
            have : sourceResult = .err (.abort .typeError) := by
              simpa [sourceStart, bodyRun] using congrArg Prod.fst sourceRun.symm
            exact notType this
          obtain ⟨targetBodyResult, targetBodyFinal, targetBodyRun, bodyRel, bodyStates, bodyGrowth⟩ :=
            bodyIH targetBody loc sourceFns targetFns index arity closure sourceLookup targetLookup
              sourceBodyEnv targetBodyEnv sourceStart targetStart bodyResult bodyFinal bodyRun bodyNotType bodyEnv startStates
          have targetBodyRun' : evaluate [targetBody] targetBodyEnv (decClock cost target) =
              (targetBodyResult, targetBodyFinal) := by simpa [targetStart] using targetBodyRun
          cases bodyResult with
          | err error =>
            cases targetBodyResult with
            | val vs => simp [resultRel] at bodyRel
            | err targetError =>
              have sourceEq : sourceResult = .err error ∧ sourceFinal = bodyFinal := by
                simpa [sourceStart, bodyRun] using sourceRun.symm
              obtain ⟨rfl, rfl⟩ := sourceEq
              refine ⟨.err targetError, targetBodyFinal, ?_, bodyRel, bodyStates, bodyGrowth⟩
              rw [evaluateApp, targetClosure']
              simp only [List.length_cons, targetCostEq]
              have targetEnough' : ¬ target.clock < cost := by omega
              rw [if_neg targetEnough', fixClock_evaluate, targetBodyRun']
          | val sourceValues =>
            obtain ⟨sourceValue, rfl⟩ := evaluate_singleton_value sourceBody sourceBodyEnv sourceStart bodyFinal sourceValues bodyRun
            cases targetBodyResult with
            | err error => simp [resultRel] at bodyRel
            | val targetValues =>
              obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value targetBody targetBodyEnv targetStart targetBodyFinal targetValues targetBodyRun
              have valueRel : ValueRelFuel fuel g allowed targetBodyFinal.code sourceValue targetValue := by
                simpa [resultRel] using bodyRel
              have restRel' : List.Forall₂ (ValueRelFuel fuel g allowed targetBodyFinal.code) sourceRest targetRest :=
                List.Forall₂.imp (fun _ _ h => valueRelFuel_mono h (stateExtends_refl g distinct) Set.Subset.rfl bodyGrowth) restRel
              have nextRun : evaluateApp requested sourceValue sourceRest bodyFinal = (sourceResult, sourceFinal) := by
                simpa [sourceStart, bodyRun] using sourceRun
              obtain ⟨result, final, targetRun, results, finalStates, growth⟩ :=
                appIH sourceValue targetValue targetRest restShort bodyFinal targetBodyFinal sourceResult sourceFinal
                  nextRun notType valueRel restRel' bodyStates
              refine ⟨result, final, ?_, results, finalStates, ?_⟩
              · rw [evaluateApp, targetClosure']
                simp only [List.length_cons, targetCostEq]
                have targetEnough' : ¬ target.clock < cost := by omega
                rw [if_neg targetEnough', fixClock_evaluate, targetBodyRun']
                exact targetRun
              · intro key value lookup
                exact growth key value (bodyGrowth key value lookup)

/-- One source-driven application step, combining empty, invalid, partial,
and full applications. The explicit induction hypotheses cover selected
bodies and recursive applications to shorter argument lists. -/
theorem appSimFuel_step {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (requested : Option Nat) (sourceFun targetFun : ClosSem.Value)
    (sourceArgs targetArgs : List ClosSem.Value) (distinct : (g.2.map Prod.fst).Nodup)
    (bodyIH : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (sourceBody targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      ExprSimFuel (C := C) (F := F) fuel g allowed sourceBody targetBody)
    (appIH : ∀ sourceValue targetValue sourceRest targetRest,
      sourceRest.length < sourceArgs.length →
      AppSimFuel (C := C) (F := F) fuel g allowed requested sourceValue targetValue sourceRest targetRest) :
    AppSimFuel (C := C) (F := F) fuel g allowed requested sourceFun targetFun sourceArgs targetArgs := by
  intro source target sourceResult sourceFinal run notType functions args states
  cases sourceArgs with
  | nil =>
    have targetEmpty : targetArgs = [] := by
      have len := args.length_eq
      cases targetArgs with
      | nil => rfl
      | cons head tail => simp at len
    subst targetArgs
    exact appSimFuel_nil fuel g allowed requested sourceFun targetFun source target sourceResult sourceFinal
      run notType functions args states
  | cons first rest =>
    have nonempty : first :: rest ≠ [] := by simp
    cases closureRun : destClosure source.maxApp requested sourceFun (first :: rest) with
    | none =>
      have bad : sourceResult = .err (.abort .typeError) := by
        rw [evaluateApp, closureRun] at run
        simpa using congrArg Prod.fst run.symm
      exact False.elim (notType bad)
    | some closure =>
      cases closure with
      | partialApp value =>
        exact evaluateApp_partial_fuel fuel g allowed requested sourceFun targetFun value (first :: rest) targetArgs
          source target sourceResult sourceFinal nonempty closureRun run functions args states
      | fullApp body env remaining =>
        exact evaluateApp_full_fuel fuel g allowed requested sourceFun targetFun (first :: rest) targetArgs
          body env remaining source target sourceResult sourceFinal nonempty closureRun run notType functions args states distinct
          (bodyIH target.code body) (fun s t rs shorter => appIH s t remaining rs shorter)

/-- Induction on remaining arguments discharges all repeated-application
steps, assuming simulations for the selected related function bodies. -/
theorem appSimFuel_of_bodies {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (requested : Option Nat) (distinct : (g.2.map Prod.fst).Nodup)
    (bodyIH : ∀ (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
        (sourceBody targetBody : ClosLang.Exp) (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp))
        (index arity : Nat),
      recClosureRelFuel fuel g allowed code loc sourceFns targetFns →
      sourceFns[index]? = some (arity, sourceBody) → targetFns[index]? = some (arity, targetBody) →
      ExprSimFuel (C := C) (F := F) fuel g allowed sourceBody targetBody) :
    ∀ sourceFun targetFun sourceArgs targetArgs,
      AppSimFuel (C := C) (F := F) fuel g allowed requested sourceFun targetFun sourceArgs targetArgs := by
  have all : ∀ n, ∀ sourceFun targetFun (sourceArgs targetArgs : List ClosSem.Value),
      sourceArgs.length = n → AppSimFuel (C := C) (F := F) fuel g allowed requested
        sourceFun targetFun sourceArgs targetArgs := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro sourceFun targetFun sourceArgs targetArgs size
      apply appSimFuel_step fuel g allowed requested sourceFun targetFun sourceArgs targetArgs distinct bodyIH
      intro sourceValue targetValue sourceRest targetRest shorter
      apply ih sourceRest.length (by omega) sourceValue targetValue sourceRest targetRest rfl
  intro sourceFun targetFun sourceArgs targetArgs
  exact all sourceArgs.length sourceFun targetFun sourceArgs targetArgs rfl

end Flapjack.Compiler.Backend.ClosCall
