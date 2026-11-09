module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.RecursiveInvariant

@[expose] public section

/-! Partial closure application for direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- A related function accepts the same partial application and produces a
related partially applied closure. This covers ordinary and recursive
closures; full and over-application require the body simulation. -/
theorem destClosure_partial_fuel (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (maxApp : Nat) (requested : Option Nat)
    (source target sourcePartial : ClosSem.Value) (sourceArgs targetArgs : List ClosSem.Value)
    (sourceRun : destClosure maxApp requested source sourceArgs = some (.partialApp sourcePartial))
    (values : ValueRelFuel fuel g allowed code source target)
    (args : List.Forall₂ (ValueRelFuel fuel g allowed code) sourceArgs targetArgs) :
    ∃ targetPartial, destClosure maxApp requested target targetArgs = some (.partialApp targetPartial) ∧
      ValueRelFuel fuel g allowed code sourcePartial targetPartial := by
  have argsLength := args.length_eq
  cases values with
  | number | word64 | block | byteVector | refPtr => simp [destClosure] at sourceRun
  | @closure loc sourceSupplied targetSupplied sourceEnv targetEnv arity sourceBody targetBody closure supplied envs =>
    have suppliedLength := supplied.length_eq
    by_cases valid : checkLoc maxApp requested (some loc) arity sourceArgs.length sourceSupplied.length &&
        sourceSupplied.length < arity
    · by_cases undersaturated : sourceArgs.length + sourceSupplied.length < arity
      · have sourceEq : sourcePartial = .closure (some loc) (sourceArgs ++ sourceSupplied) sourceEnv arity sourceBody := by
          simpa [destClosure, valid, undersaturated] using sourceRun.symm
        subst sourcePartial
        refine ⟨.closure (some loc) (targetArgs ++ targetSupplied) targetEnv arity targetBody, ?_,
          .closure closure (List.rel_append args supplied) envs⟩
        simp [destClosure, ← argsLength, ← suppliedLength, valid, undersaturated]
      · simp [destClosure, valid, undersaturated] at sourceRun
    · simp [destClosure, valid] at sourceRun
  | @recclosure loc sourceSupplied targetSupplied sourceEnv targetEnv sourceFns targetFns index closure supplied envs =>
    have suppliedLength := supplied.length_eq
    cases sourceLookup : sourceFns[index]? with
    | none => simp [destClosure, sourceLookup] at sourceRun
    | some fn =>
      obtain ⟨arity, sourceBody⟩ := fn
      have arities := recClosureRelFuel_arities fuel g allowed code loc sourceFns targetFns closure
      have targetArity : (targetFns.map Prod.fst)[index]? = some arity := by
        rw [arities]
        simp [List.getElem?_map, sourceLookup]
      cases targetLookup : targetFns[index]? with
      | none => simp [List.getElem?_map, targetLookup] at targetArity
      | some targetFn =>
        obtain ⟨targetArity', targetBody⟩ := targetFn
        have arityEq : targetArity' = arity := by
          simpa [List.getElem?_map, targetLookup] using targetArity
        subst targetArity'
        by_cases valid : checkLoc maxApp requested (some (2 * index + loc)) arity
            sourceArgs.length sourceSupplied.length && sourceSupplied.length < arity
        · by_cases undersaturated : sourceArgs.length + sourceSupplied.length < arity
          · have sourceEq : sourcePartial = .recclosure (some loc) (sourceArgs ++ sourceSupplied)
                sourceEnv sourceFns index := by
              simpa [destClosure, sourceLookup, valid, undersaturated] using sourceRun.symm
            subst sourcePartial
            refine ⟨.recclosure (some loc) (targetArgs ++ targetSupplied) targetEnv targetFns index, ?_,
              .recclosure closure (List.rel_append args supplied) envs⟩
            simp [destClosure, targetLookup, ← argsLength, ← suppliedLength, valid, undersaturated]
          · simp [destClosure, sourceLookup, valid, undersaturated] at sourceRun
        · simp [destClosure, sourceLookup, valid] at sourceRun

/-- Zeroing both clocks preserves the direct-call state relation. -/
theorem stateRelFuel_zeroClock {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {source : ClosSem.State (NumSet × C) F} {target : ClosSem.State C F}
    (states : StateRelFuel fuel g allowed source target) :
    StateRelFuel fuel g allowed { source with clock := 0 } { target with clock := 0 } := by
  obtain ⟨ffi, _, maxApp, globals, refs, sourceCode⟩ := states
  exact ⟨ffi, rfl, maxApp, globals, refs, sourceCode⟩

/-- Partial application simulates through the evaluator, including timeout
and clock consumption. Full application remains a separate obligation. -/
theorem evaluateApp_partial_fuel {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (requested : Option Nat) (sourceFun targetFun sourcePartial : ClosSem.Value)
    (sourceArgs targetArgs : List ClosSem.Value)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (sourceResult : Result (List ClosSem.Value) ClosSem.Value) (sourceFinal : ClosSem.State (NumSet × C) F)
    (nonempty : sourceArgs ≠ [])
    (sourceClosure : destClosure source.maxApp requested sourceFun sourceArgs = some (.partialApp sourcePartial))
    (sourceRun : evaluateApp requested sourceFun sourceArgs source = (sourceResult, sourceFinal))
    (functions : ValueRelFuel fuel g allowed target.code sourceFun targetFun)
    (args : List.Forall₂ (ValueRelFuel fuel g allowed target.code) sourceArgs targetArgs)
    (states : StateRelFuel fuel g allowed source target) :
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
  obtain ⟨targetPartial, targetClosure, partialRel⟩ :=
    destClosure_partial_fuel fuel g allowed target.code source.maxApp requested sourceFun targetFun sourcePartial
      sourceArgs targetArgs sourceClosure functions args
  have targetClosure' : destClosure target.maxApp requested targetFun targetArgs = some (.partialApp targetPartial) := by
    simpa [← maxApp] using targetClosure
  have clocks := states.2.1
  have lengths := args.length_eq
  cases sourceArgs with
  | nil => contradiction
  | cons sourceHead sourceTail =>
    cases targetArgs with
    | nil => contradiction
    | cons targetHead targetTail =>
      rw [evaluateApp, sourceClosure] at sourceRun
      by_cases timeout : source.clock < (sourceHead :: sourceTail).length
      · have targetTimeout : target.clock < (targetHead :: targetTail).length := by omega
        have sourceTimeout' : source.clock ≤ sourceTail.length := by simpa using timeout
        have targetTimeout' : target.clock ≤ targetTail.length := by simpa using targetTimeout
        have sourceEq : sourceResult = .err (.abort .timeoutError) ∧ sourceFinal = { source with clock := 0 } := by
          simpa [sourceTimeout'] using sourceRun.symm
        obtain ⟨rfl, rfl⟩ := sourceEq
        refine ⟨.err (.abort .timeoutError), { target with clock := 0 }, ?_, ?_, stateRelFuel_zeroClock states, ?_⟩
        · rw [evaluateApp, targetClosure']
          simp [targetTimeout']
        · rfl
        · exact fun _ _ h => h
      · have targetEnough : ¬ target.clock < (targetHead :: targetTail).length := by omega
        have sourceEnough' : ¬ source.clock ≤ sourceTail.length := by simpa using timeout
        have targetEnough' : ¬ target.clock ≤ targetTail.length := by simpa using targetEnough
        have sourceEq : sourceResult = .val [sourcePartial] ∧
            sourceFinal = decClock (sourceHead :: sourceTail).length source := by
          simpa [sourceEnough'] using sourceRun.symm
        obtain ⟨rfl, rfl⟩ := sourceEq
        refine ⟨.val [targetPartial], decClock (targetHead :: targetTail).length target, ?_, ?_, ?_, ?_⟩
        · rw [evaluateApp, targetClosure']
          simp [targetEnough']
        · exact .cons partialRel .nil
        · rw [← lengths]
          exact stateRelFuel_decClock states (sourceHead :: sourceTail).length
        · exact fun _ _ h => h

end Flapjack.Compiler.Backend.ClosCall
