import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluateForce

/-! Application cases for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesProps

/-- The expression simulation restricted to states below an outer clock.
This is an induction interface for the Lean evaluator, not a separate HOL port. -/
def EvaluateRelBelow {C F : Type} (limit : Nat) (sourceCode targetCode : List ClosLang.Exp) : Prop :=
  ∀ (targetEnv : List Value) (target : State C F) (sourceEnv : List Value)
    (targetFinal : State C F) (source : State C F)
    (targetResult : SemanticPrimitivesHOL.Result (List Value) Value),
    source.clock < limit → evaluate targetCode targetEnv target = (targetResult, targetFinal) →
    List.Forall₂ (ValueRel source.maxApp) sourceEnv targetEnv →
    StateRel source target → CodeRel source.maxApp sourceCode targetCode →
    ∃ sourceResult sourceFinal,
      evaluate sourceCode sourceEnv source = (sourceResult, sourceFinal) ∧
      resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
        sourceResult targetResult ∧ StateRel sourceFinal targetFinal

/-- Relate replacement of both closure clocks by the same value. -/
theorem stateRel_withClock {C F : Type} {source target : State C F}
    (states : StateRel source target) (clock : Nat) :
    StateRel { source with clock := clock } { target with clock := clock } := by
  obtain ⟨safe, sourceCode, targetCode, maxEq, positive, _, ffi, globals, refs, compiler, oracle⟩ := states
  exact ⟨safe, sourceCode, targetCode, maxEq, positive, rfl, ffi, globals, refs, compiler, oracle⟩

/-- Applying no arguments preserves related functions and states. -/
theorem evaluateApp_nil_related {C F : Type} (source target : State C F)
    (sourceFunction targetFunction : Value) (states : StateRel source target)
    (functions : ValueRel source.maxApp sourceFunction targetFunction) :
    evaluateApps sourceFunction [] source = (.val [sourceFunction], source) ∧
    evaluateApp none targetFunction [] target = (.val [targetFunction], target) ∧
    resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
      (.val [sourceFunction]) (.val [targetFunction]) ∧ StateRel source target := by
  exact ⟨rfl, by rw [evaluateApp], by simpa [resultRel] using List.Forall₂.cons functions .nil, states⟩

/-- Partial application of a collected ordinary closure corresponds to
applying its nested unary functions. This Lean-side case includes timeout;
the remaining application cases and HOL evaluator correspondence are open. -/
theorem evaluateApp_closure_partial {C F : Type} (source target : State C F)
    (sourceArgs targetArgs sourceSupplied targetSupplied sourceEnv targetEnv : List Value)
    (arity : Nat) (sourceBody targetBody : ClosLang.Exp)
    (names : List Basis.Pure.MlString.MlString)
    (states : StateRel source target)
    (argsRel : List.Forall₂ (ValueRel source.maxApp) sourceArgs targetArgs)
    (suppliedRel : List.Forall₂ (ValueRel source.maxApp) sourceSupplied targetSupplied)
    (envRel : List.Forall₂ (ValueRel source.maxApp) sourceEnv targetEnv)
    (bodyRel : CodeRel source.maxApp [sourceBody] [targetBody])
    (arityEq : 1 + names.length + sourceSupplied.length = arity)
    (nonempty : targetArgs ≠ []) (bound : sourceArgs.length ≤ source.maxApp)
    (partialCount : sourceArgs.length ≤ names.length) :
    resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
      (evaluateApps (.closure none [] (sourceSupplied ++ sourceEnv) 1 (mkFns names sourceBody))
        sourceArgs source).1
      (evaluateApp none (.closure none targetSupplied targetEnv arity targetBody) targetArgs target).1 ∧
    StateRel
      (evaluateApps (.closure none [] (sourceSupplied ++ sourceEnv) 1 (mkFns names sourceBody))
        sourceArgs source).2
      (evaluateApp none (.closure none targetSupplied targetEnv arity targetBody) targetArgs target).2 := by
  have argsLength := argsRel.length_eq
  have suppliedLength := suppliedRel.length_eq
  have agreement := stateRel_clock_maxApp states
  have targetBound : targetArgs.length ≤ target.maxApp := by omega
  have suppliedBound : targetSupplied.length < arity := by omega
  have partialBound : targetArgs.length + targetSupplied.length < arity := by omega
  have targetRun :
      evaluateApp none (.closure none targetSupplied targetEnv arity targetBody) targetArgs target =
        if target.clock < targetArgs.length then (.err (.abort .timeoutError), { target with clock := 0 })
        else (.val [.closure none (targetArgs ++ targetSupplied) targetEnv arity targetBody],
          decClock targetArgs.length target) := by
    cases targetArgs with
    | nil => exact (nonempty rfl).elim
    | cons first rest =>
      simp only [List.length_cons] at targetBound partialBound
      rw [evaluateApp]
      simp [destClosure, checkLoc, targetBound, suppliedBound, partialBound]
      split <;> simp_all
  by_cases timeout : target.clock < targetArgs.length
  · have sourceTimeout : source.clock < sourceArgs.length := by omega
    have sourceRun := evaluateApps_nestedFns_timeout sourceArgs names sourceBody
      (sourceSupplied ++ sourceEnv) source sourceTimeout partialCount (by omega)
    rw [sourceRun, targetRun]
    simp only [timeout, ↓reduceIte]
    exact ⟨by simp [resultRel, excRel], stateRel_withClock states 0⟩
  · have sourceClock : sourceArgs.length ≤ source.clock := by omega
    have sourceRun := evaluateApps_nestedFns_short sourceArgs names sourceBody
      (sourceSupplied ++ sourceEnv) source sourceClock partialCount (by omega)
    have combined : List.Forall₂ (ValueRel source.maxApp)
        (sourceArgs ++ sourceSupplied) (targetArgs ++ targetSupplied) :=
      List.rel_append argsRel suppliedRel
    have nextArity : 1 + (names.drop sourceArgs.length).length +
        (sourceArgs ++ sourceSupplied).length = arity := by
      simp [List.length_drop, List.length_append]
      omega
    have nextClosure : ValueRel source.maxApp
        (.closure none [] (sourceArgs ++ sourceSupplied ++ sourceEnv) 1
          (mkFns (names.drop sourceArgs.length) sourceBody))
        (.closure none (targetArgs ++ targetSupplied) targetEnv arity targetBody) :=
      .closure (sourceArgs ++ sourceSupplied) (targetArgs ++ targetSupplied) sourceEnv targetEnv
        arity sourceBody targetBody (names.drop sourceArgs.length) nextArity bodyRel envRel combined
    rw [sourceRun, targetRun]
    simp only [timeout, ↓reduceIte]
    constructor
    · simpa [resultRel, List.append_assoc] using List.Forall₂.cons nextClosure List.Forall₂.nil
    · have clocks := stateRel_withClock states (source.clock - sourceArgs.length)
      simpa [decClock, agreement.1, argsLength] using clocks

/-- A full or over-application times out before entering the closure body
on both sides when the clock cannot cover the collected unary calls. This
uses the Lean evaluator; its correspondence with HOL remains open. -/
theorem evaluateApp_closure_full_timeout {C F : Type} (source target : State C F)
    (sourceArgs targetArgs sourceSupplied targetSupplied sourceEnv targetEnv : List Value)
    (arity : Nat) (sourceBody targetBody : ClosLang.Exp)
    (names : List Basis.Pure.MlString.MlString)
    (states : StateRel source target)
    (argsRel : List.Forall₂ (ValueRel source.maxApp) sourceArgs targetArgs)
    (suppliedRel : List.Forall₂ (ValueRel source.maxApp) sourceSupplied targetSupplied)
    (arityEq : 1 + names.length + sourceSupplied.length = arity)
    (bound : sourceArgs.length ≤ source.maxApp)
    (full : names.length < sourceArgs.length) (timeout : source.clock ≤ names.length) :
    evaluateApps (.closure none [] (sourceSupplied ++ sourceEnv) 1 (mkFns names sourceBody))
        sourceArgs source = (.err (.abort .timeoutError), { source with clock := 0 }) ∧
    evaluateApp none (.closure none targetSupplied targetEnv arity targetBody) targetArgs target =
        (.err (.abort .timeoutError), { target with clock := 0 }) ∧
    StateRel { source with clock := 0 } { target with clock := 0 } := by
  have argsLength := argsRel.length_eq
  have suppliedLength := suppliedRel.length_eq
  have agreement := stateRel_clock_maxApp states
  have targetBound : targetArgs.length ≤ target.maxApp := by omega
  have suppliedBound : targetSupplied.length < arity := by omega
  have fullBound : arity ≤ targetArgs.length + targetSupplied.length := by omega
  have costTimeout : target.clock < arity - targetSupplied.length := by omega
  refine ⟨evaluateApps_nestedFns_timeout_long sourceArgs names sourceBody
    (sourceSupplied ++ sourceEnv) source timeout full (by omega), ?_, stateRel_withClock states 0⟩
  cases targetArgs with
  | nil => simp only [List.length_nil] at argsLength; omega
  | cons first rest =>
    simp only [List.length_cons] at targetBound fullBound
    have dest : destClosure target.maxApp none
        (.closure none targetSupplied targetEnv arity targetBody) (first :: rest) =
        some (.fullApp targetBody
          (((first :: rest).reverse.take (arity - targetSupplied.length)).reverse ++
            (targetSupplied ++ targetEnv))
          (((first :: rest).reverse.drop (arity - targetSupplied.length)).reverse)) := by
      simp [destClosure, checkLoc, targetBound, suppliedBound, Nat.not_lt.mpr fullBound]
    rw [evaluateApp]
    have cost : rest.length + 1 - (rest.length + 1 - (arity - targetSupplied.length)) =
        arity - targetSupplied.length := by omega
    split <;> simp_all [List.length_drop]

/-- Full application evaluates the body using the final arguments and then
applies any remaining arguments to a returned value. This is a decomposition
of the current Lean evaluator, pending HOL correspondence review. -/
theorem evaluateApp_closure_full {C F : Type} (state : State C F)
    (args supplied env : List Value) (arity : Nat) (body : ClosLang.Exp)
    (nonempty : args ≠ []) (bound : args.length ≤ state.maxApp)
    (suppliedBound : supplied.length < arity)
    (full : arity ≤ args.length + supplied.length)
    (clock : arity - supplied.length ≤ state.clock) :
    evaluateApp none (.closure none supplied env arity body) args state =
      match evaluate [body]
          ((args.reverse.take (arity - supplied.length)).reverse ++ (supplied ++ env))
          (decClock (arity - supplied.length) state) with
      | (.val [value], next) =>
        evaluateApp none value ((args.reverse.drop (arity - supplied.length)).reverse) next
      | result => result := by
  cases args with
  | nil => exact (nonempty rfl).elim
  | cons first rest =>
    have dest : destClosure state.maxApp none (.closure none supplied env arity body) (first :: rest) =
        some (.fullApp body
          (((first :: rest).reverse.take (arity - supplied.length)).reverse ++ (supplied ++ env))
          (((first :: rest).reverse.drop (arity - supplied.length)).reverse)) := by
      simp only [destClosure, checkLoc, bound, decide_true, Bool.true_and, suppliedBound,
        ↓reduceIte, Nat.not_lt.mpr full]
      rfl
    have cost : (first :: rest).length -
        (((first :: rest).reverse.drop (arity - supplied.length)).reverse).length =
        arity - supplied.length := by
      simp only [List.length_reverse, List.length_drop]
      omega
    rw [evaluateApp]
    split
    · simp_all
    · simp_all
    · rename_i expression captured remaining found
      rw [dest] at found
      simp only [Option.some.injEq, AppKind.fullApp.injEq] at found
      obtain ⟨rfl, rfl, rfl⟩ := found
      simp only [cost, not_lt.mpr clock, ↓reduceIte, fixClock_evaluate]
      cases run : evaluate [body]
          (((first :: rest).reverse.take (arity - supplied.length)).reverse ++ (supplied ++ env))
          (decClock (arity - supplied.length) state) with
      | mk result next =>
        cases result with
        | err error => rfl
        | val values =>
          cases values with
          | nil => rfl
          | cons value tail =>
            cases tail <;> rfl

/-- Full ordinary closure application follows from the body simulation and
the smaller-clock application induction hypothesis. This includes both exact
application and over-application in the current Lean evaluator. -/
theorem evaluateApp_closure_full_related {C F : Type} (source target : State C F)
    (sourceArgs targetArgs sourceSupplied targetSupplied sourceEnv targetEnv : List Value)
    (arity : Nat) (sourceBody targetBody : ClosLang.Exp)
    (names : List Basis.Pure.MlString.MlString)
    (states : StateRel source target)
    (argsRel : List.Forall₂ (ValueRel source.maxApp) sourceArgs targetArgs)
    (suppliedRel : List.Forall₂ (ValueRel source.maxApp) sourceSupplied targetSupplied)
    (envRel : List.Forall₂ (ValueRel source.maxApp) sourceEnv targetEnv)
    (bodyRel : CodeRel source.maxApp [sourceBody] [targetBody])
    (arityEq : 1 + names.length + sourceSupplied.length = arity)
    (full : names.length < sourceArgs.length) (bound : sourceArgs.length ≤ source.maxApp)
    (bodyIH : EvaluateRelBelow (C := C) (F := F) source.clock [sourceBody] [targetBody])
    (appIH : ∀ (s t : State C F) (sv tv : Value) (sa ta : List Value),
      s.clock < source.clock → StateRel s t → ValueRel s.maxApp sv tv →
      List.Forall₂ (ValueRel s.maxApp) sa ta → sa.length ≤ s.maxApp →
      resultRel (List.Forall₂ (ValueRel s.maxApp)) (ValueRel s.maxApp)
        (evaluateApps sv sa s).1 (evaluateApp none tv ta t).1 ∧
      StateRel (evaluateApps sv sa s).2 (evaluateApp none tv ta t).2) :
    resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
      (evaluateApps (.closure none [] (sourceSupplied ++ sourceEnv) 1 (mkFns names sourceBody))
        sourceArgs source).1
      (evaluateApp none (.closure none targetSupplied targetEnv arity targetBody) targetArgs target).1 ∧
    StateRel
      (evaluateApps (.closure none [] (sourceSupplied ++ sourceEnv) 1 (mkFns names sourceBody))
        sourceArgs source).2
      (evaluateApp none (.closure none targetSupplied targetEnv arity targetBody) targetArgs target).2 := by
  by_cases timeout : source.clock ≤ names.length
  · obtain ⟨sourceRun, targetRun, finalStates⟩ :=
      evaluateApp_closure_full_timeout source target sourceArgs targetArgs sourceSupplied targetSupplied
        sourceEnv targetEnv arity sourceBody targetBody names states argsRel suppliedRel arityEq bound
        full timeout
    rw [sourceRun, targetRun]
    exact ⟨by simp [resultRel, excRel], finalStates⟩
  · have argsLength := argsRel.length_eq
    have suppliedLength := suppliedRel.length_eq
    have agreement := stateRel_clock_maxApp states
    have count : arity - targetSupplied.length = 1 + names.length := by omega
    have targetBound : targetArgs.length ≤ target.maxApp := by omega
    have targetSuppliedBound : targetSupplied.length < arity := by omega
    have targetFull : arity ≤ targetArgs.length + targetSupplied.length := by omega
    have targetClock : arity - targetSupplied.length ≤ target.clock := by omega
    have targetNonempty : targetArgs ≠ [] := by
      intro empty
      simp only [empty, List.length_nil] at argsLength
      omega
    have starts : StateRel (decClock (1 + names.length) source)
        (decClock (1 + names.length) target) := by
      have related := stateRel_withClock states (source.clock - (1 + names.length))
      simpa [decClock, agreement.1] using related
    have reversed := (List.forall₂_reverse_iff).2 argsRel
    have consumed := (List.forall₂_reverse_iff).2 (List.forall₂_take (1 + names.length) reversed)
    have remaining := (List.forall₂_reverse_iff).2 (List.forall₂_drop (1 + names.length) reversed)
    have environments := List.rel_append consumed (List.rel_append suppliedRel envRel)
    rw [evaluateApps_nestedFns_long sourceArgs names sourceBody (sourceSupplied ++ sourceEnv) source
      (by omega) full (by omega),
      evaluateApp_closure_full target targetArgs targetSupplied targetEnv arity targetBody
        targetNonempty targetBound targetSuppliedBound targetFull targetClock, count]
    cases targetRun : evaluate [targetBody]
        ((targetArgs.reverse.take (1 + names.length)).reverse ++ (targetSupplied ++ targetEnv))
        (decClock (1 + names.length) target) with
    | mk targetResult targetFinal =>
      obtain ⟨sourceResult, sourceFinal, sourceRun, related, finalStates⟩ :=
        bodyIH _ _ _ _ _ _ (by simp [decClock]; omega) targetRun (by simpa [decClock] using environments) starts
          (by simpa [decClock] using bodyRel)
      rw [sourceRun]
      have maxConst := ClosProps.evaluate_const.1 [sourceBody]
        ((sourceArgs.reverse.take (1 + names.length)).reverse ++ (sourceSupplied ++ sourceEnv))
        (decClock (1 + names.length) source)
      rw [sourceRun] at maxConst
      have maxEq : sourceFinal.maxApp = source.maxApp := by simpa [decClock] using maxConst
      have clockBound := evaluate_clock_le [sourceBody]
        ((sourceArgs.reverse.take (1 + names.length)).reverse ++ (sourceSupplied ++ sourceEnv))
        (decClock (1 + names.length) source)
      rw [sourceRun] at clockBound
      have smaller : sourceFinal.clock < source.clock := by simp [decClock] at clockBound; omega
      have remainingBound : ((sourceArgs.reverse.drop (1 + names.length)).reverse).length ≤
          sourceFinal.maxApp := by
        simp only [List.length_reverse, List.length_drop, maxEq]
        omega
      cases targetResult with
      | err targetError =>
        cases sourceResult with
        | err sourceError => exact ⟨related, finalStates⟩
        | val sourceValues => simp [resultRel] at related
      | val targetValues =>
        obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value targetBody _ _ targetFinal targetValues targetRun
        cases sourceResult with
        | err sourceError => simp [resultRel] at related
        | val sourceValues =>
          obtain ⟨sourceValue, rfl⟩ := evaluate_singleton_value sourceBody _ _ sourceFinal sourceValues sourceRun
          have valueRel : ValueRel source.maxApp sourceValue targetValue := by
            simpa [resultRel, decClock] using related
          have applied := appIH sourceFinal targetFinal sourceValue targetValue
            ((sourceArgs.reverse.drop (1 + names.length)).reverse)
            ((targetArgs.reverse.drop (1 + names.length)).reverse) smaller finalStates
            (by simpa [maxEq] using valueRel) (by simpa [maxEq] using remaining) remainingBound
          simpa [maxEq] using applied

/-- Related ordinary closures preserve the result and state when applied to
related argument lists. Body evaluation and recursive application are the
induction hypotheses; recursive closures and evaluator correspondence to HOL
remain separate obligations. -/
theorem evaluateApp_closure_related {C F : Type} (source target : State C F)
    (sourceArgs targetArgs sourceSupplied targetSupplied sourceEnv targetEnv : List Value)
    (arity : Nat) (sourceBody targetBody : ClosLang.Exp)
    (names : List Basis.Pure.MlString.MlString)
    (states : StateRel source target)
    (argsRel : List.Forall₂ (ValueRel source.maxApp) sourceArgs targetArgs)
    (suppliedRel : List.Forall₂ (ValueRel source.maxApp) sourceSupplied targetSupplied)
    (envRel : List.Forall₂ (ValueRel source.maxApp) sourceEnv targetEnv)
    (bodyRel : CodeRel source.maxApp [sourceBody] [targetBody])
    (arityEq : 1 + names.length + sourceSupplied.length = arity)
    (bound : sourceArgs.length ≤ source.maxApp)
    (bodyIH : EvaluateRelBelow (C := C) (F := F) source.clock [sourceBody] [targetBody])
    (appIH : ∀ (s t : State C F) (sv tv : Value) (sa ta : List Value),
      s.clock < source.clock → StateRel s t → ValueRel s.maxApp sv tv →
      List.Forall₂ (ValueRel s.maxApp) sa ta → sa.length ≤ s.maxApp →
      resultRel (List.Forall₂ (ValueRel s.maxApp)) (ValueRel s.maxApp)
        (evaluateApps sv sa s).1 (evaluateApp none tv ta t).1 ∧
      StateRel (evaluateApps sv sa s).2 (evaluateApp none tv ta t).2) :
    resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
      (evaluateApps (.closure none [] (sourceSupplied ++ sourceEnv) 1 (mkFns names sourceBody))
        sourceArgs source).1
      (evaluateApp none (.closure none targetSupplied targetEnv arity targetBody) targetArgs target).1 ∧
    StateRel
      (evaluateApps (.closure none [] (sourceSupplied ++ sourceEnv) 1 (mkFns names sourceBody))
        sourceArgs source).2
      (evaluateApp none (.closure none targetSupplied targetEnv arity targetBody) targetArgs target).2 := by
  by_cases nonempty : targetArgs = []
  · have sourceEmpty : sourceArgs = [] := by
      have lengths := argsRel.length_eq
      simp only [nonempty, List.length_nil] at lengths
      cases sourceArgs <;> simp_all
    subst sourceArgs
    subst targetArgs
    have closureRel : ValueRel source.maxApp
        (.closure none [] (sourceSupplied ++ sourceEnv) 1 (mkFns names sourceBody))
        (.closure none targetSupplied targetEnv arity targetBody) :=
      .closure sourceSupplied targetSupplied sourceEnv targetEnv arity sourceBody targetBody
        names arityEq bodyRel envRel suppliedRel
    have nilCase := evaluateApp_nil_related source target _ _ states closureRel
    simpa [nilCase.1, nilCase.2.1] using ⟨nilCase.2.2.1, nilCase.2.2.2⟩
  · by_cases partialCount : sourceArgs.length ≤ names.length
    · exact evaluateApp_closure_partial source target sourceArgs targetArgs sourceSupplied targetSupplied
        sourceEnv targetEnv arity sourceBody targetBody names states argsRel suppliedRel envRel bodyRel
        arityEq nonempty bound partialCount
    · exact evaluateApp_closure_full_related source target sourceArgs targetArgs sourceSupplied targetSupplied
        sourceEnv targetEnv arity sourceBody targetBody names states argsRel suppliedRel envRel bodyRel
        arityEq (by omega) bound bodyIH appIH

end Flapjack.Compiler.Backend.ClosMti
