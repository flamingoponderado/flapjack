import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluateForce

/-! Application cases for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesProps

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
      forall₂_append_lists argsRel suppliedRel
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

/-- An exactly saturated ordinary closure evaluates its body with all the
arguments and supplied values in its environment. This is a property of the
Lean evaluator, whose correspondence with HOL remains open. -/
theorem evaluateApp_closure_exact {C F : Type} (state : State C F)
    (args supplied env : List Value) (arity : Nat) (body : ClosLang.Exp)
    (nonempty : args ≠ []) (bound : args.length ≤ state.maxApp)
    (exactArity : args.length + supplied.length = arity)
    (clock : args.length ≤ state.clock) :
    evaluateApp none (.closure none supplied env arity body) args state =
      evaluate [body] (args ++ supplied ++ env) (decClock args.length state) := by
  cases args with
  | nil => exact (nonempty rfl).elim
  | cons first rest =>
    have suppliedBound : supplied.length < arity := by simp only [List.length_cons] at exactArity; omega
    have needed : arity - supplied.length = (first :: rest).length := by omega
    have dest : destClosure state.maxApp none (.closure none supplied env arity body) (first :: rest) =
        some (.fullApp body ((first :: rest) ++ supplied ++ env) []) := by
      simp only [destClosure, checkLoc, bound, decide_true, Bool.true_and, suppliedBound,
        ↓reduceIte, exactArity, Nat.lt_irrefl, needed]
      simp only [← List.length_reverse (as := first :: rest), List.take_length, List.drop_length,
        List.reverse_reverse, List.reverse_nil, List.append_assoc, List.cons_append]
      rfl
    rw [evaluateApp]
    split
    · simp_all
    · simp_all
    · rename_i expression captured remaining found
      rw [dest] at found
      simp only [Option.some.injEq, AppKind.fullApp.injEq] at found
      obtain ⟨rfl, rfl, rfl⟩ := found
      simp only [List.length_nil, Nat.sub_zero, not_lt.mpr clock, ↓reduceIte, fixClock_evaluate]
      cases run : evaluate [body] ((first :: rest) ++ supplied ++ env)
          (decClock (first :: rest).length state) with
      | mk result next =>
        cases result with
        | err error => rfl
        | val values =>
          cases values with
          | nil => rfl
          | cons value tail =>
            cases tail with
            | nil => simp [evaluateApp]
            | cons other tail => rfl

/-- An exactly saturated chain of unary closures evaluates the final body
with all arguments captured. This uses the current Lean evaluator. -/
theorem evaluateApps_nestedFns_exact {C F : Type} (state : State C F)
    (args env : List Value) (names : List Basis.Pure.MlString.MlString)
    (body : ClosLang.Exp) (arity : args.length = 1 + names.length)
    (clock : args.length ≤ state.clock) (maxApp : 1 ≤ state.maxApp) :
    evaluateApps (.closure none [] env 1 (mkFns names body)) args state =
      evaluate [body] (args ++ env) (decClock args.length state) := by
  have run := evaluateApps_nestedFns_long args names body env state (by omega) (by omega) maxApp
  rw [← arity] at run
  simp only [← List.length_reverse (as := args), List.take_length, List.drop_length,
    List.reverse_reverse, List.reverse_nil] at run
  simp only [List.length_reverse] at run
  rw [run]
  cases result : evaluate [body] (args ++ env) (decClock args.length state) with
  | mk value next =>
    cases value with
    | err error => rfl
    | val values =>
      cases values with
      | nil => rfl
      | cons value tail =>
        cases tail with
        | nil => rfl
        | cons other tail => rfl

/-- Exactly saturated related closures evaluate related bodies under related
environments. The body simulation is the corresponding induction hypothesis;
the evaluator and the complete HOL theorem remain under review. -/
theorem evaluateApp_closure_exact_related_of_clock {C F : Type} (source target : State C F)
    (sourceArgs targetArgs sourceSupplied targetSupplied sourceEnv targetEnv : List Value)
    (arity : Nat) (sourceBody targetBody : ClosLang.Exp)
    (names : List Basis.Pure.MlString.MlString)
    (states : StateRel source target)
    (argsRel : List.Forall₂ (ValueRel source.maxApp) sourceArgs targetArgs)
    (suppliedRel : List.Forall₂ (ValueRel source.maxApp) sourceSupplied targetSupplied)
    (envRel : List.Forall₂ (ValueRel source.maxApp) sourceEnv targetEnv)
    (bodyRel : CodeRel source.maxApp [sourceBody] [targetBody])
    (arityEq : 1 + names.length + sourceSupplied.length = arity)
    (exactArgs : sourceArgs.length = 1 + names.length)
    (bound : sourceArgs.length ≤ source.maxApp) (clock : sourceArgs.length ≤ source.clock)
    (bodyIH : EvaluateRelAt (C := C) (F := F) [sourceBody] [targetBody]) :
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
  have targetClock : targetArgs.length ≤ target.clock := by omega
  have targetArity : targetArgs.length + targetSupplied.length = arity := by omega
  have targetNonempty : targetArgs ≠ [] := by
    intro empty
    simp only [empty, List.length_nil] at argsLength
    omega
  have clocks : StateRel (decClock sourceArgs.length source) (decClock targetArgs.length target) := by
    have related := stateRel_withClock states (source.clock - sourceArgs.length)
    simpa [decClock, agreement.1, argsLength] using related
  have environments := forall₂_append_lists argsRel (forall₂_append_lists suppliedRel envRel)
  rw [evaluateApps_nestedFns_exact source sourceArgs (sourceSupplied ++ sourceEnv) names sourceBody
    exactArgs clock (by omega),
    evaluateApp_closure_exact target targetArgs targetSupplied targetEnv arity targetBody
      targetNonempty targetBound targetArity targetClock]
  simp only [List.append_assoc]
  cases targetRun : evaluate [targetBody] (targetArgs ++ (targetSupplied ++ targetEnv))
      (decClock targetArgs.length target) with
  | mk targetResult targetFinal =>
    obtain ⟨sourceResult, sourceFinal, sourceRun, related, finalStates⟩ :=
      bodyIH _ _ _ _ _ _ targetRun (by simpa [decClock] using environments) clocks
        (by simpa [decClock] using bodyRel)
    rw [sourceRun]
    exact ⟨related, finalStates⟩

/-- Exactly saturated ordinary closure applications preserve related results
and states, including timeout. The body induction hypothesis uses the same
backward simulation interface as the other expression cases. -/
theorem evaluateApp_closure_exact_related {C F : Type} (source target : State C F)
    (sourceArgs targetArgs sourceSupplied targetSupplied sourceEnv targetEnv : List Value)
    (arity : Nat) (sourceBody targetBody : ClosLang.Exp)
    (names : List Basis.Pure.MlString.MlString)
    (states : StateRel source target)
    (argsRel : List.Forall₂ (ValueRel source.maxApp) sourceArgs targetArgs)
    (suppliedRel : List.Forall₂ (ValueRel source.maxApp) sourceSupplied targetSupplied)
    (envRel : List.Forall₂ (ValueRel source.maxApp) sourceEnv targetEnv)
    (bodyRel : CodeRel source.maxApp [sourceBody] [targetBody])
    (arityEq : 1 + names.length + sourceSupplied.length = arity)
    (exactArgs : sourceArgs.length = 1 + names.length)
    (bound : sourceArgs.length ≤ source.maxApp)
    (bodyIH : EvaluateRelAt (C := C) (F := F) [sourceBody] [targetBody]) :
    resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
      (evaluateApps (.closure none [] (sourceSupplied ++ sourceEnv) 1 (mkFns names sourceBody))
        sourceArgs source).1
      (evaluateApp none (.closure none targetSupplied targetEnv arity targetBody) targetArgs target).1 ∧
    StateRel
      (evaluateApps (.closure none [] (sourceSupplied ++ sourceEnv) 1 (mkFns names sourceBody))
        sourceArgs source).2
      (evaluateApp none (.closure none targetSupplied targetEnv arity targetBody) targetArgs target).2 := by
  by_cases clock : sourceArgs.length ≤ source.clock
  · exact evaluateApp_closure_exact_related_of_clock source target sourceArgs targetArgs sourceSupplied
      targetSupplied sourceEnv targetEnv arity sourceBody targetBody names states argsRel suppliedRel
      envRel bodyRel arityEq exactArgs bound clock bodyIH
  · obtain ⟨sourceRun, targetRun, finalStates⟩ :=
      evaluateApp_closure_full_timeout source target sourceArgs targetArgs sourceSupplied targetSupplied
        sourceEnv targetEnv arity sourceBody targetBody names states argsRel suppliedRel arityEq bound
        (by omega) (by omega)
    rw [sourceRun, targetRun]
    exact ⟨by simp [resultRel, excRel], finalStates⟩

end Flapjack.Compiler.Backend.ClosMti
