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

end Flapjack.Compiler.Backend.ClosMti
