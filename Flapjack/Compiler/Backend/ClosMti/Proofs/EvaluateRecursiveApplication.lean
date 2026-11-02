import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluateApplication

/-! Recursive closure application for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesProps

/-- Expand an application whose closure lookup selects a full application. -/
theorem evaluateApp_of_dest_full {C F : Type} (state : State C F)
    (function : Value) (args env rest : List Value) (body : ClosLang.Exp)
    (nonempty : args ≠ [])
    (found : destClosure state.maxApp none function args = some (.fullApp body env rest)) :
    evaluateApp none function args state =
      if state.clock < args.length - rest.length then
        (.err (.abort .timeoutError), { state with clock := 0 })
      else
        match evaluate [body] env (decClock (args.length - rest.length) state) with
        | (.val [value], next) => evaluateApp none value rest next
        | result => result := by
  cases args with
  | nil => exact (nonempty rfl).elim
  | cons first tail =>
    rw [evaluateApp]
    split
    · simp_all
    · simp_all
    · rename_i expression captured remaining selected
      rw [found] at selected
      simp only [Option.some.injEq, AppKind.fullApp.injEq] at selected
      obtain ⟨rfl, rfl, rfl⟩ := selected
      by_cases timeout : state.clock < (first :: tail).length - rest.length
      · simp only [List.length_cons] at timeout
        simp [timeout]
      · simp only [timeout, ↓reduceIte, fixClock_evaluate]
        cases run : evaluate [body] env (decClock ((first :: tail).length - rest.length) state) with
        | mk result next =>
          cases result with
          | err error => rfl
          | val values =>
            cases values with
            | nil => rfl
            | cons value tail => cases tail <;> rfl

/-- Once enough arguments are supplied, a recursive closure evaluates like
an ordinary closure whose environment includes all recursive bindings. This
is a Lean-evaluator property; the HOL evaluator correspondence is open. -/
theorem evaluateApp_recclosure_full_eq {C F : Type} (state : State C F)
    (args supplied env : List Value) (functions : List (Nat × ClosLang.Exp))
    (index arity : Nat) (body : ClosLang.Exp)
    (nonempty : args ≠ []) (bound : args.length ≤ state.maxApp)
    (selected : functions[index]? = some (arity, body))
    (suppliedBound : supplied.length < arity)
    (full : arity ≤ args.length + supplied.length) :
    evaluateApp none (.recclosure none supplied env functions index) args state =
      evaluateApp none (.closure none supplied
        (((List.range functions.length).map (fun i => .recclosure none [] env functions i)) ++ env)
        arity body) args state := by
  cases args with
  | nil => exact (nonempty rfl).elim
  | cons first rest =>
    have dest : destClosure state.maxApp none
        (.recclosure none supplied env functions index) (first :: rest) =
      destClosure state.maxApp none
        (.closure none supplied
          (((List.range functions.length).map (fun i => .recclosure none [] env functions i)) ++ env)
          arity body) (first :: rest) := by
      simp only [destClosure, selected, bound, checkLoc, decide_true, Bool.true_and,
        suppliedBound, ↓reduceIte, Nat.not_lt.mpr full]
      simp only [List.append_assoc]
    have found : destClosure state.maxApp none
        (.closure none supplied
          (((List.range functions.length).map (fun i => .recclosure none [] env functions i)) ++ env)
          arity body) (first :: rest) =
        some (.fullApp body
          (((first :: rest).reverse.take (arity - supplied.length)).reverse ++
            (supplied ++ ((List.range functions.length).map
              (fun i => .recclosure none [] env functions i)) ++ env))
          (((first :: rest).reverse.drop (arity - supplied.length)).reverse)) := by
      simp only [destClosure, checkLoc, bound, decide_true, Bool.true_and, suppliedBound,
        ↓reduceIte, Nat.not_lt.mpr full, List.append_assoc]
      rfl
    have recFound := dest.trans found
    rw [evaluateApp_of_dest_full state _ _ _ _ _ (by simp) recFound,
      evaluateApp_of_dest_full state _ _ _ _ _ (by simp) found]

/-- Full and over-applied recursive closures follow the ordinary closure
simulation after inserting the related recursive bindings into the body
environment. The body and subsequent application remain induction hypotheses. -/
theorem evaluateApp_recclosure_full_related {C F : Type} (source target : State C F)
    (sourceArgs targetArgs sourceSupplied targetSupplied sourceEnv targetEnv recursive : List Value)
    (functions : List (Nat × ClosLang.Exp)) (index arity : Nat)
    (sourceBody targetBody : ClosLang.Exp) (names : List Basis.Pure.MlString.MlString)
    (states : StateRel source target)
    (argsRel : List.Forall₂ (ValueRel source.maxApp) sourceArgs targetArgs)
    (suppliedRel : List.Forall₂ (ValueRel source.maxApp) sourceSupplied targetSupplied)
    (envRel : List.Forall₂ (ValueRel source.maxApp) sourceEnv targetEnv)
    (recursiveRel : List.Forall₂ (ValueRel source.maxApp) recursive
      ((List.range functions.length).map (fun i => .recclosure none [] targetEnv functions i)))
    (bodyRel : CodeRel source.maxApp [sourceBody] [targetBody])
    (selected : functions[index]? = some (arity, targetBody))
    (arityEq : 1 + names.length + sourceSupplied.length = arity)
    (full : names.length < sourceArgs.length) (bound : sourceArgs.length ≤ source.maxApp)
    (bodyIH : EvaluateRelAt (C := C) (F := F) [sourceBody] [targetBody])
    (appIH : ∀ (s t : State C F) (sv tv : Value) (sa ta : List Value),
      s.clock < source.clock → StateRel s t → ValueRel s.maxApp sv tv →
      List.Forall₂ (ValueRel s.maxApp) sa ta → sa.length ≤ s.maxApp →
      resultRel (List.Forall₂ (ValueRel s.maxApp)) (ValueRel s.maxApp)
        (evaluateApps sv sa s).1 (evaluateApp none tv ta t).1 ∧
      StateRel (evaluateApps sv sa s).2 (evaluateApp none tv ta t).2) :
    resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
      (evaluateApps (.closure none [] (sourceSupplied ++ recursive ++ sourceEnv) 1 (mkFns names sourceBody))
        sourceArgs source).1
      (evaluateApp none (.recclosure none targetSupplied targetEnv functions index) targetArgs target).1 ∧
    StateRel
      (evaluateApps (.closure none [] (sourceSupplied ++ recursive ++ sourceEnv) 1 (mkFns names sourceBody))
        sourceArgs source).2
      (evaluateApp none (.recclosure none targetSupplied targetEnv functions index) targetArgs target).2 := by
  have argsLength := argsRel.length_eq
  have suppliedLength := suppliedRel.length_eq
  have agreement := stateRel_clock_maxApp states
  have targetBound : targetArgs.length ≤ target.maxApp := by omega
  have targetSuppliedBound : targetSupplied.length < arity := by omega
  have targetFull : arity ≤ targetArgs.length + targetSupplied.length := by omega
  have targetNonempty : targetArgs ≠ [] := by
    intro empty
    simp only [empty, List.length_nil] at argsLength
    omega
  have proxy := evaluateApp_recclosure_full_eq target targetArgs targetSupplied targetEnv functions
    index arity targetBody targetNonempty targetBound selected targetSuppliedBound targetFull
  rw [proxy]
  have combined := forall₂_append_lists recursiveRel envRel
  simpa [List.append_assoc] using
    evaluateApp_closure_full_related source target sourceArgs targetArgs sourceSupplied targetSupplied
      (recursive ++ sourceEnv)
      (((List.range functions.length).map (fun i => .recclosure none [] targetEnv functions i)) ++ targetEnv)
      arity sourceBody targetBody names states argsRel suppliedRel combined bodyRel arityEq full bound bodyIH appIH

/-- Partially applying a recursive closure preserves its recursive identity
and relates the accumulated arguments to the source's unary closure chain. -/
theorem evaluateApp_recclosure_partial_related {C F : Type} (source target : State C F)
    (sourceArgs targetArgs sourceSupplied targetSupplied sourceEnv targetEnv recursive : List Value)
    (sourceFunctions targetFunctions : List (Nat × ClosLang.Exp)) (index arity : Nat)
    (sourceBody targetBody : ClosLang.Exp) (names : List Basis.Pure.MlString.MlString)
    (indexBound : index < targetFunctions.length)
    (states : StateRel source target)
    (argsRel : List.Forall₂ (ValueRel source.maxApp) sourceArgs targetArgs)
    (suppliedRel : List.Forall₂ (ValueRel source.maxApp) sourceSupplied targetSupplied)
    (envRel : List.Forall₂ (ValueRel source.maxApp) sourceEnv targetEnv)
    (functionsRel : List.Forall₂ (FunctionRel source.maxApp) sourceFunctions targetFunctions)
    (recursiveRel : List.Forall₂ (ValueRel source.maxApp) recursive
      ((List.range targetFunctions.length).map (fun i => .recclosure none [] targetEnv targetFunctions i)))
    (bodyRel : CodeRel source.maxApp [sourceBody] [targetBody])
    (selected : targetFunctions[index] = (arity, targetBody))
    (arityEq : 1 + names.length + sourceSupplied.length = arity)
    (nonempty : targetArgs ≠ []) (bound : sourceArgs.length ≤ source.maxApp)
    (partialCount : sourceArgs.length ≤ names.length) :
    resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
      (evaluateApps (.closure none [] (sourceSupplied ++ recursive ++ sourceEnv) 1 (mkFns names sourceBody))
        sourceArgs source).1
      (evaluateApp none (.recclosure none targetSupplied targetEnv targetFunctions index) targetArgs target).1 ∧
    StateRel
      (evaluateApps (.closure none [] (sourceSupplied ++ recursive ++ sourceEnv) 1 (mkFns names sourceBody))
        sourceArgs source).2
      (evaluateApp none (.recclosure none targetSupplied targetEnv targetFunctions index) targetArgs target).2 := by
  have argsLength := argsRel.length_eq
  have suppliedLength := suppliedRel.length_eq
  have agreement := stateRel_clock_maxApp states
  have targetBound : targetArgs.length ≤ target.maxApp := by omega
  have suppliedBound : targetSupplied.length < arity := by omega
  have partialBound : targetArgs.length + targetSupplied.length < arity := by omega
  have found : targetFunctions[index]? = some (arity, targetBody) := by
    rw [List.getElem?_eq_getElem indexBound, selected]
  have targetRun :
      evaluateApp none (.recclosure none targetSupplied targetEnv targetFunctions index) targetArgs target =
        if target.clock < targetArgs.length then (.err (.abort .timeoutError), { target with clock := 0 })
        else (.val [.recclosure none (targetArgs ++ targetSupplied) targetEnv targetFunctions index],
          decClock targetArgs.length target) := by
    cases targetArgs with
    | nil => exact (nonempty rfl).elim
    | cons first rest =>
      simp only [List.length_cons] at targetBound partialBound
      rw [evaluateApp]
      simp [destClosure, checkLoc, targetBound]
      split <;> simp_all
  by_cases timeout : target.clock < targetArgs.length
  · have sourceTimeout : source.clock < sourceArgs.length := by omega
    have sourceRun := evaluateApps_nestedFns_timeout sourceArgs names sourceBody
      (sourceSupplied ++ recursive ++ sourceEnv) source sourceTimeout partialCount (by omega)
    rw [sourceRun, targetRun]
    simp only [timeout, ↓reduceIte]
    exact ⟨by simp [resultRel, excRel], stateRel_withClock states 0⟩
  · have sourceClock : sourceArgs.length ≤ source.clock := by omega
    have sourceRun := evaluateApps_nestedFns_short sourceArgs names sourceBody
      (sourceSupplied ++ recursive ++ sourceEnv) source sourceClock partialCount (by omega)
    have combined := forall₂_append_lists argsRel suppliedRel
    have nextArity : 1 + (names.drop sourceArgs.length).length +
        (sourceArgs ++ sourceSupplied).length = arity := by
      simp [List.length_drop, List.length_append]
      omega
    have nextNonempty : targetArgs ++ targetSupplied ≠ [] := by
      intro empty
      have : targetArgs = [] := by simpa using (List.append_eq_nil_iff.mp empty).1
      exact nonempty this
    have nextClosure : ValueRel source.maxApp
        (.closure none [] ((sourceArgs ++ sourceSupplied) ++ recursive ++ sourceEnv) 1
          (mkFns (names.drop sourceArgs.length) sourceBody))
        (.recclosure none (targetArgs ++ targetSupplied) targetEnv targetFunctions index) :=
      .partialRecclosure (sourceArgs ++ sourceSupplied) sourceEnv sourceFunctions
        (targetArgs ++ targetSupplied) targetEnv targetFunctions index recursive
        (names.drop sourceArgs.length) sourceBody targetBody arity indexBound functionsRel envRel
        combined nextNonempty selected nextArity bodyRel recursiveRel
    rw [sourceRun, targetRun]
    simp only [timeout, ↓reduceIte]
    constructor
    · simpa [resultRel, List.append_assoc] using List.Forall₂.cons nextClosure List.Forall₂.nil
    · have clocks := stateRel_withClock states (source.clock - sourceArgs.length)
      simpa [decClock, agreement.1, argsLength] using clocks

/-- Applying a previously partially applied recursive closure preserves
related results, for any bounded argument list. Body evaluation and subsequent
application use the indicated induction hypotheses. -/
theorem evaluateApp_partialRecclosure_related {C F : Type} (source target : State C F)
    (sourceArgs targetArgs sourceSupplied targetSupplied sourceEnv targetEnv recursive : List Value)
    (sourceFunctions targetFunctions : List (Nat × ClosLang.Exp)) (index arity : Nat)
    (sourceBody targetBody : ClosLang.Exp) (names : List Basis.Pure.MlString.MlString)
    (indexBound : index < targetFunctions.length)
    (states : StateRel source target)
    (argsRel : List.Forall₂ (ValueRel source.maxApp) sourceArgs targetArgs)
    (suppliedRel : List.Forall₂ (ValueRel source.maxApp) sourceSupplied targetSupplied)
    (envRel : List.Forall₂ (ValueRel source.maxApp) sourceEnv targetEnv)
    (functionsRel : List.Forall₂ (FunctionRel source.maxApp) sourceFunctions targetFunctions)
    (recursiveRel : List.Forall₂ (ValueRel source.maxApp) recursive
      ((List.range targetFunctions.length).map (fun i => .recclosure none [] targetEnv targetFunctions i)))
    (bodyRel : CodeRel source.maxApp [sourceBody] [targetBody])
    (selected : targetFunctions[index] = (arity, targetBody))
    (arityEq : 1 + names.length + sourceSupplied.length = arity)
    (suppliedNonempty : targetSupplied ≠ []) (bound : sourceArgs.length ≤ source.maxApp)
    (bodyIH : EvaluateRelAt (C := C) (F := F) [sourceBody] [targetBody])
    (appIH : ∀ (s t : State C F) (sv tv : Value) (sa ta : List Value),
      s.clock < source.clock → StateRel s t → ValueRel s.maxApp sv tv →
      List.Forall₂ (ValueRel s.maxApp) sa ta → sa.length ≤ s.maxApp →
      resultRel (List.Forall₂ (ValueRel s.maxApp)) (ValueRel s.maxApp)
        (evaluateApps sv sa s).1 (evaluateApp none tv ta t).1 ∧
      StateRel (evaluateApps sv sa s).2 (evaluateApp none tv ta t).2) :
    resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
      (evaluateApps (.closure none [] (sourceSupplied ++ recursive ++ sourceEnv) 1 (mkFns names sourceBody))
        sourceArgs source).1
      (evaluateApp none (.recclosure none targetSupplied targetEnv targetFunctions index) targetArgs target).1 ∧
    StateRel
      (evaluateApps (.closure none [] (sourceSupplied ++ recursive ++ sourceEnv) 1 (mkFns names sourceBody))
        sourceArgs source).2
      (evaluateApp none (.recclosure none targetSupplied targetEnv targetFunctions index) targetArgs target).2 := by
  by_cases empty : targetArgs = []
  · have sourceEmpty : sourceArgs = [] := by
      have lengths := argsRel.length_eq
      simp only [empty, List.length_nil] at lengths
      cases sourceArgs <;> simp_all
    subst sourceArgs
    subst targetArgs
    have closureRel : ValueRel source.maxApp
        (.closure none [] (sourceSupplied ++ recursive ++ sourceEnv) 1 (mkFns names sourceBody))
        (.recclosure none targetSupplied targetEnv targetFunctions index) :=
      .partialRecclosure sourceSupplied sourceEnv sourceFunctions targetSupplied targetEnv targetFunctions
        index recursive names sourceBody targetBody arity indexBound functionsRel envRel suppliedRel
        suppliedNonempty selected arityEq bodyRel recursiveRel
    constructor
    · simpa [evaluateApps, evaluateApp, resultRel, List.append_assoc] using
        List.Forall₂.cons closureRel List.Forall₂.nil
    · simpa [evaluateApps, evaluateApp] using states
  · by_cases partialCount : sourceArgs.length ≤ names.length
    · exact evaluateApp_recclosure_partial_related source target sourceArgs targetArgs sourceSupplied
        targetSupplied sourceEnv targetEnv recursive sourceFunctions targetFunctions index arity
        sourceBody targetBody names indexBound states argsRel suppliedRel envRel functionsRel recursiveRel
        bodyRel selected arityEq empty bound partialCount
    · have found : targetFunctions[index]? = some (arity, targetBody) := by
        rw [List.getElem?_eq_getElem indexBound, selected]
      exact evaluateApp_recclosure_full_related source target sourceArgs targetArgs sourceSupplied
        targetSupplied sourceEnv targetEnv recursive targetFunctions index arity sourceBody targetBody
        names states argsRel suppliedRel envRel recursiveRel bodyRel found arityEq (by omega) bound bodyIH appIH

end Flapjack.Compiler.Backend.ClosMti
