import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluateApplication
import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluateLetrec

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

/-- The first unary call into a recursive closure is the same as calling its
selected unary body with the recursive bundle inserted into its environment. -/
theorem evaluateApps_recclosure_eq_closure {C F : Type} (state : State C F)
    (args env : List Value) (functions : List (Nat × ClosLang.Exp))
    (index : Nat) (body : ClosLang.Exp) (nonempty : args ≠ [])
    (maxApp : 1 ≤ state.maxApp) (selected : functions[index]? = some (1, body)) :
    evaluateApps (.recclosure none [] env functions index) args state =
      evaluateApps (.closure none []
        (((List.range functions.length).map (fun i => .recclosure none [] env functions i)) ++ env)
        1 body) args state := by
  induction args using List.reverseRecOn with
  | nil => exact (nonempty rfl).elim
  | append_singleton args value ih =>
    rw [evaluateApps_snoc, evaluateApps_snoc]
    rw [evaluateApp_recclosure_full_eq state [value] [] env functions index 1 body
      (by simp) (by simpa using maxApp) selected (by simp) (by simp)]

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
    (bodyIH : EvaluateRelBelow (C := C) (F := F) source.clock [sourceBody] [targetBody])
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
    (bodyIH : EvaluateRelBelow (C := C) (F := F) source.clock [sourceBody] [targetBody])
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

/-- Initial applications of related recursive closures preserve related
results and states, assuming the two smaller-clock induction hypotheses. -/
theorem evaluateApp_recclosure_related {C F : Type} (source target : State C F)
    (sourceArgs targetArgs sourceEnv targetEnv : List Value)
    (sourceFunctions targetFunctions : List (Nat × ClosLang.Exp)) (index : Nat)
    (indexBound : index < targetFunctions.length)
    (states : StateRel source target)
    (argsRel : List.Forall₂ (ValueRel source.maxApp) sourceArgs targetArgs)
    (envRel : List.Forall₂ (ValueRel source.maxApp) sourceEnv targetEnv)
    (functionsRel : List.Forall₂ (FunctionRel source.maxApp) sourceFunctions targetFunctions)
    (bound : sourceArgs.length ≤ source.maxApp)
    (bodyIH : ∀ sourceBody targetBody,
      EvaluateRelBelow (C := C) (F := F) source.clock [sourceBody] [targetBody])
    (appIH : ∀ (s t : State C F) (sv tv : Value) (sa ta : List Value),
      s.clock < source.clock → StateRel s t → ValueRel s.maxApp sv tv →
      List.Forall₂ (ValueRel s.maxApp) sa ta → sa.length ≤ s.maxApp →
      resultRel (List.Forall₂ (ValueRel s.maxApp)) (ValueRel s.maxApp)
        (evaluateApps sv sa s).1 (evaluateApp none tv ta t).1 ∧
      StateRel (evaluateApps sv sa s).2 (evaluateApp none tv ta t).2) :
    resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
      (evaluateApps (.recclosure none [] sourceEnv sourceFunctions index) sourceArgs source).1
      (evaluateApp none (.recclosure none [] targetEnv targetFunctions index) targetArgs target).1 ∧
    StateRel
      (evaluateApps (.recclosure none [] sourceEnv sourceFunctions index) sourceArgs source).2
      (evaluateApp none (.recclosure none [] targetEnv targetFunctions index) targetArgs target).2 := by
  by_cases empty : targetArgs = []
  · have sourceEmpty : sourceArgs = [] := by
      have lengths := argsRel.length_eq
      simp only [empty, List.length_nil] at lengths
      cases sourceArgs <;> simp_all
    subst sourceArgs
    subst targetArgs
    have related : ValueRel source.maxApp (.recclosure none [] sourceEnv sourceFunctions index)
        (.recclosure none [] targetEnv targetFunctions index) :=
      .recclosure sourceEnv targetEnv sourceFunctions targetFunctions index functionsRel envRel indexBound
    have nilCase := evaluateApp_nil_related source target _ _ states related
    simpa [nilCase.1, nilCase.2.1] using ⟨nilCase.2.2.1, nilCase.2.2.2⟩
  · have sourceBound : index < sourceFunctions.length := by
      have lengths := functionsRel.length_eq
      omega
    have entries : FunctionRel source.maxApp sourceFunctions[index] targetFunctions[index] :=
      functionsRel.get sourceBound indexBound
    cases sourceEntry : sourceFunctions[index] with
    | mk sourceArity sourceFunction =>
      cases targetEntry : targetFunctions[index] with
      | mk targetArity targetFunction =>
        rw [sourceEntry, targetEntry] at entries
        obtain ⟨body, names, codeRel, _, _, sourceArityEq, sourceFunctionEq, targetArityEq⟩ := entries
        dsimp only at codeRel sourceArityEq sourceFunctionEq targetArityEq
        have sourceSelected : sourceFunctions[index]? = some (1, mkFns names body) := by
          rw [List.getElem?_eq_getElem sourceBound, sourceEntry]
          simp [sourceArityEq, sourceFunctionEq]
        have targetSelected : targetFunctions[index] = (targetArity, targetFunction) := targetEntry
        have sourceNonempty : sourceArgs ≠ [] := by
          intro sourceEmpty
          have lengths := argsRel.length_eq
          simp only [sourceEmpty, List.length_nil] at lengths
          have : targetArgs = [] := by
            cases targetArgs with
            | nil => rfl
            | cons head tail => simp only [List.length_cons] at lengths; omega
          exact empty this
        have sourceMax : 1 ≤ source.maxApp := by
          have agreement := stateRel_clock_maxApp states
          omega
        have sourceEq := evaluateApps_recclosure_eq_closure source sourceArgs sourceEnv sourceFunctions
          index (mkFns names body) sourceNonempty sourceMax sourceSelected
        rw [sourceEq]
        have recursiveRel := recursiveClosures_related source.maxApp sourceFunctions targetFunctions
          sourceEnv targetEnv functionsRel envRel
        by_cases partialCount : sourceArgs.length ≤ names.length
        · have caseRel := evaluateApp_recclosure_partial_related source target sourceArgs targetArgs [] []
            sourceEnv targetEnv _ sourceFunctions targetFunctions index targetArity body targetFunction names
            indexBound states argsRel .nil envRel functionsRel recursiveRel codeRel targetSelected
            (by simp [targetArityEq, Nat.add_comm]) empty bound partialCount
          simpa using caseRel
        · have targetFound : targetFunctions[index]? = some (targetArity, targetFunction) := by
            rw [List.getElem?_eq_getElem indexBound, targetEntry]
          have caseRel := evaluateApp_recclosure_full_related source target sourceArgs targetArgs [] []
            sourceEnv targetEnv _ targetFunctions index targetArity body targetFunction names states argsRel
            .nil envRel recursiveRel codeRel targetFound (by simp [targetArityEq, Nat.add_comm])
            (by omega) bound (bodyIH body targetFunction) appIH
          simpa using caseRel

/-- Non-closure values fail application on both sides, without changing state. -/
theorem evaluateApp_badClosure_related {C F : Type} (source target : State C F)
    (sourceFunction targetFunction : Value) (sourceArgs targetArgs : List Value)
    (states : StateRel source target) (argsRel : List.Forall₂ (ValueRel source.maxApp) sourceArgs targetArgs)
    (nonempty : targetArgs ≠ [])
    (sourceBad : ∀ value, destClosure source.maxApp none sourceFunction [value] = none)
    (targetBad : destClosure target.maxApp none targetFunction targetArgs = none) :
    resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
      (evaluateApps sourceFunction sourceArgs source).1 (evaluateApp none targetFunction targetArgs target).1 ∧
    StateRel (evaluateApps sourceFunction sourceArgs source).2
      (evaluateApp none targetFunction targetArgs target).2 := by
  have sourceNonempty : sourceArgs ≠ [] := by
    intro empty
    have lengths := argsRel.length_eq
    simp only [empty, List.length_nil] at lengths
    have : targetArgs = [] := by
      cases targetArgs with
      | nil => rfl
      | cons head tail => simp only [List.length_cons] at lengths; omega
    exact nonempty this
  have sourceRun : evaluateApps sourceFunction sourceArgs source = (.err (.abort .typeError), source) := by
    induction sourceArgs using List.reverseRecOn with
    | nil => exact (sourceNonempty rfl).elim
    | append_singleton args value ih =>
      exact evaluateApps_snoc_badClosure args value sourceFunction source (sourceBad value)
  have targetRun : evaluateApp none targetFunction targetArgs target = (.err (.abort .typeError), target) := by
    cases targetArgs with
    | nil => exact (nonempty rfl).elim
    | cons first rest =>
      rw [evaluateApp]
      split <;> simp_all
  rw [sourceRun, targetRun]
  exact ⟨by simp [resultRel, excRel], states⟩

/-- Application of related values preserves related results and states,
assuming the smaller-clock body and application hypotheses. HOL evaluator
correspondence and the enclosing mutual induction remain pending. -/
theorem evaluateApp_value_related {C F : Type} (source target : State C F)
    (sourceFunction targetFunction : Value) (sourceArgs targetArgs : List Value)
    (states : StateRel source target) (functions : ValueRel source.maxApp sourceFunction targetFunction)
    (argsRel : List.Forall₂ (ValueRel source.maxApp) sourceArgs targetArgs)
    (bound : sourceArgs.length ≤ source.maxApp)
    (bodyIH : ∀ sourceBody targetBody,
      EvaluateRelBelow (C := C) (F := F) source.clock [sourceBody] [targetBody])
    (appIH : ∀ (s t : State C F) (sv tv : Value) (sa ta : List Value),
      s.clock < source.clock → StateRel s t → ValueRel s.maxApp sv tv →
      List.Forall₂ (ValueRel s.maxApp) sa ta → sa.length ≤ s.maxApp →
      resultRel (List.Forall₂ (ValueRel s.maxApp)) (ValueRel s.maxApp)
        (evaluateApps sv sa s).1 (evaluateApp none tv ta t).1 ∧
      StateRel (evaluateApps sv sa s).2 (evaluateApp none tv ta t).2) :
    resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
      (evaluateApps sourceFunction sourceArgs source).1 (evaluateApp none targetFunction targetArgs target).1 ∧
    StateRel (evaluateApps sourceFunction sourceArgs source).2
      (evaluateApp none targetFunction targetArgs target).2 := by
  by_cases empty : targetArgs = []
  · have sourceEmpty : sourceArgs = [] := by
      have lengths := argsRel.length_eq
      simp only [empty, List.length_nil] at lengths
      cases sourceArgs <;> simp_all
    subst sourceArgs
    subst targetArgs
    have nilCase := evaluateApp_nil_related source target _ _ states functions
    simpa [nilCase.1, nilCase.2.1] using ⟨nilCase.2.2.1, nilCase.2.2.2⟩
  · cases functions with
    | number value =>
      exact evaluateApp_badClosure_related source target _ _ sourceArgs targetArgs states argsRel empty
        (by intro value; rfl) (by cases targetArgs <;> rfl)
    | word64 value =>
      exact evaluateApp_badClosure_related source target _ _ sourceArgs targetArgs states argsRel empty
        (by intro value; rfl) (by cases targetArgs <;> rfl)
    | byteVector bytes =>
      exact evaluateApp_badClosure_related source target _ _ sourceArgs targetArgs states argsRel empty
        (by intro value; rfl) (by cases targetArgs <;> rfl)
    | refPtr flag address =>
      exact evaluateApp_badClosure_related source target _ _ sourceArgs targetArgs states argsRel empty
        (by intro value; rfl) (by cases targetArgs <;> rfl)
    | block tag left right related =>
      exact evaluateApp_badClosure_related source target _ _ sourceArgs targetArgs states argsRel empty
        (by intro value; rfl) (by cases targetArgs <;> rfl)
    | closure supplied₁ supplied₂ env₁ env₂ arity body₁ body₂ names arityEq code envRel suppliedRel =>
      exact evaluateApp_closure_related source target sourceArgs targetArgs supplied₁ supplied₂ env₁ env₂
        arity body₁ body₂ names states argsRel suppliedRel envRel code arityEq bound (bodyIH body₁ body₂) appIH
    | recclosure env₁ env₂ funs₁ funs₂ index funsRel envRel indexBound =>
      exact evaluateApp_recclosure_related source target sourceArgs targetArgs env₁ env₂ funs₁ funs₂ index
        indexBound states argsRel envRel funsRel bound bodyIH appIH
    | partialRecclosure supplied₁ env₁ funs₁ supplied₂ env₂ funs₂ index recursive names body₁ body₂
        arity indexBound funsRel envRel suppliedRel suppliedNonempty selected arityEq code recursiveRel =>
      exact evaluateApp_partialRecclosure_related source target sourceArgs targetArgs supplied₁ supplied₂
        env₁ env₂ recursive funs₁ funs₂ index arity body₁ body₂ names indexBound states argsRel suppliedRel
        envRel funsRel recursiveRel code selected arityEq suppliedNonempty bound (bodyIH body₁ body₂) appIH

end Flapjack.Compiler.Backend.ClosMti
