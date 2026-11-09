import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Install
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.RecursiveFunctions
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Control
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.PureBindings

/-! State-local steps for the evaluator induction. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.DbVars
open Flapjack.Compiler.Backend.ClosLang
open Flapjack.SemanticPrimitivesHOL (Result)

theorem evaluate_ordinary_op_step {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (args : List ClosLang.Exp) (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (source : State C F) (argsIH : EvalSimulationAt source args)
    (primitive : PrimitiveSimulation (C := C) (F := F) op) :
    EvalSimulationAt source [.op trace op args] := by
  intro env nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  have argsVars : ∀ n, altFv n args = true → EnvOk m l index env nextEnv n := by
    intro n present
    apply vars n
    simpa [altFv_op] using present
  have argsSafe : everyFnVarsNone args := by simpa [everyFnVarsNone, fnVarsNoneExp] using safe
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error =>
      rw [FlatToClos.evaluate_op_error args env source middle error trace op argsRun] at run
      cases run
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        argsIH env nextEnv target (.err error) sourceNext m l index argsRun noType length argsVars
          argsSafe code oracle states
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
        rw [altFree_op]
        simp only [shiftList, shiftSing]
        exact FlatToClos.evaluate_op_error _ _ _ _ _ _ _ targetRun
    | val values =>
      have valuesNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        argsIH env nextEnv target (.val values) middle m l index argsRun valuesNoType length argsVars
          argsSafe code oracle states
      cases targetResult with
      | err error => cases error <;> simp [ResultRel] at resultRel
      | val targetValues =>
        obtain ⟨outcome, appRun, appRel⟩ := primitive values.reverse targetValues.reverse middle targetMiddle
          (List.forall₂_reverse_iff.mpr resultRel) middleRel
        cases sourceApp : doApp op values.reverse middle with
        | err error =>
          cases outcome with
          | val pair => simp [AppResultRel, sourceApp] at appRel
          | err targetError =>
            rw [evaluate_ordinary_op_values trace op args env source middle values notInstall notForce argsRun, sourceApp] at run
            cases run
            refine ⟨.err targetError, targetMiddle, ?_, ?_, middleRel⟩
            · rw [altFree_op]
              simp only [shiftList, shiftSing]
              rw [evaluate_ordinary_op_values _ _ _ _ _ _ _ notInstall notForce targetRun, appRun]
            · simpa [AppResultRel, sourceApp] using appRel
        | val pair =>
          obtain ⟨value, last⟩ := pair
          cases outcome with
          | err error => simp [AppResultRel, sourceApp] at appRel
          | val targetPair =>
            obtain ⟨targetValue, targetLast⟩ := targetPair
            have related : ValueRel value targetValue ∧ StateRel last targetLast := by
              simpa [AppResultRel, sourceApp] using appRel
            rw [evaluate_ordinary_op_values trace op args env source middle values notInstall notForce argsRun, sourceApp] at run
            cases run
            refine ⟨.val [targetValue], targetLast, ?_, .cons related.1 .nil, related.2⟩
            rw [altFree_op]
            simp only [shiftList, shiftSing]
            rw [evaluate_ordinary_op_values _ _ _ _ _ _ _ notInstall notForce targetRun, appRun]

/-- All ordinary primitives have a state-local simulation step. -/
theorem evaluate_ordinary_all_step {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (args : List ClosLang.Exp) (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (source : State C F) (argsIH : EvalSimulationAt source args) :
    EvalSimulationAt source [.op trace op args] :=
  evaluate_ordinary_op_step trace op args notInstall notForce source argsIH
    (primitiveSimulation_ordinary op notInstall notForce)

theorem evaluate_raise_step {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (source : State C F) (bodyIH : EvalSimulationAt source [body]) :
    EvalSimulationAt source [.raise trace body] := by
  intro env nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  have bodyVars : ∀ n, altFv n [body] = true → EnvOk m l index env nextEnv n := by
    intro n present
    apply vars n
    simpa [altFv_raise] using present
  have bodySafe : everyFnVarsNone [body] := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using safe
  cases bodyRun : evaluate [body] env source with
  | mk bodyResult bodyNext =>
    cases bodyResult with
    | err error =>
      simp [evaluate, bodyRun] at run
      obtain ⟨rfl, rfl⟩ := run
      obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
        bodyIH env nextEnv target (.err error) bodyNext m l index
          bodyRun noType length bodyVars bodySafe code oracle states
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetNext, ?_, resultRel, nextRel⟩
        simp only [altFree_singleton, shiftList] at targetRun
        simp [altFree_singleton, altFreeSing, shiftList, shiftSing, evaluate, targetRun]
    | val values =>
      have valueLength := (evaluate_length (C := C) (F := F)).1 [body] env source bodyNext values bodyRun
      have bodyNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
        bodyIH env nextEnv target (.val values) bodyNext m l index
          bodyRun bodyNoType length bodyVars bodySafe code oracle states
      cases values with
      | nil => simp at valueLength
      | cons value tail =>
        cases tail with
        | cons first rest => simp at valueLength
        | nil =>
          cases targetResult with
          | err error => cases error <;> simp [ResultRel] at resultRel
          | val targetValues =>
            cases resultRel with
            | cons valueRel restRel =>
              cases restRel
              simp [evaluate, bodyRun] at run
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨.err (.raise _), targetNext, ?_, valueRel, nextRel⟩
              simp only [altFree_singleton, shiftList] at targetRun
              simp [altFree_singleton, altFreeSing, shiftList, shiftSing, evaluate, targetRun]


theorem evaluate_tick_step {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (source : State C F) (bodyIH : EvalSimulationAt (decClock 1 source) [body]) :
    EvalSimulationAt source [.tick trace body] := by
  intro env nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  have bodyVars : ∀ n, altFv n [body] = true → EnvOk m l index env nextEnv n := by
    intro n present
    apply vars n
    simpa [altFv_tick] using present
  have bodySafe : everyFnVarsNone [body] := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using safe
  by_cases zero : source.clock = 0
  · have targetZero : target.clock = 0 := by rw [← states.1]; exact zero
    simp [evaluate, zero] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨.err (.abort .timeoutError), target, ?_, rfl, states⟩
    simp [altFree_singleton, altFreeSing, shiftList, shiftSing, evaluate, targetZero]
  · have targetNonzero : target.clock ≠ 0 := by rw [← states.1]; exact zero
    have clocks : StateRel (decClock 1 source) (decClock 1 target) := by
      simpa [decClock, ← states.1] using stateRel_withClock states (source.clock - 1)
    have bodyRun : evaluate [body] env (decClock 1 source) = (result, sourceNext) := by
      simpa [evaluate, zero] using run
    obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
      bodyIH env nextEnv (decClock 1 target) result sourceNext m l index
        bodyRun noType length bodyVars bodySafe (by simpa [CodeSafe, decClock] using code)
        (by simpa [OracleSafe, decClock] using oracle) clocks
    refine ⟨targetResult, targetNext, ?_, resultRel, nextRel⟩
    simpa [altFree_singleton, altFreeSing, shiftList, shiftSing, evaluate, targetNonzero] using targetRun


theorem evaluate_letrec_step {C F : Type} (names : List Flapjack.Basis.Pure.MlString.MlString)
    (location : Option Nat) (selected : Option (List Nat)) (functions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (source : State C F) (bodyIH : EvalSimulationAt source [body]) :
    EvalSimulationAt source [.letrec names location selected functions body] := by
  intro env nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  have safeParts : selected = none ∧ fnVarsNoneFuns functions ∧ everyFnVarsNone [body] := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using safe
  have selectedNone := safeParts.1
  subst selected
  have funSafe : ∀ arity exp, (arity, exp) ∈ functions → everyFnVarsNone [exp] := by
    intro arity exp member
    exact recursiveFunction_safe functions safeParts.2.1 arity exp member
  let live := varsToList (listMkUnion ((altFreeFuns functions.length functions).map Prod.snd))
  let compact := live.filter (· < m + l)
  let nextFunctions := shiftFuns functions.length (m + l) (shiftedEnv 0 compact)
    ((altFreeFuns functions.length functions).map Prod.fst)
  obtain ⟨captured, captureRun, functionsRel⟩ :=
    recursiveFunctions_capture names location none functions body m l index env nextEnv length funSafe vars
  have nextLength : nextFunctions.length = functions.length := by
    simp [nextFunctions, shiftFuns_length, altFreeFuns_length]
  have arities := functionsRel_arities env captured functions.length functions nextFunctions functionsRel
  have validity : functions.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) =
      nextFunctions.all (fun (arity, _) => arity ≤ target.maxApp && arity != 0) := by
    have maxEq := states.2.2.1
    rw [← maxEq]
    have h := congrArg (fun xs : List Nat => xs.all (fun arity => arity ≤ source.maxApp && arity != 0)) arities
    simpa only [List.all_map, Function.comp_def] using h
  by_cases valid : functions.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true
  · have targetValid : nextFunctions.all (fun (arity, _) => arity ≤ target.maxApp && arity != 0) = true := by
      rw [← validity]; exact valid
    let front := (List.range functions.length).map (fun i => Value.recclosure location [] env functions i)
    let nextFront := (List.range functions.length).map (fun i => Value.recclosure location [] captured nextFunctions i)
    have bodyRun : evaluate [body] (front ++ env) source = (result, sourceNext) := by
      simpa [evaluate, valid, front] using run
    have bodyLength : (front ++ env).length = m + (l + functions.length) := by
      simp [front, length]; omega
    have bodyVars : ∀ n, altFv n [body] = true →
        EnvOk m (l + functions.length) index (front ++ env) (nextFront ++ nextEnv) n := by
      intro n present
      exact envOk_recursive_body names location none functions nextFunctions body m l index env nextEnv captured
        functionsRel vars n present
    obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
      bodyIH (front ++ env) (nextFront ++ nextEnv) target result sourceNext m (l + functions.length) index
        bodyRun noType bodyLength bodyVars safeParts.2.2 code oracle states
    refine ⟨targetResult, targetNext, ?_, resultRel, nextRel⟩
    rw [altFree_letrec]
    simp only [altFree_singleton, Flapjack.holHd, shiftList, shiftSing, List.length_map, Option.getD_some]
    have funEq : functions.map (fun x =>
        ((x.1, (altFreeSing x.2).1), DbVarSet.shift (x.1 + functions.length) (altFreeSing x.2).2)) =
        altFreeFuns functions.length functions := by
      simpa [altFree_singleton, Flapjack.holHd] using (altFreeFuns_as_map functions.length functions).symm
    rw [funEq]
    change evaluate [.letrec names location (some (compact.map (getVar m l index))) nextFunctions
      (shiftSing (altFreeSing body).1 m (l + functions.length) index)] nextEnv target = _
    change lookupVars (compact.map (getVar m l index)) nextEnv = some captured at captureRun
    simp only [evaluate, targetValid, if_true, captureRun]
    simpa [altFree_singleton, shiftList, nextFront, nextLength] using targetRun
  · simp [evaluate, valid] at run
    exact False.elim (noType run.1.symm)


theorem evaluate_handle_step {C F : Type} (trace : BackendCommon.Tra) (body handler : ClosLang.Exp)
    (source : State C F) (bodyIH : EvalSimulationAt source [body])
    (handlerIH : ∀ state : State C F, state.clock ≤ source.clock → EvalSimulationAt state [handler]) :
    EvalSimulationAt source [.handle trace body handler] := by
  intro env nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  have safeParts : everyFnVarsNone [body] ∧ everyFnVarsNone [handler] := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using safe
  have bodyVars : ∀ n, altFv n [body] = true → EnvOk m l index env nextEnv n := by
    intro n present
    apply vars n
    rw [altFv_handle]
    simp [present]
  cases bodyRun : evaluate [body] env source with
  | mk bodyResult middle =>
    have bodyNoType : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      rw [evaluate, fixClock_evaluate, bodyRun] at run
      cases run
      exact noType rfl
    obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
      bodyIH env nextEnv target bodyResult middle m l index bodyRun bodyNoType length bodyVars
        safeParts.1 code oracle states
    cases bodyResult with
    | val values =>
      cases targetResult with
      | err error => cases error <;> simp [ResultRel] at resultRel
      | val targetValues =>
        rw [evaluate, fixClock_evaluate, bodyRun] at run
        cases run
        refine ⟨.val targetValues, targetMiddle, ?_, resultRel, middleRel⟩
        simp only [altFree_singleton, shiftList] at targetRun
        simp only [altFree_singleton, altFreeSing, shiftList, shiftSing]
        rw [evaluate, fixClock_evaluate, targetRun]
    | err error =>
      cases error with
      | abort reason =>
        cases targetResult with
        | val values => simp [ResultRel] at resultRel
        | err targetError =>
          cases targetError with
          | raise value => simp [ResultRel] at resultRel
          | abort targetReason =>
            rw [evaluate, fixClock_evaluate, bodyRun] at run
            cases run
            refine ⟨.err (.abort targetReason), targetMiddle, ?_, resultRel, middleRel⟩
            simp only [altFree_singleton, shiftList] at targetRun
            simp only [altFree_singleton, altFreeSing, shiftList, shiftSing]
            rw [evaluate, fixClock_evaluate, targetRun]
      | raise value =>
        cases targetResult with
        | val values => simp [ResultRel] at resultRel
        | err targetError =>
          cases targetError with
          | abort reason => simp [ResultRel] at resultRel
          | raise targetValue =>
            have valueRel : ValueRel value targetValue := resultRel
            have handlerVars : ∀ n, altFv n [handler] = true →
                EnvOk m (l + 1) index (value :: env) (targetValue :: nextEnv) n := by
              intro n present
              have headRel : List.Forall₂ ValueRel [value] [targetValue] := .cons valueRel .nil
              have extended := envOk_extend m l index [value] [targetValue] env nextEnv n headRel
                (by
                  intro lower
                  apply vars (n - 1)
                  rw [altFv_handle]
                  have equal : n - 1 + 1 = n := by simp at lower; omega
                  simp [equal, present])
              simpa using extended
            have handlerLength : (value :: env).length = m + (l + 1) := by simp; omega
            have middleSafety := (evaluate_preserves_safe.1 [body]) env source (.err (.raise value)) middle
              bodyRun code oracle
            have handlerRun : evaluate [handler] (value :: env) middle = (result, sourceNext) := by
              rw [evaluate, fixClock_evaluate, bodyRun] at run
              exact run
            obtain ⟨targetHandlerResult, targetLast, targetHandlerRun, handlerRel, lastRel⟩ :=
              (handlerIH middle (by have h := evaluate_clock_le [body] env source; simpa [bodyRun] using h)) (value :: env) (targetValue :: nextEnv) targetMiddle result sourceNext m (l + 1) index
                handlerRun noType handlerLength handlerVars safeParts.2 middleSafety.1 middleSafety.2 middleRel
            refine ⟨targetHandlerResult, targetLast, ?_, handlerRel, lastRel⟩
            simp only [altFree_singleton, shiftList] at targetRun targetHandlerRun
            simp only [altFree_singleton, altFreeSing, shiftList, shiftSing]
            rw [evaluate, fixClock_evaluate, targetRun]
            exact targetHandlerRun


theorem evaluate_if_step {C F : Type} (trace : BackendCommon.Tra) (condition yes no : ClosLang.Exp)
    (source : State C F) (conditionIH : EvalSimulationAt source [condition])
    (yesIH : ∀ state : State C F, state.clock ≤ source.clock → EvalSimulationAt state [yes])
    (noIH : ∀ state : State C F, state.clock ≤ source.clock → EvalSimulationAt state [no]) :
    EvalSimulationAt source [.ifThenElse trace condition yes no] := by
  intro env nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  have safeParts : everyFnVarsNone [condition] ∧ everyFnVarsNone [yes] ∧ everyFnVarsNone [no] := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using safe
  have condVars : ∀ n, altFv n [condition] = true → EnvOk m l index env nextEnv n := by
    intro n present
    apply vars n
    rw [altFv_if]
    simp [present]
  have yesVars : ∀ n, altFv n [yes] = true → EnvOk m l index env nextEnv n := by
    intro n present
    apply vars n
    rw [altFv_if]
    simp [present]
  have noVars : ∀ n, altFv n [no] = true → EnvOk m l index env nextEnv n := by
    intro n present
    apply vars n
    rw [altFv_if]
    simp [present]
  cases conditionRun : evaluate [condition] env source with
  | mk conditionResult middle =>
    cases conditionResult with
    | err error =>
      rw [evaluate, fixClock_evaluate, conditionRun] at run
      cases run
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        conditionIH env nextEnv target (.err error) middle m l index conditionRun
          noType length condVars safeParts.1 code oracle states
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
        simp only [altFree_singleton, shiftList] at targetRun
        simp only [altFree_singleton, altFreeSing, shiftList, shiftSing]
        rw [evaluate, fixClock_evaluate, targetRun]
    | val values =>
      have valueLength := (evaluate_length (C := C) (F := F)).1 [condition] env source middle values conditionRun
      cases values with
      | nil => simp at valueLength
      | cons value tail =>
        cases tail with
        | cons other tail => simp at valueLength
        | nil =>
          have condNoType : (Result.val [value] : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
          obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
            conditionIH env nextEnv target (.val [value]) middle m l index conditionRun
              condNoType length condVars safeParts.1 code oracle states
          cases targetResult with
          | err error => cases error <;> simp [ResultRel] at resultRel
          | val targetValues =>
            cases resultRel with
            | cons valueRel restRel =>
              cases restRel
              rename_i targetValue
              have boolEq := valueRel_asBool valueRel
              have middleSafety := (evaluate_preserves_safe.1 [condition]) env source (.val [value]) middle
                conditionRun code oracle
              cases decision : asBool value with
              | none =>
                rw [evaluate, fixClock_evaluate, conditionRun] at run
                simp [decision] at run
                exact False.elim (noType run.1.symm)
              | some flag =>
                have targetDecision : asBool targetValue = some flag := by rw [← boolEq]; exact decision
                cases flag with
                | false =>
                  have branchRun : evaluate [no] env middle = (result, sourceNext) := by
                    rw [evaluate, fixClock_evaluate, conditionRun] at run
                    simpa [decision] using run
                  obtain ⟨targetBranchResult, targetLast, targetBranchRun, branchRel, lastRel⟩ :=
                    (noIH middle (by have h := evaluate_clock_le [condition] env source; simpa [conditionRun] using h)) env nextEnv targetMiddle result sourceNext m l index branchRun noType length noVars
                      safeParts.2.2 middleSafety.1 middleSafety.2 middleRel
                  refine ⟨targetBranchResult, targetLast, ?_, branchRel, lastRel⟩
                  simp only [altFree_singleton, shiftList] at targetRun targetBranchRun
                  simp only [altFree_singleton, altFreeSing, shiftList, shiftSing]
                  rw [evaluate, fixClock_evaluate, targetRun]
                  simpa [targetDecision] using targetBranchRun
                | true =>
                  have branchRun : evaluate [yes] env middle = (result, sourceNext) := by
                    rw [evaluate, fixClock_evaluate, conditionRun] at run
                    simpa [decision] using run
                  obtain ⟨targetBranchResult, targetLast, targetBranchRun, branchRel, lastRel⟩ :=
                    (yesIH middle (by have h := evaluate_clock_le [condition] env source; simpa [conditionRun] using h)) env nextEnv targetMiddle result sourceNext m l index branchRun noType length yesVars
                      safeParts.2.1 middleSafety.1 middleSafety.2 middleRel
                  refine ⟨targetBranchResult, targetLast, ?_, branchRel, lastRel⟩
                  simp only [altFree_singleton, shiftList] at targetRun targetBranchRun
                  simp only [altFree_singleton, altFreeSing, shiftList, shiftSing]
                  rw [evaluate, fixClock_evaluate, targetRun]
                  simpa [targetDecision] using targetBranchRun


theorem evaluate_let_step {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp)
    (source : State C F) (bindingsIH : EvalSimulationAt source bindings)
    (bodyIH : ∀ state : State C F, state.clock ≤ source.clock → EvalSimulationAt state [body]) :
    EvalSimulationAt source [.let trace bindings body] := by
  intro env nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  have safeParts : everyFnVarsNone bindings ∧ everyFnVarsNone [body] := by
    simpa [everyFnVarsNone, fnVarsNoneExp, and_comm] using safe
  by_cases optimized : (noOverlap bindings.length (altFree [body]).2 && pureList bindings) = true
  · have unused : noOverlap bindings.length (altFree [body]).2 = true := (Bool.and_eq_true_iff.mp optimized).1
    have pure : pureList bindings = true := (Bool.and_eq_true_iff.mp optimized).2
    cases bindingsRun : evaluate bindings env source with
    | mk bindingsResult middle =>
      have bindingsNoType : bindingsResult ≠ .err (.abort .typeError) := by
        intro bad
        subst bindingsResult
        rw [evaluate, fixClock_evaluate, bindingsRun] at run
        cases run
        exact noType rfl
      obtain ⟨values, resultEq, stateEq, valuesLength⟩ :=
        evaluate_pure_length bindings env source middle bindingsResult pure bindingsRun bindingsNoType
      subst bindingsResult
      subst middle
      have bodyRun : evaluate [body] (values ++ env) source = (result, sourceNext) := by
        rw [evaluate, fixClock_evaluate, bindingsRun] at run
        exact run
      have bodyVars : ∀ n, altFv n [body] = true →
          EnvOk m (l + bindings.length) index (values ++ env)
            (List.replicate bindings.length (.number 0) ++ nextEnv) n := by
        intro n present
        exact envOk_unused_bindings trace bindings body m l index env nextEnv values
          valuesLength pure unused vars n present
      have bodyLength : (values ++ env).length = m + (l + bindings.length) := by
        simp only [List.length_append, valuesLength, length]; omega
      obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
        (bodyIH source (by omega)) (values ++ env) (List.replicate bindings.length (.number 0) ++ nextEnv)
          target result sourceNext m (l + bindings.length) index bodyRun noType bodyLength bodyVars
          safeParts.2 code oracle states
      refine ⟨targetResult, targetNext, ?_, resultRel, nextRel⟩
      rw [altFree_let, if_pos optimized]
      simp only [altFree_singleton, Flapjack.holHd, shiftList, shiftSing, List.length_replicate] at targetRun ⊢
      rw [evaluate, fixClock_evaluate, evaluate_shift_replicate_const0]
      exact targetRun
  · have bindingsVars : ∀ n, altFv n bindings = true → EnvOk m l index env nextEnv n := by
      intro n present
      apply vars n
      rw [altFv_let]
      have noOpt : (noOverlap bindings.length (altFreeList [body]).2 && pureList bindings) ≠ true := optimized
      simp [noOpt, present]
    cases bindingsRun : evaluate bindings env source with
    | mk bindingsResult middle =>
      cases bindingsResult with
      | err error =>
        rw [evaluate, fixClock_evaluate, bindingsRun] at run
        cases run
        obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
          bindingsIH env nextEnv target (.err error) middle m l index bindingsRun
            noType length bindingsVars safeParts.1 code oracle states
        cases targetResult with
        | val values => cases error <;> simp [ResultRel] at resultRel
        | err targetError =>
          refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
          rw [altFree_let, if_neg optimized]
          simp only [altFree_singleton, Flapjack.holHd, shiftList, shiftSing]
          rw [evaluate, fixClock_evaluate, targetRun]
      | val values =>
        have valuesLength := (evaluate_length (C := C) (F := F)).1 bindings env source middle values bindingsRun
        have bindingNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
        obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
          bindingsIH env nextEnv target (.val values) middle m l index bindingsRun
            bindingNoType length bindingsVars safeParts.1 code oracle states
        cases targetResult with
        | err error => cases error <;> simp [ResultRel] at resultRel
        | val targetValues =>
          have bodyVars : ∀ n, altFv n [body] = true →
              EnvOk m (l + bindings.length) index (values ++ env) (targetValues ++ nextEnv) n := by
            intro n present
            have extended := envOk_extend m l index values targetValues env nextEnv n resultRel (by
              intro lower
              apply vars (n - values.length)
              rw [altFv_let]
              have shifted : n - values.length + bindings.length = n := by omega
              have noOpt : (noOverlap bindings.length (altFreeList [body]).2 && pureList bindings) ≠ true := optimized
              simp [noOpt, shifted, present])
            simpa [valuesLength] using extended
          have bodyLength : (values ++ env).length = m + (l + bindings.length) := by
            simp only [List.length_append, valuesLength, length]; omega
          have bodyRun : evaluate [body] (values ++ env) middle = (result, sourceNext) := by
            rw [evaluate, fixClock_evaluate, bindingsRun] at run
            exact run
          have middleSafety := (evaluate_preserves_safe.1 bindings) env source (.val values) middle
            bindingsRun code oracle
          obtain ⟨targetBodyResult, targetNext, targetBodyRun, bodyRel, nextRel⟩ :=
            (bodyIH middle (by have h := evaluate_clock_le bindings env source; simpa [bindingsRun] using h)) (values ++ env) (targetValues ++ nextEnv) targetMiddle result sourceNext
              m (l + bindings.length) index bodyRun noType bodyLength bodyVars safeParts.2
              middleSafety.1 middleSafety.2 middleRel
          refine ⟨targetBodyResult, targetNext, ?_, bodyRel, nextRel⟩
          rw [altFree_let, if_neg optimized]
          simp only [altFree_singleton, Flapjack.holHd, shiftList, shiftSing] at targetBodyRun ⊢
          rw [evaluate, fixClock_evaluate, targetRun]
          simpa [altFree, altFreeList_length] using targetBodyRun


theorem evaluate_cons_step {C F : Type} (first second : ClosLang.Exp) (rest : List ClosLang.Exp)
    (source : State C F) (firstIH : EvalSimulationAt source [first])
    (restIH : ∀ state : State C F, state.clock ≤ source.clock → EvalSimulationAt state (second :: rest)) :
    EvalSimulationAt source (first :: second :: rest) := by
  intro env nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  have firstVars : ∀ n, altFv n [first] = true → EnvOk m l index env nextEnv n := by
    intro n present
    apply vars n
    rw [altFv_cons]
    simp [present]
  have restVars : ∀ n, altFv n (second :: rest) = true → EnvOk m l index env nextEnv n := by
    intro n present
    apply vars n
    rw [altFv_cons]
    simp [present]
  have safety : everyFnVarsNone [first] ∧ everyFnVarsNone (second :: rest) := by
    simpa [everyFnVarsNone] using safe
  cases firstRun : evaluate [first] env source with
  | mk firstResult middle =>
    cases firstResult with
    | err error =>
      have fullRun := ClosProps.evaluate_cons_error first (second :: rest) env source middle error firstRun
      rw [fullRun] at run
      cases run
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        firstIH env nextEnv target (.err error) sourceNext m l index
          firstRun noType length firstVars safety.1 code oracle states
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
        simp only [altFree_singleton, shiftList] at targetRun
        simp only [altFree, altFreeList, shiftList]
        exact ClosProps.evaluate_cons_error _ _ _ _ _ _ targetRun
    | val values =>
      have valueLength := (evaluate_length (C := C) (F := F)).1 [first] env source middle values firstRun
      cases values with
      | nil => simp at valueLength
      | cons value tail =>
        cases tail with
        | cons other tail => simp at valueLength
        | nil =>
          have firstNoType : (Result.val [value] : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
          obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
            firstIH env nextEnv target (.val [value]) middle m l index
              firstRun firstNoType length firstVars safety.1 code oracle states
          cases targetResult with
          | err error => cases error <;> simp [ResultRel] at resultRel
          | val targetValues =>
            cases resultRel with
            | cons valueRel tailRel =>
              cases tailRel
              rename_i targetValue
              have middleSafety := (evaluate_preserves_safe.1 [first]) env source (.val [value]) middle firstRun code oracle
              cases restRun : evaluate (second :: rest) env middle with
              | mk restResult last =>
                have fullRun := ClosProps.evaluate_cons_value first (second :: rest) env source middle value firstRun
                rw [restRun] at fullRun
                cases restResult with
                | err error =>
                  simp only at fullRun
                  rw [fullRun] at run
                  cases run
                  obtain ⟨targetRestResult, targetLast, targetRestRun, restRel, lastRel⟩ :=
                    (restIH middle (by have h := evaluate_clock_le [first] env source; simpa [firstRun] using h)) env nextEnv targetMiddle (.err error) sourceNext m l index
                      restRun noType length restVars safety.2 middleSafety.1 middleSafety.2 middleRel
                  cases targetRestResult with
                  | val values => cases error <;> simp [ResultRel] at restRel
                  | err targetError =>
                    refine ⟨.err targetError, targetLast, ?_, restRel, lastRel⟩
                    simp only [altFree_singleton, shiftList] at targetRun
                    simp only [altFree, altFreeList, shiftList] at targetRestRun ⊢
                    rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ targetRun, targetRestRun]

                | val values =>
                  simp only at fullRun
                  rw [fullRun] at run
                  cases run
                  have restNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
                  obtain ⟨targetRestResult, targetLast, targetRestRun, restRel, lastRel⟩ :=
                    (restIH middle (by have h := evaluate_clock_le [first] env source; simpa [firstRun] using h)) env nextEnv targetMiddle (.val values) sourceNext m l index
                      restRun restNoType length restVars safety.2 middleSafety.1 middleSafety.2 middleRel
                  cases targetRestResult with
                  | err error => cases error <;> simp [ResultRel] at restRel
                  | val targetValues =>
                    refine ⟨.val (targetValue :: targetValues), targetLast, ?_, .cons valueRel restRel, lastRel⟩
                    simp only [altFree_singleton, shiftList] at targetRun
                    simp only [altFree, altFreeList, shiftList] at targetRestRun ⊢
                    rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ targetRun, targetRestRun]



end Flapjack.Compiler.Backend.ClosAnnotate
