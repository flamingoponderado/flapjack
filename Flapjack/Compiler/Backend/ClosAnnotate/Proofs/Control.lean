import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Safety

/-! Control-flow cases of the proof-side annotation simulation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Handlers evaluate related raised values in extended related environments. -/
theorem evaluate_handle {C F : Type} (trace : BackendCommon.Tra) (body handler : ClosLang.Exp)
    (bodyIH : EvalSimulation (C := C) (F := F) [body])
    (handlerIH : EvalSimulation (C := C) (F := F) [handler]) :
    EvalSimulation (C := C) (F := F) [.handle trace body handler] := by
  intro env source nextEnv target result sourceNext m l index run noType length vars safe code oracle states
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
      bodyIH env source nextEnv target bodyResult middle m l index bodyRun bodyNoType length bodyVars
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
              handlerIH (value :: env) middle (targetValue :: nextEnv) targetMiddle result sourceNext m (l + 1) index
                handlerRun noType handlerLength handlerVars safeParts.2 middleSafety.1 middleSafety.2 middleRel
            refine ⟨targetHandlerResult, targetLast, ?_, handlerRel, lastRel⟩
            simp only [altFree_singleton, shiftList] at targetRun targetHandlerRun
            simp only [altFree_singleton, altFreeSing, shiftList, shiftSing]
            rw [evaluate, fixClock_evaluate, targetRun]
            exact targetHandlerRun

/-- Related values have the same Boolean observation. -/
theorem valueRel_asBool {left right : Value} (related : ValueRel left right) : asBool left = asBool right := by
  cases related with
  | block tag left right entries =>
    cases entries with
    | nil => rfl
    | cons head tail => cases tag <;> simp [asBool]
  | number _ | word64 _ | byteVector _ | refPtr _ _ => rfl
  | closure => rfl
  | recclosure => rfl

/-- Conditionals evaluate the same branch after annotation. -/
theorem evaluate_if {C F : Type} (trace : BackendCommon.Tra) (condition yes no : ClosLang.Exp)
    (conditionIH : EvalSimulation (C := C) (F := F) [condition])
    (yesIH : EvalSimulation (C := C) (F := F) [yes])
    (noIH : EvalSimulation (C := C) (F := F) [no]) :
    EvalSimulation (C := C) (F := F) [.ifThenElse trace condition yes no] := by
  intro env source nextEnv target result sourceNext m l index run noType length vars safe code oracle states
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
        conditionIH env source nextEnv target (.err error) middle m l index conditionRun
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
            conditionIH env source nextEnv target (.val [value]) middle m l index conditionRun
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
                    noIH env middle nextEnv targetMiddle result sourceNext m l index branchRun noType length noVars
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
                    yesIH env middle nextEnv targetMiddle result sourceNext m l index branchRun noType length yesVars
                      safeParts.2.1 middleSafety.1 middleSafety.2 middleRel
                  refine ⟨targetBranchResult, targetLast, ?_, branchRel, lastRel⟩
                  simp only [altFree_singleton, shiftList] at targetRun targetBranchRun
                  simp only [altFree_singleton, altFreeSing, shiftList, shiftSing]
                  rw [evaluate, fixClock_evaluate, targetRun]
                  simpa [targetDecision] using targetBranchRun

end Flapjack.Compiler.Backend.ClosAnnotate
