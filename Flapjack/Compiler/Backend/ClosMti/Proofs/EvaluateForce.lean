module

public import Flapjack.Compiler.Backend.ClosMti.Proofs.PrimitiveThunk

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section

/-! Forced thunk evaluation for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesProps

/-- A successfully inspected thunk must be named by a single unflagged
reference. -/
theorem destThunk_isThunk_shape (values : List Value) (refs : HolFiniteMapExact Nat (Ref Value))
    (mode : AstHOL.ThunkMode) (value : Value)
    (run : destThunk values refs = .isThunk mode value) :
    ∃ ptr, values = [.refPtr false ptr] := by
  cases values with
  | nil => simp [destThunk] at run
  | cons first rest =>
    cases rest with
    | cons second tail => simp [destThunk] at run
    | nil =>
      cases first <;> try simp [destThunk] at run
      case refPtr flag ptr =>
        cases flag <;> simp_all
        all_goals split at run <;> simp_all

/-- The evaluator's generated unary force application is preserved by the
multi-argument pass. -/
theorem forceApplication_codeRel (maxApp : Nat) :
    CodeRel maxApp [appUnit (.var .none 0)] [appUnit (.var .none 0)] := by
  simp [CodeRel, appUnit, ClosProps.noMti, ClosProps.noMtiList, introList,
    introExp_app_none, collectApps, introExp_var, introExp_op]

/-- Updating a forced thunk on related argument and result lists fails
together or produces related states. -/
theorem updateThunk_lists_related {C F : Type} (source target : State C F)
    (sourcePointers targetPointers sourceValues targetValues : List Value)
    (states : StateRel source target)
    (pointers : List.Forall₂ (ValueRel source.maxApp) sourcePointers targetPointers)
    (values : List.Forall₂ (ValueRel source.maxApp) sourceValues targetValues) :
    (updateThunk targetPointers target.refs targetValues = none →
      updateThunk sourcePointers source.refs sourceValues = none) ∧
    (∀ targetRefs, updateThunk targetPointers target.refs targetValues = some targetRefs →
      ∃ sourceRefs, updateThunk sourcePointers source.refs sourceValues = some sourceRefs ∧
        StateRel { source with refs := sourceRefs } { target with refs := targetRefs }) := by
  cases pointers with
  | nil => simp [updateThunk]
  | cons head tail =>
    cases tail with
    | cons second rest => cases head <;> simp [updateThunk]
    | nil =>
      cases head with
      | refPtr flag ptr => exact updateThunk_related states values flag ptr
      | number _ | word64 _ | block _ _ _ _ | byteVector _ | closure | recclosure | partialRecclosure =>
        simp [updateThunk]

/-- Continue a force operation after evaluating its argument list. -/
noncomputable def runForced {C F : Type} (values : List Value) (state : State C F) : EvalResult C F :=
  match destThunk values state.refs with
  | .badRef | .notThunk => (.err (.abort .typeError), state)
  | .isThunk .evaluated value => (.val [value], state)
  | .isThunk .notEvaluated value =>
    let (result, last) := evaluate [appUnit (.var .none 0)] [value] state
    match result with
    | .err error => (.err error, last)
    | .val forced => match updateThunk values last.refs forced with
      | none => (.err (.abort .typeError), last)
      | some refs => (.val forced, { last with refs := refs })

/-- Force expressions first evaluate their arguments, then inspect the thunk. -/
theorem evaluate_force_eq {C F : Type} (trace : BackendCommon.Tra) (args : List ClosLang.Exp)
    (env : List Value) (state : State C F) :
    evaluate [.op trace (.thunkOp .forceThunk) args] env state =
      match evaluate args env state with
      | (.err error, next) => (.err error, next)
      | (.val values, next) => runForced values next := by
  rw [evaluate, fixClock_evaluate]
  cases evaluated : evaluate args env state with
  | mk result next =>
    cases result with
    | err error => rfl
    | val values =>
      dsimp only
      unfold runForced
      split <;> simp_all
      split <;> simp_all
      split <;> simp_all

/-- A target bad-reference result can only relate to the same source case. -/
theorem destThunkRel_target_badRef {maxApp : Nat} {source : DestThunkResult}
    (related : DestThunkRel maxApp source .badRef) : source = .badRef := by
  cases related
  rfl

/-- A target non-thunk result can only relate to the same source case. -/
theorem destThunkRel_target_notThunk {maxApp : Nat} {source : DestThunkResult}
    (related : DestThunkRel maxApp source .notThunk) : source = .notThunk := by
  cases related
  rfl

/-- A target thunk has a related source thunk in the same evaluation mode. -/
theorem destThunkRel_target_isThunk {maxApp : Nat} {source : DestThunkResult}
    {mode : AstHOL.ThunkMode} {value : Value}
    (related : DestThunkRel maxApp source (.isThunk mode value)) :
    ∃ sourceValue, source = .isThunk mode sourceValue ∧ ValueRel maxApp sourceValue value := by
  cases related with
  | isThunk mode sourceValue targetValue valueRel => exact ⟨sourceValue, rfl, valueRel⟩

/-- Forcing related thunks preserves the backward result and state relation,
using the generated application as the evaluator induction hypothesis. -/
theorem runForced_relatedWithin {C F : Type} (limit : Nat) (source target : State C F)
    (sourceValues targetValues : List Value)
    (targetResult : SemanticPrimitivesHOL.Result (List Value) Value) (targetFinal : State C F)
    (run : runForced targetValues target = (targetResult, targetFinal))
    (states : StateRel source target)
    (values : List.Forall₂ (ValueRel source.maxApp) sourceValues targetValues)
    (clock : source.clock ≤ limit)
    (forceIH : ∀ sourceCode, @EvaluateRelWithin C F limit sourceCode [appUnit (.var .none 0)]) :
    ∃ sourceResult sourceFinal,
      runForced sourceValues source = (sourceResult, sourceFinal) ∧
      resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
        sourceResult targetResult ∧ StateRel sourceFinal targetFinal := by
  have inspected := destThunk_related states values
  cases targetDest : destThunk targetValues target.refs with
  | badRef =>
    have sourceDest := destThunkRel_target_badRef (by simpa [targetDest] using inspected)
    simp [runForced, targetDest] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨.err (.abort .typeError), source, by simp [runForced, sourceDest],
      by simp [resultRel, excRel], states⟩
  | notThunk =>
    have sourceDest := destThunkRel_target_notThunk (by simpa [targetDest] using inspected)
    simp [runForced, targetDest] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨.err (.abort .typeError), source, by simp [runForced, sourceDest],
      by simp [resultRel, excRel], states⟩
  | isThunk mode targetValue =>
    obtain ⟨sourceValue, sourceDest, valueRel⟩ :=
      destThunkRel_target_isThunk (by simpa [targetDest] using inspected)
    cases mode with
    | evaluated =>
      simp [runForced, targetDest] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨.val [sourceValue], source, by simp [runForced, sourceDest],
        by simpa [resultRel] using List.Forall₂.cons valueRel List.Forall₂.nil, states⟩
    | notEvaluated =>
      cases targetForceRun : evaluate [appUnit (.var .none 0)] [targetValue] target with
      | mk forcedResult targetLast =>
        obtain ⟨sourceForceResult, sourceLast, sourceForceRun, forcedRel, finalStates⟩ :=
          forceIH [appUnit (.var .none 0)] [targetValue] target [sourceValue] targetLast source forcedResult
            clock targetForceRun (List.Forall₂.cons valueRel .nil) states (forceApplication_codeRel source.maxApp)
        have maxEq : sourceLast.maxApp = source.maxApp := by
          have preserved := ClosProps.evaluate_const.1 [appUnit (.var .none 0)] [sourceValue] source
          simpa [sourceForceRun] using preserved
        cases forcedResult with
        | err targetError =>
          cases sourceForceResult with
          | val vals => simp [resultRel] at forcedRel
          | err sourceError =>
            simp [runForced, targetDest, targetForceRun] at run
            obtain ⟨rfl, rfl⟩ := run
            exact ⟨.err sourceError, sourceLast,
              by simp [runForced, sourceDest, sourceForceRun], forcedRel, finalStates⟩
        | val targetForced =>
          cases sourceForceResult with
          | err error => simp [resultRel] at forcedRel
          | val sourceForced =>
            have pointers : List.Forall₂ (ValueRel sourceLast.maxApp) sourceValues targetValues := by
              simpa [maxEq] using values
            have output : List.Forall₂ (ValueRel sourceLast.maxApp) sourceForced targetForced := by
              simpa [resultRel, maxEq] using forcedRel
            have update := updateThunk_lists_related sourceLast targetLast sourceValues targetValues
              sourceForced targetForced finalStates pointers output
            cases targetUpdate : updateThunk targetValues targetLast.refs targetForced with
            | none =>
              have sourceUpdate := update.1 targetUpdate
              simp [runForced, targetDest, targetForceRun, targetUpdate] at run
              obtain ⟨rfl, rfl⟩ := run
              exact ⟨.err (.abort .typeError), sourceLast,
                by simp [runForced, sourceDest, sourceForceRun, sourceUpdate],
                by simp [resultRel, excRel], finalStates⟩
            | some targetRefs =>
              obtain ⟨sourceRefs, sourceUpdate, updatedStates⟩ := update.2 targetRefs targetUpdate
              simp [runForced, targetDest, targetForceRun, targetUpdate] at run
              obtain ⟨rfl, rfl⟩ := run
              exact ⟨.val sourceForced, { sourceLast with refs := sourceRefs },
                by simp [runForced, sourceDest, sourceForceRun, sourceUpdate],
                by simpa [resultRel, maxEq] using output, updatedStates⟩

/-- Forced-thunk expressions preserve the clock-bounded simulation. -/
theorem evaluateRel_forceWithin {C F : Type} (limit : Nat) (trace : BackendCommon.Tra)
    (targetArgs sourceCode : List ClosLang.Exp)
    (argsIH : ∀ sourceCode, @EvaluateRelWithin C F limit sourceCode targetArgs)
    (forceIH : ∀ sourceCode, @EvaluateRelWithin C F limit sourceCode [appUnit (.var .none 0)]) :
    @EvaluateRelWithin C F limit sourceCode [.op trace (.thunkOp .forceThunk) targetArgs] := by
  intro targetEnv target sourceEnv targetFinal source targetResult clock run env states code
  have length := codeRel_length code
  cases sourceCode with
  | nil => simp at length
  | cons expression rest =>
    cases rest with
    | cons next tail => simp at length
    | nil =>
      have unary : ClosProps.noMti expression := code.1 expression (by simp)
      have transformed : introExp source.maxApp expression =
          .op trace (.thunkOp .forceThunk) targetArgs := by
        simpa [introList] using code.2.symm
      obtain ⟨args, rfl, argsUnary, argsEq⟩ :=
        introExp_eq_op source.maxApp expression trace (.thunkOp .forceThunk) targetArgs unary transformed
      have argsCode : CodeRel source.maxApp args targetArgs :=
        ⟨ClosProps.noMtiList_iff args |>.mp argsUnary, argsEq⟩
      cases targetArgsRun : evaluate targetArgs targetEnv target with
      | mk argsResult targetMiddle =>
        obtain ⟨sourceArgsResult, sourceMiddle, sourceArgsRun, argsRel, middleStates⟩ :=
          argsIH args targetEnv target sourceEnv targetMiddle source argsResult clock targetArgsRun env states argsCode
        have maxEq : sourceMiddle.maxApp = source.maxApp := by
          have preserved := ClosProps.evaluate_const.1 args sourceEnv source
          simpa [sourceArgsRun] using preserved
        have middleClock : sourceMiddle.clock ≤ limit := by
          have preserved := evaluate_clock_le args sourceEnv source
          simp only [sourceArgsRun] at preserved
          omega
        cases argsResult with
        | err targetError =>
          cases sourceArgsResult with
          | val values => simp [resultRel] at argsRel
          | err sourceError =>
            rw [evaluate_force_eq, targetArgsRun] at run
            simp only [Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            exact ⟨.err sourceError, sourceMiddle, by rw [evaluate_force_eq, sourceArgsRun],
              argsRel, middleStates⟩
        | val targetValues =>
          cases sourceArgsResult with
          | err error => simp [resultRel] at argsRel
          | val sourceValues =>
            have valuesRel : List.Forall₂ (ValueRel sourceMiddle.maxApp) sourceValues targetValues := by
              simpa [resultRel, maxEq] using argsRel
            have targetContinuation : runForced targetValues targetMiddle = (targetResult, targetFinal) := by
              rw [evaluate_force_eq, targetArgsRun] at run
              exact run
            obtain ⟨sourceResult, sourceFinal, sourceContinuation, continuationRel, finalStates⟩ :=
              runForced_relatedWithin limit sourceMiddle targetMiddle sourceValues targetValues targetResult targetFinal
                targetContinuation middleStates valuesRel middleClock forceIH
            refine ⟨sourceResult, sourceFinal, ?_, ?_, finalStates⟩
            · rw [evaluate_force_eq, sourceArgsRun]
              exact sourceContinuation
            · simpa [maxEq] using continuationRel

end Flapjack.Compiler.Backend.ClosMti
