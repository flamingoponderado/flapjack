import Flapjack.Compiler.Backend.ClosTicks.Proofs.EvaluateSequence

/-! Application-expression case of the tick-removal evaluator simulation. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

private instance : Nonempty ClosLang.Exp := ⟨.var .none 0⟩

/-- An application produced by tick removal came from one under leading ticks. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_App_IMP_mk_Ticks"]
theorem remove_ticks_App_IMP_mk_Ticks (expression : ClosLang.Exp) (trace : BackendCommon.Tra)
    (location : Option Nat) (function : ClosLang.Exp) (args : List ClosLang.Exp)
    (removed : [ClosLang.Exp.app trace location function args] = removeList [expression]) :
    ∃ traces sourceFunction sourceArgs,
      expression = mkTicks traces (.app trace location sourceFunction sourceArgs) ∧
      function = Flapjack.holHd (removeList [sourceFunction]) ∧ args = removeList sourceArgs := by
  cases expression
  case tick outer inner =>
    have innerRemoved : [ClosLang.Exp.app trace location function args] = removeList [inner] := by
      simpa [removeList, removeSing] using removed
    obtain ⟨traces, sourceFunction, sourceArgs, equal, functionEqual, argsEqual⟩ :=
      remove_ticks_App_IMP_mk_Ticks inner trace location function args innerRemoved
    exact ⟨outer :: traces, sourceFunction, sourceArgs, by simp [mkTicks, equal], functionEqual, argsEqual⟩
  case app actualTrace actualLocation sourceFunction sourceArgs =>
    simp [removeList, removeSing] at removed
    obtain ⟨rfl, rfl, rfl, rfl⟩ := removed
    exact ⟨[], sourceFunction, sourceArgs, rfl, by simp [removeList, Flapjack.holHd], rfl⟩
  all_goals simp [removeList, removeSing] at removed
termination_by sizeOf expression

namespace AppPort
/-- The closure state has the reviewed canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end AppPort

/-- The application-expression case of the reverse tick-removal simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_ticks_app {C F : Type} (trace : BackendCommon.Tra)
    (location : Option Nat) (function : ClosLang.Exp) (args : List ClosLang.Exp)
    (envTarget : List Value) (target : State C F)
    (argsIH : 0 < args.length → ∀ (result : Result (List Value) Value) (next : State C F)
        (envSource : List Value) (source : State C F) (code : List ClosLang.Exp),
      evaluate args envTarget target = (result, next) ∧ List.Forall₂ ValueRel envSource envTarget ∧
        StateRel source target ∧ CodeRel code args →
      ∃ extra sourceResult sourceNext,
        evaluate code envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
        ResultRel sourceResult result ∧ StateRel sourceNext next)
    (functionIH : ∀ (values : List Value) (middle : State C F),
      0 < args.length → evaluate args envTarget target = (.val values, middle) →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (envSource : List Value) (source : State C F) (code : List ClosLang.Exp),
        evaluate [function] envTarget middle = (result, next) ∧ List.Forall₂ ValueRel envSource envTarget ∧
          StateRel source middle ∧ CodeRel code [function] →
        ∃ extra sourceResult sourceNext,
          evaluate code envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
          ResultRel sourceResult result ∧ StateRel sourceNext next)
    (appIH : ∀ (values : List Value) (middle : State C F) (functions : List Value) (last : State C F),
      0 < args.length → evaluate args envTarget target = (.val values, middle) →
      evaluate [function] envTarget middle = (.val functions, last) →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (sourceFunction : Value) (sourceArgs : List Value) (source : State C F),
        evaluateApp location (@Flapjack.holHd Value ⟨unitValue⟩ functions) values last = (result, next) ∧
          ValueRel sourceFunction (@Flapjack.holHd Value ⟨unitValue⟩ functions) ∧
          List.Forall₂ ValueRel sourceArgs values ∧ StateRel source last →
        ∃ extra sourceResult sourceNext,
          evaluateApp location sourceFunction sourceArgs { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
          ResultRel sourceResult result ∧ StateRel sourceNext next)
    (result : Result (List Value) Value) (targetNext : State C F)
    (envSource : List Value) (source : State C F) (sourceCode : List ClosLang.Exp)
    (premises : evaluate [.app trace location function args] envTarget target = (result, targetNext) ∧
      List.Forall₂ ValueRel envSource envTarget ∧ StateRel source target ∧
      CodeRel sourceCode [.app trace location function args]) :
    ∃ extra sourceResult sourceNext,
      evaluate sourceCode envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
      ResultRel sourceResult result ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have length := code_rel_IMP_LENGTH sourceCode [.app trace location function args] code
  have singleton : ∃ expression, sourceCode = [expression] := by
    cases sourceCode with
    | nil => simp at length
    | cons first rest =>
      cases rest with
      | nil => exact ⟨first, rfl⟩
      | cons second rest => simp at length
  obtain ⟨expression, rfl⟩ := singleton
  obtain ⟨traces, sourceFunction, sourceArgs, rfl, functionCode, argsCode⟩ :=
    remove_ticks_App_IMP_mk_Ticks expression trace location function args code
  simp only [removeList, Flapjack.holHd] at functionCode
  have wrapped (extra : Nat) : evaluate [mkTicks traces (.app trace location sourceFunction sourceArgs)] envSource
      { source with clock := source.clock + (extra + traces.length) } =
      evaluate [.app trace location sourceFunction sourceArgs] envSource { source with clock := source.clock + extra } := by
    rw [evaluate_mk_Ticks]
    have enough : ¬ source.clock + (extra + traces.length) < traces.length := by omega
    have clocks : source.clock + (extra + traces.length) - traces.length = source.clock + extra := by omega
    simp [decClock, enough, clocks]
  cases args with
  | nil =>
    have sourceEmpty : sourceArgs = [] := by
      have h := congrArg List.length argsCode
      simp [removeList_eq_map] at h
      simpa using h.symm
    subst sourceArgs
    simp [evaluate] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨traces.length, .err (.abort .typeError), source, ?_, rfl, states⟩
    simpa using (show evaluate [mkTicks traces (.app trace location sourceFunction [])] envSource
        { source with clock := source.clock + (0 + traces.length) } = (.err (.abort .typeError), source) by
      rw [wrapped]
      simp [evaluate])
  | cons first rest =>
    have nonempty : 0 < (first :: rest).length := by simp
    have sourceNonempty : sourceArgs.isEmpty = false := by
      cases sourceArgs with
      | nil => simp [removeList] at argsCode
      | cons first rest => rfl
    cases argsRun : evaluate (first :: rest) envTarget target with
    | mk argsResult targetMiddle =>
      obtain ⟨argsExtra, sourceArgsResult, sourceMiddle, sourceArgsRun, argsRel, middleRel⟩ :=
        argsIH nonempty argsResult targetMiddle envSource source sourceArgs ⟨argsRun, envRel, states, argsCode⟩
      cases argsResult with
      | err error =>
        rw [evaluate, fixClock_evaluate, argsRun] at run
        cases run
        cases sourceArgsResult with
        | val values => cases error <;> simp [ResultRel] at argsRel
        | err sourceError =>
          refine ⟨argsExtra + traces.length, .err sourceError, sourceMiddle, ?_, argsRel, middleRel⟩
          rw [wrapped, evaluate]
          simp only [sourceNonempty, Bool.false_eq_true, ↓reduceIte]
          rw [fixClock_evaluate, sourceArgsRun]
      | val values =>
        cases sourceArgsResult with
        | err error => cases error <;> simp [ResultRel] at argsRel
        | val sourceValues =>
          cases functionRun : evaluate [function] envTarget targetMiddle with
          | mk functionResult targetLast =>
            obtain ⟨functionExtra, sourceFunctionResult, sourceLast, sourceFunctionRun, functionRel, lastRel⟩ :=
              functionIH values targetMiddle nonempty argsRun functionResult targetLast envSource sourceMiddle [sourceFunction]
                ⟨functionRun, envRel, middleRel, by simp [CodeRel, removeList, functionCode]⟩
            have shiftedArgs (extra : Nat) : evaluate sourceArgs envSource
                { source with clock := source.clock + (argsExtra + extra) } =
                  (.val sourceValues, { sourceMiddle with clock := sourceMiddle.clock + extra }) := by
              have h := (evaluate_addClock (C := C) (F := F)).1 sourceArgs envSource
                { source with clock := source.clock + argsExtra } sourceMiddle (.val sourceValues) extra sourceArgsRun (by simp)
              simpa [Nat.add_assoc] using h
            cases functionResult with
            | err error =>
              rw [evaluate, fixClock_evaluate, argsRun] at run
              simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run
              rw [fixClock_evaluate, functionRun] at run
              cases run
              cases sourceFunctionResult with
              | val values => cases error <;> simp [ResultRel] at functionRel
              | err sourceError =>
                refine ⟨argsExtra + functionExtra + traces.length, .err sourceError, sourceLast, ?_, functionRel, lastRel⟩
                rw [wrapped, evaluate]
                simp only [sourceNonempty, Bool.false_eq_true, ↓reduceIte]
                rw [fixClock_evaluate, shiftedArgs functionExtra, fixClock_evaluate, sourceFunctionRun]
            | val functions =>
              obtain ⟨value, rfl⟩ := evaluate_singleton_value function envTarget targetMiddle targetLast functions functionRun
              cases sourceFunctionResult with
              | err error => cases error <;> simp [ResultRel] at functionRel
              | val sourceFunctions =>
                cases functionRel with
                | cons valueRel tailRel =>
                  cases tailRel
                  rename_i sourceValue
                  have appRun : evaluateApp location value values targetLast = (result, targetNext) := by
                    rw [evaluate, fixClock_evaluate, argsRun] at run
                    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run
                    rw [fixClock_evaluate, functionRun] at run
                    exact run
                  obtain ⟨appExtra, sourceResult, sourceNext, sourceAppRun, resultRel, nextRel⟩ :=
                    appIH values targetMiddle [value] targetLast nonempty argsRun functionRun result targetNext
                      sourceValue sourceValues sourceLast ⟨by simpa [Flapjack.holHd] using appRun,
                        by simpa [Flapjack.holHd] using valueRel, argsRel, lastRel⟩
                  have shiftedFunction : evaluate [sourceFunction] envSource
                      { sourceMiddle with clock := sourceMiddle.clock + (functionExtra + appExtra) } =
                        (.val [sourceValue], { sourceLast with clock := sourceLast.clock + appExtra }) := by
                    have h := (evaluate_addClock (C := C) (F := F)).1 [sourceFunction] envSource
                      { sourceMiddle with clock := sourceMiddle.clock + functionExtra } sourceLast (.val [sourceValue])
                      appExtra sourceFunctionRun (by simp)
                    simpa [Nat.add_assoc] using h
                  refine ⟨argsExtra + (functionExtra + appExtra) + traces.length, sourceResult, sourceNext,
                    ?_, resultRel, nextRel⟩
                  rw [wrapped, evaluate]
                  simp only [sourceNonempty, Bool.false_eq_true, ↓reduceIte]
                  rw [fixClock_evaluate, shiftedArgs (functionExtra + appExtra), fixClock_evaluate, shiftedFunction]
                  exact sourceAppRun

end Flapjack.Compiler.Backend.ClosTicks
