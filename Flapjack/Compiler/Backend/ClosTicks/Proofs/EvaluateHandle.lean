module

public import Flapjack.Compiler.Backend.ClosTicks.Proofs.EvaluateSequence

@[expose] public section

/-! Exception-handler case of the tick-removal evaluator simulation. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- A handler produced by tick removal came from a handler under ticks. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_Handle_IMP_mk_Ticks"]
theorem remove_ticks_Handle_IMP_mk_Ticks (expression : ClosLang.Exp) (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp)
    (removed : [ClosLang.Exp.handle trace body handler] = removeList [expression]) :
    ∃ traces sourceBody sourceHandler, expression = mkTicks traces (.handle trace sourceBody sourceHandler) ∧
      [body] = removeList [sourceBody] ∧ [handler] = removeList [sourceHandler] := by
  cases expression
  case tick outer inner =>
    have innerRemoved : [ClosLang.Exp.handle trace body handler] = removeList [inner] := by
      simpa [removeList, removeSing] using removed
    obtain ⟨traces, sourceBody, sourceHandler, equal, bodyEqual, handlerEqual⟩ :=
      remove_ticks_Handle_IMP_mk_Ticks inner trace body handler innerRemoved
    exact ⟨outer :: traces, sourceBody, sourceHandler, by simp [mkTicks, equal], bodyEqual, handlerEqual⟩
  case handle actualTrace sourceBody sourceHandler =>
    simp [removeList, removeSing] at removed
    obtain ⟨rfl, rfl, rfl⟩ := removed
    exact ⟨[], sourceBody, sourceHandler, rfl, by simp [removeList], by simp [removeList]⟩
  all_goals simp [removeList, removeSing] at removed
termination_by sizeOf expression

namespace HandlePort
/-- The closure state has the reviewed canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end HandlePort

/-- The handler case of the reverse tick-removal simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_ticks_handle {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (envTarget : List Value) (target : State C F)
    (bodyIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (envSource : List Value) (source : State C F) (code : List ClosLang.Exp),
      evaluate [body] envTarget target = (result, next) ∧ List.Forall₂ ValueRel envSource envTarget ∧
        StateRel source target ∧ CodeRel code [body] →
      ∃ extra sourceResult sourceNext,
        evaluate code envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
        ResultRel sourceResult result ∧ StateRel sourceNext next)
    (handlerIH : ∀ (value : Value) (middle : State C F),
      evaluate [body] envTarget target = (.err (.raise value), middle) →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (envSource : List Value) (source : State C F) (code : List ClosLang.Exp),
        evaluate [handler] (value :: envTarget) middle = (result, next) ∧
          List.Forall₂ ValueRel envSource (value :: envTarget) ∧ StateRel source middle ∧
          CodeRel code [handler] →
        ∃ extra sourceResult sourceNext,
          evaluate code envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
          ResultRel sourceResult result ∧ StateRel sourceNext next)
    (result : Result (List Value) Value) (targetNext : State C F)
    (envSource : List Value) (source : State C F) (sourceCode : List ClosLang.Exp)
    (premises : evaluate [.handle trace body handler] envTarget target = (result, targetNext) ∧
      List.Forall₂ ValueRel envSource envTarget ∧ StateRel source target ∧
      CodeRel sourceCode [.handle trace body handler]) :
    ∃ extra sourceResult sourceNext,
      evaluate sourceCode envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
      ResultRel sourceResult result ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have length := code_rel_IMP_LENGTH sourceCode [.handle trace body handler] code
  have singleton : ∃ expression, sourceCode = [expression] := by
    cases sourceCode with
    | nil => simp at length
    | cons first rest =>
      cases rest with
      | nil => exact ⟨first, rfl⟩
      | cons second rest => simp at length
  obtain ⟨expression, rfl⟩ := singleton
  obtain ⟨traces, sourceBody, sourceHandler, rfl, bodyCode, handlerCode⟩ :=
    remove_ticks_Handle_IMP_mk_Ticks expression trace body handler code
  have wrapped (extra : Nat) : evaluate [mkTicks traces (.handle trace sourceBody sourceHandler)] envSource
      { source with clock := source.clock + (extra + traces.length) } =
      evaluate [.handle trace sourceBody sourceHandler] envSource { source with clock := source.clock + extra } := by
    rw [evaluate_mk_Ticks]
    have enough : ¬ source.clock + (extra + traces.length) < traces.length := by omega
    have clocks : source.clock + (extra + traces.length) - traces.length = source.clock + extra := by omega
    simp [decClock, enough, clocks]
  cases bodyRun : evaluate [body] envTarget target with
  | mk bodyResult targetMiddle =>
    obtain ⟨extra, sourceResult, sourceMiddle, sourceRun, related, middleRel⟩ :=
      bodyIH bodyResult targetMiddle envSource source [sourceBody] ⟨bodyRun, envRel, states, bodyCode⟩
    cases bodyResult with
    | val values =>
      cases sourceResult with
      | err error => cases error <;> simp [ResultRel] at related
      | val sourceValues =>
        rw [evaluate, fixClock_evaluate, bodyRun] at run
        cases run
        refine ⟨extra + traces.length, .val sourceValues, sourceMiddle, ?_, related, middleRel⟩
        rw [wrapped, evaluate, fixClock_evaluate, sourceRun]
    | err error =>
      cases error with
      | abort reason =>
        cases sourceResult with
        | val values => simp [ResultRel] at related
        | err sourceError =>
          cases sourceError with
          | raise value => simp [ResultRel] at related
          | abort sourceReason =>
            rw [evaluate, fixClock_evaluate, bodyRun] at run
            cases run
            refine ⟨extra + traces.length, .err (.abort sourceReason), sourceMiddle, ?_, related, middleRel⟩
            rw [wrapped, evaluate, fixClock_evaluate, sourceRun]
      | raise value =>
        cases sourceResult with
        | val values => simp [ResultRel] at related
        | err sourceError =>
          cases sourceError with
          | abort reason => simp [ResultRel] at related
          | raise sourceValue =>
            have handlerRun : evaluate [handler] (value :: envTarget) targetMiddle = (result, targetNext) := by
              rw [evaluate, fixClock_evaluate, bodyRun] at run
              exact run
            obtain ⟨handlerExtra, sourceHandlerResult, sourceLast, sourceHandlerRun, handlerRel, lastRel⟩ :=
              handlerIH value targetMiddle bodyRun result targetNext (sourceValue :: envSource) sourceMiddle
                [sourceHandler] ⟨handlerRun, .cons related envRel, middleRel, handlerCode⟩
            have shifted := (evaluate_addClock (C := C) (F := F)).1 [sourceBody] envSource
              { source with clock := source.clock + extra } sourceMiddle (.err (.raise sourceValue)) handlerExtra
              sourceRun (by simp)
            have shiftedRun : evaluate [sourceBody] envSource
                { source with clock := source.clock + (extra + handlerExtra) } =
                  (.err (.raise sourceValue), { sourceMiddle with clock := sourceMiddle.clock + handlerExtra }) := by
              simpa [Nat.add_assoc] using shifted
            refine ⟨extra + handlerExtra + traces.length, sourceHandlerResult, sourceLast, ?_, handlerRel, lastRel⟩
            rw [wrapped, evaluate, fixClock_evaluate, shiftedRun]
            exact sourceHandlerRun

end Flapjack.Compiler.Backend.ClosTicks
