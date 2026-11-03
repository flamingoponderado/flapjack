import Flapjack.Compiler.Backend.ClosTicks.Proofs.EvaluateSequence

/-! Let case of the tick-removal evaluator simulation. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- A let produced by tick removal came from a let under leading ticks. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_Let_IMP_mk_Ticks"]
theorem remove_ticks_Let_IMP_mk_Ticks (expression : ClosLang.Exp) (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp)
    (removed : [ClosLang.Exp.let trace bindings body] = removeList [expression]) :
    ∃ traces sourceBindings sourceBody, expression = mkTicks traces (.let trace sourceBindings sourceBody) ∧
      bindings = removeList sourceBindings ∧ [body] = removeList [sourceBody] := by
  cases expression
  case tick outer inner =>
    have innerRemoved : [ClosLang.Exp.let trace bindings body] = removeList [inner] := by
      simpa [removeList, removeSing] using removed
    obtain ⟨traces, sourceBindings, sourceBody, equal, bindingsEqual, bodyEqual⟩ :=
      remove_ticks_Let_IMP_mk_Ticks inner trace bindings body innerRemoved
    exact ⟨outer :: traces, sourceBindings, sourceBody, by simp [mkTicks, equal], bindingsEqual, bodyEqual⟩
  case «let» actualTrace sourceBindings sourceBody =>
    simp [removeList, removeSing] at removed
    obtain ⟨rfl, rfl, rfl⟩ := removed
    exact ⟨[], sourceBindings, sourceBody, rfl, rfl, by simp [removeList]⟩
  all_goals simp [removeList, removeSing] at removed
termination_by sizeOf expression

namespace LetPort
/-- The closure state has the reviewed canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end LetPort

/-- The let case of the reverse tick-removal simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_ticks_let {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (envTarget : List Value) (target : State C F)
    (bindingsIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (envSource : List Value) (source : State C F) (code : List ClosLang.Exp),
      evaluate bindings envTarget target = (result, next) ∧ List.Forall₂ ValueRel envSource envTarget ∧
        StateRel source target ∧ CodeRel code bindings →
      ∃ extra sourceResult sourceNext,
        evaluate code envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
        ResultRel sourceResult result ∧ StateRel sourceNext next)
    (bodyIH : ∀ (values : List Value) (middle : State C F),
      evaluate bindings envTarget target = (.val values, middle) →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (envSource : List Value) (source : State C F) (code : List ClosLang.Exp),
        evaluate [body] (values ++ envTarget) middle = (result, next) ∧
          List.Forall₂ ValueRel envSource (values ++ envTarget) ∧ StateRel source middle ∧
          CodeRel code [body] →
        ∃ extra sourceResult sourceNext,
          evaluate code envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
          ResultRel sourceResult result ∧ StateRel sourceNext next)
    (result : Result (List Value) Value) (targetNext : State C F)
    (envSource : List Value) (source : State C F) (sourceCode : List ClosLang.Exp)
    (premises : evaluate [.let trace bindings body] envTarget target = (result, targetNext) ∧
      List.Forall₂ ValueRel envSource envTarget ∧ StateRel source target ∧
      CodeRel sourceCode [.let trace bindings body]) :
    ∃ extra sourceResult sourceNext,
      evaluate sourceCode envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
      ResultRel sourceResult result ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have length := code_rel_IMP_LENGTH sourceCode [.let trace bindings body] code
  have singleton : ∃ expression, sourceCode = [expression] := by
    cases sourceCode with
    | nil => simp at length
    | cons first rest =>
      cases rest with
      | nil => exact ⟨first, rfl⟩
      | cons second rest => simp at length
  obtain ⟨expression, rfl⟩ := singleton
  obtain ⟨traces, sourceBindings, sourceBody, rfl, bindingsCode, bodyCode⟩ :=
    remove_ticks_Let_IMP_mk_Ticks expression trace bindings body code
  have wrapped (extra : Nat) : evaluate [mkTicks traces (.let trace sourceBindings sourceBody)] envSource
      { source with clock := source.clock + (extra + traces.length) } =
      evaluate [.let trace sourceBindings sourceBody] envSource { source with clock := source.clock + extra } := by
    rw [evaluate_mk_Ticks]
    have enough : ¬ source.clock + (extra + traces.length) < traces.length := by omega
    have clocks : source.clock + (extra + traces.length) - traces.length = source.clock + extra := by omega
    simp [decClock, enough, clocks]
  cases bindingsRun : evaluate bindings envTarget target with
  | mk bindingsResult targetMiddle =>
    obtain ⟨extra, sourceResult, sourceMiddle, sourceRun, related, middleRel⟩ :=
      bindingsIH bindingsResult targetMiddle envSource source sourceBindings ⟨bindingsRun, envRel, states, bindingsCode⟩
    cases bindingsResult with
    | err error =>
      rw [evaluate, fixClock_evaluate, bindingsRun] at run
      cases run
      cases sourceResult with
      | val values => cases error <;> simp [ResultRel] at related
      | err sourceError =>
        refine ⟨extra + traces.length, .err sourceError, sourceMiddle, ?_, related, middleRel⟩
        rw [wrapped, evaluate, fixClock_evaluate, sourceRun]
    | val values =>
      cases sourceResult with
      | err error => cases error <;> simp [ResultRel] at related
      | val sourceValues =>
        have bodyRun : evaluate [body] (values ++ envTarget) targetMiddle = (result, targetNext) := by
          rw [evaluate, fixClock_evaluate, bindingsRun] at run
          exact run
        obtain ⟨bodyExtra, sourceBodyResult, sourceLast, sourceBodyRun, bodyRel, lastRel⟩ :=
          bodyIH values targetMiddle bindingsRun result targetNext (sourceValues ++ envSource) sourceMiddle
            [sourceBody] ⟨bodyRun, List.rel_append related envRel, middleRel, bodyCode⟩
        have shifted := (evaluate_addClock (C := C) (F := F)).1 sourceBindings envSource
          { source with clock := source.clock + extra } sourceMiddle (.val sourceValues) bodyExtra
          sourceRun (by simp)
        have shiftedRun : evaluate sourceBindings envSource
            { source with clock := source.clock + (extra + bodyExtra) } =
              (.val sourceValues, { sourceMiddle with clock := sourceMiddle.clock + bodyExtra }) := by
          simpa [Nat.add_assoc] using shifted
        refine ⟨extra + bodyExtra + traces.length, sourceBodyResult, sourceLast, ?_, bodyRel, lastRel⟩
        rw [wrapped, evaluate, fixClock_evaluate, shiftedRun]
        exact sourceBodyRun

end Flapjack.Compiler.Backend.ClosTicks
