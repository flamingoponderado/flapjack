module

public import Flapjack.Compiler.Backend.ClosTicks.Proofs.Evaluate
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength

@[expose] public section

/-! Raise case of the tick-removal evaluator simulation. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- A raise produced by tick removal came from a raise under leading ticks. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_Raise_IMP_mk_Ticks"]
theorem remove_ticks_Raise_IMP_mk_Ticks (expression : ClosLang.Exp) (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (removed : [ClosLang.Exp.raise trace body] = removeList [expression]) :
    ∃ traces sourceBody, expression = mkTicks traces (.raise trace sourceBody) ∧
      [body] = removeList [sourceBody] := by
  cases expression
  case tick outer inner =>
    have innerRemoved : [ClosLang.Exp.raise trace body] = removeList [inner] := by
      simpa [removeList, removeSing] using removed
    obtain ⟨traces, sourceBody, equal, bodyEqual⟩ :=
      remove_ticks_Raise_IMP_mk_Ticks inner trace body innerRemoved
    exact ⟨outer :: traces, sourceBody, by simp [mkTicks, equal], bodyEqual⟩
  case raise actualTrace sourceBody =>
    simp [removeList, removeSing] at removed
    obtain ⟨rfl, rfl⟩ := removed
    exact ⟨[], sourceBody, rfl, by simp [removeList]⟩
  all_goals simp [removeList, removeSing] at removed
termination_by sizeOf expression

namespace RaisePort
/-- The closure state has the reviewed canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end RaisePort

/-- The raise case of the reverse tick-removal simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_ticks_raise {C F : Type} (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (envTarget : List Value) (target : State C F)
    (bodyIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (envSource : List Value) (source : State C F) (code : List ClosLang.Exp),
      evaluate [body] envTarget target = (result, next) ∧ List.Forall₂ ValueRel envSource envTarget ∧
        StateRel source target ∧ CodeRel code [body] →
      ∃ extra sourceResult sourceNext,
        evaluate code envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
        ResultRel sourceResult result ∧ StateRel sourceNext next)
    (result : Result (List Value) Value) (targetNext : State C F)
    (envSource : List Value) (source : State C F) (sourceCode : List ClosLang.Exp)
    (premises : evaluate [.raise trace body] envTarget target = (result, targetNext) ∧
      List.Forall₂ ValueRel envSource envTarget ∧ StateRel source target ∧
      CodeRel sourceCode [.raise trace body]) :
    ∃ extra sourceResult sourceNext,
      evaluate sourceCode envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
      ResultRel sourceResult result ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have length := code_rel_IMP_LENGTH sourceCode [.raise trace body] code
  have singleton : ∃ expression, sourceCode = [expression] := by
    cases sourceCode with
    | nil => simp at length
    | cons first rest =>
      cases rest with
      | nil => exact ⟨first, rfl⟩
      | cons second rest => simp at length
  obtain ⟨expression, rfl⟩ := singleton
  obtain ⟨traces, sourceBody, rfl, bodyCode⟩ :=
    remove_ticks_Raise_IMP_mk_Ticks expression trace body code
  cases bodyRun : evaluate [body] envTarget target with
  | mk bodyResult bodyNext =>
    obtain ⟨extra, sourceResult, sourceNext, sourceRun, related, nextRel⟩ :=
      bodyIH bodyResult bodyNext envSource source [sourceBody] ⟨bodyRun, envRel, states, bodyCode⟩
    have wrapped : evaluate [mkTicks traces (.raise trace sourceBody)] envSource
        { source with clock := source.clock + (extra + traces.length) } =
        evaluate [.raise trace sourceBody] envSource { source with clock := source.clock + extra } := by
      rw [evaluate_mk_Ticks]
      have enough : ¬ source.clock + (extra + traces.length) < traces.length := by omega
      have clocks : source.clock + (extra + traces.length) - traces.length = source.clock + extra := by omega
      simp [decClock, enough, clocks]
    cases bodyResult with
    | err error =>
      simp [evaluate, bodyRun] at run
      obtain ⟨rfl, rfl⟩ := run
      cases sourceResult with
      | val values => cases error <;> simp [ResultRel] at related
      | err sourceError =>
        refine ⟨extra + traces.length, .err sourceError, sourceNext, ?_, related, nextRel⟩
        rw [wrapped]
        simp [evaluate, sourceRun]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value body envTarget target bodyNext values bodyRun
      cases sourceResult with
      | err error => cases error <;> simp [ResultRel] at related
      | val sourceValues =>
        cases related with
        | cons valueRel tailRel =>
          cases tailRel
          simp [evaluate, bodyRun] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨extra + traces.length, .err (.raise _), sourceNext, ?_, valueRel, nextRel⟩
          rw [wrapped]
          simp [evaluate, sourceRun]

end Flapjack.Compiler.Backend.ClosTicks
