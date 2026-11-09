module

public import Flapjack.Compiler.Backend.ClosTicks.Proofs.EvaluateSequence

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section

/-! Direct-call case of the tick-removal evaluator simulation. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- A call produced by tick removal has zero ticks and came from a call under
leading ticks. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_Call_IMP_mk_Ticks"]
theorem remove_ticks_Call_IMP_mk_Ticks (expression : ClosLang.Exp) (trace : BackendCommon.Tra)
    (ticks location : Nat) (args : List ClosLang.Exp)
    (removed : [ClosLang.Exp.call trace ticks location args] = removeList [expression]) :
    ticks = 0 ∧ ∃ traces sourceTicks sourceArgs,
      expression = mkTicks traces (.call trace sourceTicks location sourceArgs) ∧ args = removeList sourceArgs := by
  cases expression
  case tick outer inner =>
    have innerRemoved : [ClosLang.Exp.call trace ticks location args] = removeList [inner] := by
      simpa [removeList, removeSing] using removed
    obtain ⟨zero, traces, sourceTicks, sourceArgs, equal, argsEqual⟩ :=
      remove_ticks_Call_IMP_mk_Ticks inner trace ticks location args innerRemoved
    exact ⟨zero, outer :: traces, sourceTicks, sourceArgs, by simp [mkTicks, equal], argsEqual⟩
  case call actualTrace sourceTicks actualLocation sourceArgs =>
    simp [removeList, removeSing] at removed
    obtain ⟨rfl, rfl, rfl, rfl⟩ := removed
    exact ⟨rfl, [], sourceTicks, sourceArgs, rfl, rfl⟩
  all_goals simp [removeList, removeSing] at removed
termination_by sizeOf expression

namespace CallPort
/-- The closure state has the reviewed canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end CallPort

/-- The direct-call case of the reverse tick-removal simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_ticks_call {C F : Type} (trace : BackendCommon.Tra)
    (ticks location : Nat) (args : List ClosLang.Exp) (envTarget : List Value) (target : State C F)
    (argsIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (envSource : List Value) (source : State C F) (code : List ClosLang.Exp),
      evaluate args envTarget target = (result, next) ∧ List.Forall₂ ValueRel envSource envTarget ∧
        StateRel source target ∧ CodeRel code args →
      ∃ extra sourceResult sourceNext,
        evaluate code envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
        ResultRel sourceResult result ∧ StateRel sourceNext next)
    (result : Result (List Value) Value) (targetNext : State C F)
    (envSource : List Value) (source : State C F) (sourceCode : List ClosLang.Exp)
    (premises : evaluate [.call trace ticks location args] envTarget target = (result, targetNext) ∧
      List.Forall₂ ValueRel envSource envTarget ∧ StateRel source target ∧
      CodeRel sourceCode [.call trace ticks location args]) :
    ∃ extra sourceResult sourceNext,
      evaluate sourceCode envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
      ResultRel sourceResult result ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have length := code_rel_IMP_LENGTH sourceCode [.call trace ticks location args] code
  have singleton : ∃ expression, sourceCode = [expression] := by
    cases sourceCode with
    | nil => simp at length
    | cons first rest =>
      cases rest with
      | nil => exact ⟨first, rfl⟩
      | cons second rest => simp at length
  obtain ⟨expression, rfl⟩ := singleton
  obtain ⟨rfl, traces, sourceTicks, sourceArgs, rfl, argsCode⟩ :=
    remove_ticks_Call_IMP_mk_Ticks expression trace ticks location args code
  have wrapped (extra : Nat) : evaluate [mkTicks traces (.call trace sourceTicks location sourceArgs)] envSource
      { source with clock := source.clock + (extra + traces.length) } =
      evaluate [.call trace sourceTicks location sourceArgs] envSource { source with clock := source.clock + extra } := by
    rw [evaluate_mk_Ticks]
    have enough : ¬ source.clock + (extra + traces.length) < traces.length := by omega
    have clocks : source.clock + (extra + traces.length) - traces.length = source.clock + extra := by omega
    simp [decClock, enough, clocks]
  cases argsRun : evaluate args envTarget target with
  | mk argsResult targetMiddle =>
    obtain ⟨extra, sourceResult, sourceMiddle, sourceRun, related, middleRel⟩ :=
      argsIH argsResult targetMiddle envSource source sourceArgs ⟨argsRun, envRel, states, argsCode⟩
    cases argsResult with
    | err error =>
      rw [evaluate, fixClock_evaluate, argsRun] at run
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
        have sourceEmpty : sourceMiddle.code = HolFiniteMapExact.empty := middleRel.2.1
        have targetEmpty : targetMiddle.code = HolFiniteMapExact.empty := middleRel.2.2.1
        rw [evaluate, fixClock_evaluate, argsRun] at run
        simp [findCode, targetEmpty, HolFiniteMapExact.empty] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨extra + traces.length, .err (.abort .typeError), sourceMiddle, ?_, rfl, middleRel⟩
        rw [wrapped, evaluate, fixClock_evaluate, sourceRun]
        simp [findCode, sourceEmpty, HolFiniteMapExact.empty]

end Flapjack.Compiler.Backend.ClosTicks
