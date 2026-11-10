module

public import Flapjack.Compiler.Backend.ClosTicks.Proofs.Evaluate

@[expose] public section

/-! Tick case of the tick-removal evaluator simulation. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Removing ticks cannot produce a singleton headed by a tick. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_Tick"]
theorem remove_ticks_Tick (expression : ClosLang.Exp) (trace : BackendCommon.Tra) (body : ClosLang.Exp) :
    ¬ ([ClosLang.Exp.tick trace body] = removeSource [expression]) := by
  cases expression
  case tick outer inner =>
    intro removed
    exact remove_ticks_Tick inner trace body (by simpa [removeList, removeSing] using removed)
  all_goals simp [removeList, removeSing]
termination_by sizeOf expression

namespace TickPort
/-- The closure state has the reviewed canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end TickPort

/-- The target-tick case of the reverse simulation is impossible because
tick removal cannot produce a leading tick. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_ticks_tick {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (envTarget : List Value) (target : State C F) (result : Result (List Value) Value) (targetNext : State C F)
    (envSource : List Value) (source : State C F) (sourceCode : List ClosLang.Exp)
    (premises : evaluate [.tick trace body] envTarget target = (result, targetNext) ∧
      List.Forall₂ ValueRel envSource envTarget ∧ StateRel source target ∧
      CodeRel sourceCode [.tick trace body]) :
    ∃ extra sourceResult sourceNext,
      evaluate sourceCode envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
      ResultRel sourceResult result ∧ StateRel sourceNext targetNext := by
  have code := premises.2.2.2
  have length := code_rel_IMP_LENGTH sourceCode [.tick trace body] code
  cases sourceCode with
  | nil => simp at length
  | cons first rest =>
    cases rest with
    | nil => exact (remove_ticks_Tick first trace body code).elim
    | cons second rest => simp at length

end Flapjack.Compiler.Backend.ClosTicks
