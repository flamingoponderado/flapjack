import Flapjack.Compiler.Backend.ClosTicks.Proofs.Relations
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import Mathlib.Tactic

/-! Evaluator infrastructure for closure tick-removal correctness. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Wrap an expression in the given sequence of ticks. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "mk_Ticks_def"]
def mkTicks : List BackendCommon.Tra → ClosLang.Exp → ClosLang.Exp
  | [], e => e
  | t :: ts, e => .tick t (mkTicks ts e)

/-- Tick removal ignores a sequence of leading ticks. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_mk_Ticks"]
theorem remove_ticks_mk_Ticks (traces : List BackendCommon.Tra) (expression : ClosLang.Exp) :
    removeList [mkTicks traces expression] = removeList [expression] := by
  induction traces with
  | nil => rfl
  | cons trace rest ih => simpa [mkTicks, removeList, removeSing] using ih

namespace EvaluatePort
/-- The closure state has the reviewed canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end EvaluatePort

/-- Evaluating leading ticks consumes their count, or times out at clock zero. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "evaluate_mk_Ticks"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_mk_Ticks {C F : Type} (traces : List BackendCommon.Tra)
    (expression : ClosLang.Exp) (env : List Value) (state : State C F) :
    evaluate [mkTicks traces expression] env state =
      if state.clock < traces.length then (.err (.abort .timeoutError), { state with clock := 0 })
      else evaluate [expression] env (decClock traces.length state) := by
  induction traces generalizing state with
  | nil => simp [mkTicks, decClock]
  | cons trace rest ih =>
    by_cases zero : state.clock = 0
    · cases state
      simp_all [mkTicks, evaluate]
    · rw [mkTicks, evaluate]
      simp only [zero, if_false]
      rw [ih]
      simp only [List.length_cons, decClock]
      by_cases short : state.clock < rest.length + 1
      · have short' : state.clock - 1 < rest.length := by omega
        simp [short, short']
      · have enough : ¬ state.clock - 1 < rest.length := by omega
        have subtract : state.clock - 1 - rest.length = state.clock - (rest.length + 1) := by omega
        simp [short, enough, subtract]

/-- Result relation used by the original tick-removal evaluator simulation. -/
def ResultRel : Result (List Value) Value → Result (List Value) Value → Prop
  | .val left, .val right => List.Forall₂ ValueRel left right
  | .err (.raise left), .err (.raise right) => ValueRel left right
  | .err (.abort left), .err (.abort right) => left = right
  | _, _ => False

/-- The empty-list case of the reverse tick-removal simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_ticks_nil {C F : Type} (envTarget : List Value)
    (target : State C F) (targetResult : Result (List Value) Value) (targetNext : State C F)
    (envSource : List Value) (source : State C F) (sourceCode : List ClosLang.Exp)
    (premises : evaluate [] envTarget target = (targetResult, targetNext) ∧
      List.Forall₂ ValueRel envSource envTarget ∧ StateRel source target ∧ CodeRel sourceCode []) :
    ∃ extra sourceResult sourceNext,
      evaluate sourceCode envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
      ResultRel sourceResult targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, _, states, code⟩ := premises
  simp [evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  have empty : sourceCode = [] := by
    have length := code_rel_IMP_LENGTH sourceCode [] code
    simpa using length
  subst sourceCode
  exact ⟨0, .val [], source, by simp [evaluate], .nil, states⟩

end Flapjack.Compiler.Backend.ClosTicks
