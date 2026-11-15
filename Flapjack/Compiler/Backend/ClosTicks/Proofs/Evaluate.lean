module

public import Flapjack.Compiler.Backend.ClosTicks.Proofs.Relations
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
public import Mathlib.Tactic

public import Flapjack.Misc.ListLookupRel

@[expose] public section

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
    removeSource [mkTicks traces expression] = removeSource [expression] := by
  induction traces with
  | nil => rfl
  | cons trace rest ih => simpa [mkTicks, removeList, removeSing] using ih

/-- If tick removal produces a variable, its source consists of that variable
preceded by zero or more ticks. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_Var_IMP_mk_Ticks"]
theorem remove_ticks_Var_IMP_mk_Ticks (expression : ClosLang.Exp) (trace : BackendCommon.Tra)
    (index : Nat) (removed : [ClosLang.Exp.var trace index] = removeSource [expression]) :
    ∃ traces, expression = mkTicks traces (.var trace index) := by
  cases expression
  case tick outer body =>
    have bodyRemoved : [ClosLang.Exp.var trace index] = removeSource [body] := by
      simpa [removeList, removeSing] using removed
    obtain ⟨traces, equal⟩ := remove_ticks_Var_IMP_mk_Ticks body trace index bodyRemoved
    exact ⟨outer :: traces, by simp [mkTicks, equal]⟩
  case var actualTrace actualIndex =>
    simp [removeList, removeSing] at removed
    obtain ⟨rfl, rfl⟩ := removed
    exact ⟨[], rfl⟩
  all_goals simp [removeList, removeSing] at removed
termination_by sizeOf expression

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

/-- The variable case of the reverse tick-removal simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_ticks_var {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (envTarget : List Value) (target : State C F) (targetResult : Result (List Value) Value)
    (targetNext : State C F) (envSource : List Value) (source : State C F)
    (sourceCode : List ClosLang.Exp)
    (premises : evaluate [.var trace index] envTarget target = (targetResult, targetNext) ∧
      List.Forall₂ ValueRel envSource envTarget ∧ StateRel source target ∧
      CodeRel sourceCode [.var trace index]) :
    ∃ extra sourceResult sourceNext,
      evaluate sourceCode envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
      ResultRel sourceResult targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have length := code_rel_IMP_LENGTH sourceCode [.var trace index] code
  have singleton : ∃ e, sourceCode = [e] := by
    cases sourceCode with
    | nil => simp at length
    | cons first rest =>
      cases rest with
      | nil => exact ⟨first, rfl⟩
      | cons second rest => simp at length
  obtain ⟨expression, rfl⟩ := singleton
  have removed : [ClosLang.Exp.var trace index] = removeSource [expression] := by
    simpa [CodeRel] using code
  obtain ⟨traces, rfl⟩ := remove_ticks_Var_IMP_mk_Ticks expression trace index removed
  have lookup := Flapjack.forall₂_lookupRel envRel index
  have restored : decClock traces.length { source with clock := source.clock + traces.length } = source := by
    simp [decClock]
  cases found : envTarget[index]? with
  | none =>
    cases sourceFound : envSource[index]? with
    | some value => simp [Flapjack.optionRel, sourceFound, found] at lookup
    | none =>
      simp [evaluate, found] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨traces.length, .err (.abort .typeError), source, ?_, rfl, states⟩
      rw [evaluate_mk_Ticks]
      simp [restored, evaluate, sourceFound]
  | some value =>
    cases sourceFound : envSource[index]? with
    | none => simp [Flapjack.optionRel, sourceFound, found] at lookup
    | some sourceValue =>
      have values : ValueRel sourceValue value := by
        simpa [Flapjack.optionRel, sourceFound, found] using lookup
      simp [evaluate, found] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨traces.length, .val [sourceValue], source, ?_, .cons values .nil, states⟩
      rw [evaluate_mk_Ticks]
      simp [restored, evaluate, sourceFound]

end Flapjack.Compiler.Backend.ClosTicks
