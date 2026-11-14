module

public import Flapjack.Compiler.Backend.ClosTicks.Proofs.Evaluate

@[expose] public section

/-! Closure-construction case of the tick-removal evaluator simulation. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- A function produced by tick removal came from one under leading ticks. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_Fn_IMP_mk_Ticks"]
theorem remove_ticks_Fn_IMP_mk_Ticks (expression : ClosLang.Exp) (name : Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp)
    (removed : [ClosLang.Exp.fn name location selected arity body] = removeSource [expression]) :
    ∃ traces sourceBody, expression = mkTicks traces (.fn name location selected arity sourceBody) ∧
      [body] = removeSource [sourceBody] := by
  cases expression
  case tick outer inner =>
    have innerRemoved : [ClosLang.Exp.fn name location selected arity body] = removeSource [inner] := by
      simpa [removeList, removeSing] using removed
    obtain ⟨traces, sourceBody, equal, bodyEqual⟩ :=
      remove_ticks_Fn_IMP_mk_Ticks inner name location selected arity body innerRemoved
    exact ⟨outer :: traces, sourceBody, by simp [mkTicks, equal], bodyEqual⟩
  case fn actualName actualLocation actualSelected actualArity sourceBody =>
    simp [removeList, removeSing] at removed
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := removed
    exact ⟨[], sourceBody, rfl, by simp [removeList]⟩
  all_goals simp [removeList, removeSing] at removed
termination_by sizeOf expression

/-- Related environments agree on target lookup failure or return related values. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "lookup_vars_lemma"]
theorem lookup_vars_lemma (indices : List Nat) (source target : List Value)
    (related : List.Forall₂ ValueRel source target) :
    match lookupVars indices target with
    | none => lookupVars indices source = none
    | some values => ∃ sourceValues, List.Forall₂ ValueRel sourceValues values ∧
        lookupVars indices source = some sourceValues := by
  have lookupRel : Flapjack.optionRel (List.Forall₂ ValueRel)
      (lookupVars indices source) (lookupVars indices target) := by
    induction indices with
    | nil => simp [lookupVars, Flapjack.optionRel]
    | cons index rest ih =>
      have head := Flapjack.forall₂_lookupRel related index
      cases left : source[index]? <;> cases right : target[index]? <;>
        simp [Flapjack.optionRel, left, right] at head
      · simp [lookupVars, left, right, Flapjack.optionRel]
      · rename_i value nextValue
        cases leftTail : lookupVars rest source <;> cases rightTail : lookupVars rest target <;>
          simp [Flapjack.optionRel, leftTail, rightTail] at ih
        · simp [lookupVars, left, right, leftTail, rightTail, Flapjack.optionRel]
        · simp [lookupVars, left, right, leftTail, rightTail, Flapjack.optionRel, head, ih]

  cases left : lookupVars indices source <;> cases right : lookupVars indices target <;>
    simp_all [Flapjack.optionRel]

namespace FnPort
/-- The closure state has the reviewed canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end FnPort

/-- The function-construction case of the reverse tick-removal simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_ticks_fn {C F : Type} (name : Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp)
    (envTarget : List Value) (target : State C F) (result : Result (List Value) Value) (targetNext : State C F)
    (envSource : List Value) (source : State C F) (sourceCode : List ClosLang.Exp)
    (premises : evaluate [.fn name location selected arity body] envTarget target = (result, targetNext) ∧
      List.Forall₂ ValueRel envSource envTarget ∧ StateRel source target ∧
      CodeRel sourceCode [.fn name location selected arity body]) :
    ∃ extra sourceResult sourceNext,
      evaluate sourceCode envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
      ResultRel sourceResult result ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have length := code_rel_IMP_LENGTH sourceCode [.fn name location selected arity body] code
  have singleton : ∃ expression, sourceCode = [expression] := by
    cases sourceCode with
    | nil => simp at length
    | cons first rest =>
      cases rest with
      | nil => exact ⟨first, rfl⟩
      | cons second rest => simp at length
  obtain ⟨expression, rfl⟩ := singleton
  obtain ⟨traces, sourceBody, rfl, bodyCode⟩ :=
    remove_ticks_Fn_IMP_mk_Ticks expression name location selected arity body code
  have wrapped : evaluate [mkTicks traces (.fn name location selected arity sourceBody)] envSource
      { source with clock := source.clock + traces.length } =
      evaluate [.fn name location selected arity sourceBody] envSource source := by
    rw [evaluate_mk_Ticks]
    simp [decClock]
  have maxEq : target.maxApp = source.maxApp := states.2.2.2.1
  cases selected with
  | none =>
    by_cases arityOk : arity ≤ target.maxApp ∧ arity ≠ 0
    · simp [evaluate, arityOk] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨traces.length, .val [.closure location [] envSource arity sourceBody], source, ?_, ?_, states⟩
      · rw [wrapped]
        simp [evaluate, ← maxEq, arityOk]
      · exact .cons (.closure location [] [] envSource envTarget arity sourceBody body envRel .nil bodyCode) .nil
    · simp [evaluate, arityOk] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨traces.length, .err (.abort .typeError), source, ?_, rfl, states⟩
      rw [wrapped]
      simp [evaluate, ← maxEq, arityOk]
  | some indices =>
    by_cases arityOk : arity ≤ target.maxApp ∧ arity ≠ 0
    · have captureRel := lookup_vars_lemma indices envSource envTarget envRel
      cases capture : lookupVars indices envTarget with
      | none =>
        cases sourceCapture : lookupVars indices envSource with
        | none =>
          simp [evaluate, arityOk, capture] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨traces.length, .err (.abort .typeError), source, ?_, rfl, states⟩
          rw [wrapped]
          simp [evaluate, ← maxEq, arityOk, sourceCapture]
        | some values => simp [capture, sourceCapture] at captureRel
      | some values =>
        cases sourceCapture : lookupVars indices envSource with
        | none => simp [capture, sourceCapture] at captureRel
        | some sourceValues =>
          have captures : List.Forall₂ ValueRel sourceValues values := by
            simpa [capture, sourceCapture] using captureRel
          simp [evaluate, arityOk, capture] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨traces.length, .val [.closure location [] sourceValues arity sourceBody], source, ?_, ?_, states⟩
          · rw [wrapped]
            simp [evaluate, ← maxEq, arityOk, sourceCapture]
          · exact .cons (.closure location [] [] sourceValues values arity sourceBody body captures .nil bodyCode) .nil
    · simp [evaluate, arityOk] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨traces.length, .err (.abort .typeError), source, ?_, rfl, states⟩
      rw [wrapped]
      simp [evaluate, ← maxEq, arityOk]

end Flapjack.Compiler.Backend.ClosTicks
