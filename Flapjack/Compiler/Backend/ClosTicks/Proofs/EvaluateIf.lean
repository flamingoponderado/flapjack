module

public import Flapjack.Compiler.Backend.ClosTicks.Proofs.EvaluateSequence
public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBoolean

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section

/-! Conditional case of the tick-removal evaluator simulation. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

instance evaluateIfInst1 : Nonempty ClosLang.Exp := ⟨.var .none 0⟩

/-- A conditional produced by tick removal came from one under leading ticks. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_If_IMP_mk_Ticks"]
theorem remove_ticks_If_IMP_mk_Ticks (expression : ClosLang.Exp) (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp)
    (removed : [ClosLang.Exp.ifThenElse trace condition yes no] = removeList [expression]) :
    ∃ traces sourceCondition sourceYes sourceNo,
      expression = mkTicks traces (.ifThenElse trace sourceCondition sourceYes sourceNo) ∧
      condition = Flapjack.holHd (removeList [sourceCondition]) ∧
      yes = Flapjack.holHd (removeList [sourceYes]) ∧ no = Flapjack.holHd (removeList [sourceNo]) := by
  cases expression
  case tick outer inner =>
    have innerRemoved : [ClosLang.Exp.ifThenElse trace condition yes no] = removeList [inner] := by
      simpa [removeList, removeSing] using removed
    obtain ⟨traces, sourceCondition, sourceYes, sourceNo, equal, condEqual, yesEqual, noEqual⟩ :=
      remove_ticks_If_IMP_mk_Ticks inner trace condition yes no innerRemoved
    exact ⟨outer :: traces, sourceCondition, sourceYes, sourceNo, by simp [mkTicks, equal],
      condEqual, yesEqual, noEqual⟩
  case ifThenElse actualTrace sourceCondition sourceYes sourceNo =>
    simp [removeList, removeSing] at removed
    obtain ⟨rfl, rfl, rfl, rfl⟩ := removed
    exact ⟨[], sourceCondition, sourceYes, sourceNo, rfl, by simp [removeList, Flapjack.holHd],
      by simp [removeList, Flapjack.holHd], by simp [removeList, Flapjack.holHd]⟩
  all_goals simp [removeList, removeSing] at removed
termination_by sizeOf expression

/-- Related values have the same Boolean observation. This is Flapjack
infrastructure for the conditional case rather than a separate HOL theorem. -/
theorem valueRel_asBool {left right : Value} (related : ValueRel left right) :
    asBool left = asBool right := by
  cases related with
  | block tag left right entries =>
    cases entries with
    | nil => rfl
    | cons head tail => cases tag <;> simp [asBool]
  | number _ | word64 _ | byteVector _ | refPtr _ _ => rfl
  | closure => rfl
  | recclosure => rfl

namespace IfPort
/-- The closure state has the reviewed canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end IfPort

/-- The conditional case of the reverse tick-removal simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_ticks_if {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (envTarget : List Value) (target : State C F)
    (conditionIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (envSource : List Value) (source : State C F) (code : List ClosLang.Exp),
      evaluate [condition] envTarget target = (result, next) ∧ List.Forall₂ ValueRel envSource envTarget ∧
        StateRel source target ∧ CodeRel code [condition] →
      ∃ extra sourceResult sourceNext,
        evaluate code envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
        ResultRel sourceResult result ∧ StateRel sourceNext next)
    (yesIH : ∀ (values : List Value) (middle : State C F),
      evaluate [condition] envTarget target = (.val values, middle) →
      boolValue true = @Flapjack.holHd Value ⟨unitValue⟩ values →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (envSource : List Value) (source : State C F) (code : List ClosLang.Exp),
        evaluate [yes] envTarget middle = (result, next) ∧ List.Forall₂ ValueRel envSource envTarget ∧
          StateRel source middle ∧ CodeRel code [yes] →
        ∃ extra sourceResult sourceNext,
          evaluate code envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
          ResultRel sourceResult result ∧ StateRel sourceNext next)
    (noIH : ∀ (values : List Value) (middle : State C F),
      evaluate [condition] envTarget target = (.val values, middle) →
      boolValue true ≠ @Flapjack.holHd Value ⟨unitValue⟩ values →
      boolValue false = @Flapjack.holHd Value ⟨unitValue⟩ values →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (envSource : List Value) (source : State C F) (code : List ClosLang.Exp),
        evaluate [no] envTarget middle = (result, next) ∧ List.Forall₂ ValueRel envSource envTarget ∧
          StateRel source middle ∧ CodeRel code [no] →
        ∃ extra sourceResult sourceNext,
          evaluate code envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
          ResultRel sourceResult result ∧ StateRel sourceNext next)
    (result : Result (List Value) Value) (targetNext : State C F)
    (envSource : List Value) (source : State C F) (sourceCode : List ClosLang.Exp)
    (premises : evaluate [.ifThenElse trace condition yes no] envTarget target = (result, targetNext) ∧
      List.Forall₂ ValueRel envSource envTarget ∧ StateRel source target ∧
      CodeRel sourceCode [.ifThenElse trace condition yes no]) :
    ∃ extra sourceResult sourceNext,
      evaluate sourceCode envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
      ResultRel sourceResult result ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have length := code_rel_IMP_LENGTH sourceCode [.ifThenElse trace condition yes no] code
  have singleton : ∃ expression, sourceCode = [expression] := by
    cases sourceCode with
    | nil => simp at length
    | cons first rest =>
      cases rest with
      | nil => exact ⟨first, rfl⟩
      | cons second rest => simp at length
  obtain ⟨expression, rfl⟩ := singleton
  obtain ⟨traces, sourceCondition, sourceYes, sourceNo, rfl, condCode, yesCode, noCode⟩ :=
    remove_ticks_If_IMP_mk_Ticks expression trace condition yes no code
  simp only [removeList, Flapjack.holHd] at condCode yesCode noCode
  have wrapped (extra : Nat) : evaluate [mkTicks traces (.ifThenElse trace sourceCondition sourceYes sourceNo)] envSource
      { source with clock := source.clock + (extra + traces.length) } =
      evaluate [.ifThenElse trace sourceCondition sourceYes sourceNo] envSource { source with clock := source.clock + extra } := by
    rw [evaluate_mk_Ticks]
    have enough : ¬ source.clock + (extra + traces.length) < traces.length := by omega
    have clocks : source.clock + (extra + traces.length) - traces.length = source.clock + extra := by omega
    simp [decClock, enough, clocks]
  cases conditionRun : evaluate [condition] envTarget target with
  | mk conditionResult targetMiddle =>
    obtain ⟨extra, sourceResult, sourceMiddle, sourceRun, related, middleRel⟩ :=
      conditionIH conditionResult targetMiddle envSource source [sourceCondition]
        ⟨conditionRun, envRel, states, by simp [CodeRel, removeList, condCode]⟩
    cases conditionResult with
    | err error =>
      rw [evaluate, fixClock_evaluate, conditionRun] at run
      cases run
      cases sourceResult with
      | val values => cases error <;> simp [ResultRel] at related
      | err sourceError =>
        refine ⟨extra + traces.length, .err sourceError, sourceMiddle, ?_, related, middleRel⟩
        rw [wrapped, evaluate, fixClock_evaluate, sourceRun]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value condition envTarget target targetMiddle values conditionRun
      cases sourceResult with
      | err error => cases error <;> simp [ResultRel] at related
      | val sourceValues =>
        cases related with
        | cons valueRel tailRel =>
          cases tailRel
          rename_i sourceValue
          have boolEq : asBool sourceValue = asBool value := valueRel_asBool valueRel
          cases decision : asBool value with
          | none =>
            have sourceDecision : asBool sourceValue = none := boolEq.trans decision
            rw [evaluate, fixClock_evaluate, conditionRun] at run
            simp [decision] at run
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨extra + traces.length, .err (.abort .typeError), sourceMiddle, ?_, rfl, middleRel⟩
            rw [wrapped, evaluate, fixClock_evaluate, sourceRun]
            simp [sourceDecision]
          | some flag =>
            have sourceDecision : asBool sourceValue = some flag := boolEq.trans decision
            have shifted (branchExtra : Nat) : evaluate [sourceCondition] envSource
                { source with clock := source.clock + (extra + branchExtra) } =
                  (.val [sourceValue], { sourceMiddle with clock := sourceMiddle.clock + branchExtra }) := by
              have h := (evaluate_addClock (C := C) (F := F)).1 [sourceCondition] envSource
                { source with clock := source.clock + extra } sourceMiddle (.val [sourceValue]) branchExtra sourceRun (by simp)
              simpa [Nat.add_assoc] using h
            cases flag with
            | false =>
              have valueEq : boolValue false = value := ((asBool_eq_some value false).mp decision).symm
              have notTrue : boolValue true ≠ value := by
                rw [← valueEq]
                simp [boolValue, BackendCommon.trueTag, BackendCommon.falseTag]
              have branchRun : evaluate [no] envTarget targetMiddle = (result, targetNext) := by
                rw [evaluate, fixClock_evaluate, conditionRun] at run
                simpa [decision] using run
              obtain ⟨branchExtra, sourceBranchResult, sourceLast, sourceBranchRun, branchRel, lastRel⟩ :=
                noIH [value] targetMiddle conditionRun (by simpa [Flapjack.holHd] using notTrue)
                  (by simpa [Flapjack.holHd] using valueEq) result targetNext envSource sourceMiddle [sourceNo]
                  ⟨branchRun, envRel, middleRel, by simp [CodeRel, removeList, noCode]⟩
              refine ⟨extra + branchExtra + traces.length, sourceBranchResult, sourceLast, ?_, branchRel, lastRel⟩
              rw [wrapped, evaluate, fixClock_evaluate, shifted branchExtra]
              simpa [sourceDecision] using sourceBranchRun
            | true =>
              have valueEq : boolValue true = value := ((asBool_eq_some value true).mp decision).symm
              have branchRun : evaluate [yes] envTarget targetMiddle = (result, targetNext) := by
                rw [evaluate, fixClock_evaluate, conditionRun] at run
                simpa [decision] using run
              obtain ⟨branchExtra, sourceBranchResult, sourceLast, sourceBranchRun, branchRel, lastRel⟩ :=
                yesIH [value] targetMiddle conditionRun (by simpa [Flapjack.holHd] using valueEq)
                  result targetNext envSource sourceMiddle [sourceYes]
                  ⟨branchRun, envRel, middleRel, by simp [CodeRel, removeList, yesCode]⟩
              refine ⟨extra + branchExtra + traces.length, sourceBranchResult, sourceLast, ?_, branchRel, lastRel⟩
              rw [wrapped, evaluate, fixClock_evaluate, shifted branchExtra]
              simpa [sourceDecision] using sourceBranchRun

end Flapjack.Compiler.Backend.ClosTicks
