module

public import Flapjack.Compiler.Backend.ClosTicks.Proofs.Primitive
public import Flapjack.Compiler.Backend.ClosTicks.Proofs.EvaluateSequence

@[expose] public section

/-! Operation cases of the tick-removal evaluator simulation. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- An operation produced by tick removal came from one under leading ticks. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_Op_IMP_mk_Ticks"]
theorem remove_ticks_Op_IMP_mk_Ticks (expression : ClosLang.Exp) (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp)
    (removed : [ClosLang.Exp.op trace op args] = removeList [expression]) :
    ∃ traces sourceArgs, expression = mkTicks traces (.op trace op sourceArgs) ∧ args = removeList sourceArgs := by
  cases expression
  case tick outer inner =>
    have innerRemoved : [ClosLang.Exp.op trace op args] = removeList [inner] := by
      simpa [removeList, removeSing] using removed
    obtain ⟨traces, sourceArgs, equal, argsEqual⟩ := remove_ticks_Op_IMP_mk_Ticks inner trace op args innerRemoved
    exact ⟨outer :: traces, sourceArgs, by simp [mkTicks, equal], argsEqual⟩
  case op actualTrace actualOp sourceArgs =>
    simp [removeList, removeSing] at removed
    obtain ⟨rfl, rfl, rfl⟩ := removed
    exact ⟨[], sourceArgs, rfl, rfl⟩
  all_goals simp [removeList, removeSing] at removed
termination_by sizeOf expression

/-- Ordinary operations simulate after related argument evaluation. This
Flapjack helper isolates the non-install, non-forcing dispatcher branch of
the original operation case. -/
theorem evaluate_ordinary_op {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (envTarget : List Value) (target : State C F)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (envSource : List Value) (source : State C F) (code : List ClosLang.Exp),
      evaluate args envTarget target = (result, next) ∧ List.Forall₂ ValueRel envSource envTarget ∧
        StateRel source target ∧ CodeRel code args →
      ∃ extra sourceResult sourceNext,
        evaluate code envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
        ResultRel sourceResult result ∧ StateRel sourceNext next)
    (result : Result (List Value) Value) (targetNext : State C F)
    (envSource : List Value) (source : State C F) (sourceCode : List ClosLang.Exp)
    (premises : evaluate [.op trace op args] envTarget target = (result, targetNext) ∧
      List.Forall₂ ValueRel envSource envTarget ∧ StateRel source target ∧
      CodeRel sourceCode [.op trace op args]) :
    ∃ extra sourceResult sourceNext,
      evaluate sourceCode envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
      ResultRel sourceResult result ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have length := code_rel_IMP_LENGTH sourceCode [.op trace op args] code
  have singleton : ∃ expression, sourceCode = [expression] := by
    cases sourceCode with
    | nil => simp at length
    | cons first rest =>
      cases rest with
      | nil => exact ⟨first, rfl⟩
      | cons second rest => simp at length
  obtain ⟨expression, rfl⟩ := singleton
  obtain ⟨traces, sourceArgs, rfl, argsCode⟩ := remove_ticks_Op_IMP_mk_Ticks expression trace op args code
  have wrapped (extra : Nat) : evaluate [mkTicks traces (.op trace op sourceArgs)] envSource
      { source with clock := source.clock + (extra + traces.length) } =
      evaluate [.op trace op sourceArgs] envSource { source with clock := source.clock + extra } := by
    rw [evaluate_mk_Ticks]
    have enough : ¬ source.clock + (extra + traces.length) < traces.length := by omega
    have clocks : source.clock + (extra + traces.length) - traces.length = source.clock + extra := by omega
    simp [decClock, enough, clocks]
  rw [evaluate_ordinaryOp_eq trace op _ _ _ notInstall notForce] at run
  cases argsRun : evaluate args envTarget target with
  | mk argsResult targetMiddle =>
    obtain ⟨extra, sourceArgsResult, sourceMiddle, sourceArgsRun, argsRel, middleRel⟩ :=
      argsIH argsResult targetMiddle envSource source sourceArgs ⟨argsRun, envRel, states, argsCode⟩
    rw [argsRun] at run
    cases argsResult with
    | err error =>
      cases run
      cases sourceArgsResult with
      | val values => cases error <;> simp [ResultRel] at argsRel
      | err sourceError =>
        refine ⟨extra + traces.length, .err sourceError, sourceMiddle, ?_, argsRel, middleRel⟩
        rw [wrapped, evaluate_ordinaryOp_eq trace op _ _ _ notInstall notForce, sourceArgsRun]
    | val values =>
      cases sourceArgsResult with
      | err error => cases error <;> simp [ResultRel] at argsRel
      | val sourceValues =>
        have step := PrimitivePort.doAppLemma sourceMiddle targetMiddle sourceValues.reverse values.reverse op
          ⟨middleRel, List.rel_reverse argsRel⟩
        cases appRun : doApp op values.reverse targetMiddle with
        | err error =>
          simp only [appRun] at step run
          cases run
          obtain ⟨sourceError, sourceApp, errors⟩ := step
          refine ⟨extra + traces.length, .err sourceError, sourceMiddle, ?_, ?_, middleRel⟩
          · rw [wrapped, evaluate_ordinaryOp_eq trace op _ _ _ notInstall notForce, sourceArgsRun]
            simp [sourceApp]
          · cases error <;> cases sourceError <;>
              simp_all [ResultRel, Flapjack.SemanticPrimitivesProps.excRel]
        | val pair =>
          rcases pair with ⟨value, last⟩
          simp only [appRun] at step run
          cases run
          obtain ⟨sourceValue, sourceLast, valuesRel, lastRel, sourceApp⟩ := step
          refine ⟨extra + traces.length, .val [sourceValue], sourceLast, ?_, .cons valuesRel .nil, lastRel⟩
          rw [wrapped, evaluate_ordinaryOp_eq trace op _ _ _ notInstall notForce, sourceArgsRun]
          simp [sourceApp]

end Flapjack.Compiler.Backend.ClosTicks
