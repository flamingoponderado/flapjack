module

public import Flapjack.Compiler.Backend.ClosTicks.Proofs.EvaluateOp
public import Flapjack.Compiler.Backend.ClosTicks.Proofs.Force

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section

/-! Thunk-forcing path of the tick-removal evaluator simulation. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- The thunk-forcing branch of the operation simulation. This is Flapjack
infrastructure for assembling the original operation induction case. -/
theorem evaluate_force {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (envTarget : List Value) (target : State C F)
    (argsIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (envSource : List Value) (source : State C F) (code : List ClosLang.Exp),
      evaluate args envTarget target = (result, next) ∧ List.Forall₂ ValueRel envSource envTarget ∧
        StateRel source target ∧ CodeRel code args →
      ∃ extra sourceResult sourceNext,
        evaluate code envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
        ResultRel sourceResult result ∧ StateRel sourceNext next)
    (forceIH : ∀ (values : List Value) (middle : State C F) (value : Value),
      evaluate args envTarget target = (.val values, middle) →
      destThunk values middle.refs = .isThunk .notEvaluated value →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (envSource : List Value) (source : State C F) (code : List ClosLang.Exp),
        evaluate [appUnit (.var .none 0)] [value] middle = (result, next) ∧
          List.Forall₂ ValueRel envSource [value] ∧ StateRel source middle ∧
          CodeRel code [appUnit (.var .none 0)] →
        ∃ extra sourceResult sourceNext,
          evaluate code envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
          ResultRel sourceResult result ∧ StateRel sourceNext next)
    (result : Result (List Value) Value) (targetNext : State C F)
    (envSource : List Value) (source : State C F) (sourceCode : List ClosLang.Exp)
    (premises : evaluate [.op trace (.thunkOp .forceThunk) args] envTarget target = (result, targetNext) ∧
      List.Forall₂ ValueRel envSource envTarget ∧ StateRel source target ∧
      CodeRel sourceCode [.op trace (.thunkOp .forceThunk) args]) :
    ∃ extra sourceResult sourceNext,
      evaluate sourceCode envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
      ResultRel sourceResult result ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have length := code_rel_IMP_LENGTH sourceCode [.op trace (.thunkOp .forceThunk) args] code
  have singleton : ∃ expression, sourceCode = [expression] := by
    cases sourceCode with
    | nil => simp at length
    | cons first rest =>
      cases rest with
      | nil => exact ⟨first, rfl⟩
      | cons second rest => simp at length
  obtain ⟨expression, rfl⟩ := singleton
  obtain ⟨traces, sourceArgs, rfl, argsCode⟩ :=
    remove_ticks_Op_IMP_mk_Ticks expression trace (.thunkOp .forceThunk) args code
  have wrapped (extra : Nat) : evaluate [mkTicks traces (.op trace (.thunkOp .forceThunk) sourceArgs)] envSource
      { source with clock := source.clock + (extra + traces.length) } =
      evaluate [.op trace (.thunkOp .forceThunk) sourceArgs] envSource { source with clock := source.clock + extra } := by
    rw [evaluate_mk_Ticks]
    have enough : ¬ source.clock + (extra + traces.length) < traces.length := by omega
    have clocks : source.clock + (extra + traces.length) - traces.length = source.clock + extra := by omega
    simp [decClock, enough, clocks]
  cases argsRun : evaluate args envTarget target with
  | mk argsResult targetMiddle =>
    obtain ⟨extra, sourceArgsResult, sourceMiddle, sourceArgsRun, argsRel, middleRel⟩ :=
      argsIH argsResult targetMiddle envSource source sourceArgs ⟨argsRun, envRel, states, argsCode⟩
    cases argsResult with
    | err error =>
      rw [evaluate, fixClock_evaluate, argsRun] at run
      cases run
      cases sourceArgsResult with
      | val values => cases error <;> simp [ResultRel] at argsRel
      | err sourceError =>
        refine ⟨extra + traces.length, .err sourceError, sourceMiddle, ?_, argsRel, middleRel⟩
        rw [wrapped, evaluate, fixClock_evaluate, sourceArgsRun]
    | val values =>
      cases sourceArgsResult with
      | err error => cases error <;> simp [ResultRel] at argsRel
      | val sourceValues =>
        have inspected := destThunk_list_related sourceMiddle targetMiddle sourceValues values argsRel middleRel
        rw [evaluate, fixClock_evaluate, argsRun] at run
        dsimp only at run
        cases targetThunk : destThunk values targetMiddle.refs with
        | badRef =>
          cases sourceThunk : destThunk sourceValues sourceMiddle.refs <;>
            simp [DestThunkRel, sourceThunk, targetThunk] at inspected
          rw [targetThunk] at run
          cases run
          refine ⟨extra + traces.length, .err (.abort .typeError), sourceMiddle, ?_, rfl, middleRel⟩
          rw [wrapped, evaluate, fixClock_evaluate, sourceArgsRun]
          dsimp only
          rw [sourceThunk]
          simp
        | notThunk =>
          cases sourceThunk : destThunk sourceValues sourceMiddle.refs <;>
            simp [DestThunkRel, sourceThunk, targetThunk] at inspected
          rw [targetThunk] at run
          cases run
          refine ⟨extra + traces.length, .err (.abort .typeError), sourceMiddle, ?_, rfl, middleRel⟩
          rw [wrapped, evaluate, fixClock_evaluate, sourceArgsRun]
          dsimp only
          rw [sourceThunk]
          simp
        | isThunk mode value =>
          cases sourceThunk : destThunk sourceValues sourceMiddle.refs with
          | badRef => simp [DestThunkRel, sourceThunk, targetThunk] at inspected
          | notThunk => simp [DestThunkRel, sourceThunk, targetThunk] at inspected
          | isThunk sourceMode sourceValue =>
            have rel : sourceMode = mode ∧ ValueRel sourceValue value := by
              simpa [DestThunkRel, sourceThunk, targetThunk] using inspected
            obtain ⟨rfl, valueRel⟩ := rel
            cases sourceMode with
            | evaluated =>
              rw [targetThunk] at run
              cases run
              refine ⟨extra + traces.length, .val [sourceValue], sourceMiddle, ?_, .cons valueRel .nil, middleRel⟩
              rw [wrapped, evaluate, fixClock_evaluate, sourceArgsRun]
              dsimp only
              rw [sourceThunk]
            | notEvaluated =>
              cases forceRun : evaluate [appUnit (.var .none 0)] [value] targetMiddle with
              | mk forceResult targetLast =>
                obtain ⟨forceExtra, sourceForceResult, sourceLast, sourceForceRun, forceRel, lastRel⟩ :=
                  forceIH values targetMiddle value argsRun targetThunk forceResult targetLast [sourceValue] sourceMiddle
                    [appUnit (.var .none 0)] ⟨forceRun, .cons valueRel .nil, middleRel,
                      by simp [CodeRel, removeList, removeSing, appUnit]⟩
                have shiftedArgs := (evaluate_addClock (C := C) (F := F)).1 sourceArgs envSource
                  { source with clock := source.clock + extra } sourceMiddle (.val sourceValues) forceExtra sourceArgsRun (by simp)
                have sourceArgsShift : evaluate sourceArgs envSource
                    { source with clock := source.clock + (extra + forceExtra) } =
                      (.val sourceValues, { sourceMiddle with clock := sourceMiddle.clock + forceExtra }) := by
                  simpa [Nat.add_assoc] using shiftedArgs
                cases forceResult with
                | err error =>
                  rw [targetThunk] at run
                  dsimp only at run
                  rw [forceRun] at run
                  cases run
                  cases sourceForceResult with
                  | val vals => cases error <;> simp [ResultRel] at forceRel
                  | err sourceError =>
                    refine ⟨extra + forceExtra + traces.length, .err sourceError, sourceLast, ?_, forceRel, lastRel⟩
                    rw [wrapped, evaluate, fixClock_evaluate, sourceArgsShift]
                    dsimp only
                    rw [sourceThunk]
                    dsimp only
                    rw [sourceForceRun]
                | val forced =>
                  cases sourceForceResult with
                  | err error => cases error <;> simp [ResultRel] at forceRel
                  | val sourceForced =>
                    have update := updateThunk_related sourceLast targetLast sourceValues values sourceForced forced
                      argsRel forceRel lastRel
                    cases targetUpdate : updateThunk values targetLast.refs forced with
                    | none =>
                      cases sourceUpdate : updateThunk sourceValues sourceLast.refs sourceForced with
                      | none =>
                        rw [targetThunk] at run
                        dsimp only at run
                        rw [forceRun] at run
                        dsimp only at run
                        rw [targetUpdate] at run
                        cases run
                        refine ⟨extra + forceExtra + traces.length, .err (.abort .typeError), sourceLast, ?_, rfl, lastRel⟩
                        rw [wrapped, evaluate, fixClock_evaluate, sourceArgsShift]
                        dsimp only
                        rw [sourceThunk]
                        dsimp only
                        rw [sourceForceRun]
                        dsimp only
                        rw [sourceUpdate]
                        simp
                      | some refs =>
                        rw [sourceUpdate] at update
                        obtain ⟨targetRefs, targetRun, _⟩ := update
                        simp [targetUpdate] at targetRun
                    | some targetRefs =>
                      cases sourceUpdate : updateThunk sourceValues sourceLast.refs sourceForced with
                      | none => simp [sourceUpdate, targetUpdate] at update
                      | some sourceRefs =>
                        rw [sourceUpdate] at update
                        obtain ⟨actualTargetRefs, targetRun, updatedRel⟩ := update
                        have equal : actualTargetRefs = targetRefs := by simpa [targetUpdate] using targetRun.symm
                        subst targetRefs
                        rw [targetThunk] at run
                        dsimp only at run
                        rw [forceRun] at run
                        dsimp only at run
                        rw [targetUpdate] at run
                        cases run
                        refine ⟨extra + forceExtra + traces.length, .val sourceForced,
                          { sourceLast with refs := sourceRefs }, ?_, forceRel, updatedRel⟩
                        rw [wrapped, evaluate, fixClock_evaluate, sourceArgsShift]
                        dsimp only
                        rw [sourceThunk]
                        dsimp only
                        rw [sourceForceRun]
                        dsimp only
                        rw [sourceUpdate]

end Flapjack.Compiler.Backend.ClosTicks
