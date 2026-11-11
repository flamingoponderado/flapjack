module

public import Flapjack.Compiler.Backend.ClosTicks.Proofs.EvaluateOp
public import Flapjack.Compiler.Backend.Semantics.ClosProps.SimpleRelations
public import Flapjack.Compiler.Backend.ClosTicks.Proofs.Install
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
public import Flapjack.Compiler.Backend.Semantics.ClosProps.InstallStep

@[expose] public section

/-! Installation path of the tick-removal evaluator simulation. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL (Result)

/-- The installation branch of the operation simulation. This is Flapjack
infrastructure for assembling the original operation induction case. -/
theorem evaluate_install {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (envTarget : List Value) (target : State C F)
    (argsIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (envSource : List Value) (source : State C F) (code : List ClosLang.Exp),
      evaluate args envTarget target = (result, next) ∧ List.Forall₂ ValueRel envSource envTarget ∧
        StateRel source target ∧ CodeRel code args →
      ∃ extra sourceResult sourceNext,
        evaluate code envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
        ResultRel sourceResult result ∧ StateRel sourceNext next)
    (programIH : ∀ (values : List Value) (middle : State C F) (program : List ClosLang.Exp)
        (installed : State C F),
      evaluate args envTarget target = (.val values, middle) →
      doInstall values.reverse middle = (.val program, installed) →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (envSource : List Value) (source : State C F) (code : List ClosLang.Exp),
        evaluate program [] installed = (result, next) ∧ List.Forall₂ ValueRel envSource [] ∧
          StateRel source installed ∧ CodeRel code program →
        ∃ extra sourceResult sourceNext,
          evaluate code envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
          ResultRel sourceResult result ∧ StateRel sourceNext next)
    (result : Result (List Value) Value) (targetNext : State C F)
    (envSource : List Value) (source : State C F) (sourceCode : List ClosLang.Exp)
    (premises : evaluate [.op trace .install args] envTarget target = (result, targetNext) ∧
      List.Forall₂ ValueRel envSource envTarget ∧ StateRel source target ∧
      CodeRel sourceCode [.op trace .install args]) :
    ∃ extra sourceResult sourceNext,
      evaluate sourceCode envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
      ResultRel sourceResult result ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have length := code_rel_IMP_LENGTH sourceCode [.op trace .install args] code
  have singleton : ∃ expression, sourceCode = [expression] := by
    cases sourceCode with
    | nil => simp at length
    | cons first rest =>
      cases rest with
      | nil => exact ⟨first, rfl⟩
      | cons second rest => simp at length
  obtain ⟨expression, rfl⟩ := singleton
  obtain ⟨traces, sourceArgs, rfl, argsCode⟩ := remove_ticks_Op_IMP_mk_Ticks expression trace .install args code
  have wrapped (extra : Nat) : evaluate [mkTicks traces (.op trace .install sourceArgs)] envSource
      { source with clock := source.clock + (extra + traces.length) } =
      evaluate [.op trace .install sourceArgs] envSource { source with clock := source.clock + extra } := by
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
      rw [evaluate_install_eq, argsRun] at run
      cases run
      cases sourceArgsResult with
      | val values => cases error <;> simp [ResultRel] at argsRel
      | err sourceError =>
        refine ⟨extra + traces.length, .err sourceError, sourceMiddle, ?_, argsRel, middleRel⟩
        rw [wrapped, evaluate_install_eq, sourceArgsRun]
    | val values =>
      cases sourceArgsResult with
      | err error => cases error <;> simp [ResultRel] at argsRel
      | val sourceValues =>
        have installs := install_related sourceMiddle targetMiddle sourceValues.reverse values.reverse
          middleRel (List.rel_reverse argsRel)
        cases targetInstall : doInstall values.reverse targetMiddle with
        | mk targetInstallResult targetInstalled =>
          cases sourceInstall : doInstall sourceValues.reverse sourceMiddle with
          | mk sourceInstallResult sourceInstalled =>
            rw [sourceInstall, targetInstall] at installs
            cases targetInstallResult with
            | err error =>
              cases sourceInstallResult with
              | val program => simp [InstallRel] at installs
              | err sourceError =>
                rw [evaluate_install_eq, argsRun] at run
                simp only [runInstalled, targetInstall] at run
                cases run
                refine ⟨extra + traces.length, .err sourceError, sourceInstalled, ?_, ?_, installs.2⟩
                · rw [wrapped, evaluate_install_eq, sourceArgsRun]
                  simp [runInstalled, sourceInstall]
                · cases error <;> cases sourceError <;>
                    simp_all [InstallRel, ResultRel, Flapjack.SemanticPrimitivesProps.excRel]
            | val program =>
              cases sourceInstallResult with
              | err error => simp [InstallRel] at installs
              | val sourceProgram =>
                obtain ⟨sourceNonempty, programRel, installedRel⟩ := installs
                cases programRun : evaluate program [] targetInstalled with
                | mk programResult targetLast =>
                  obtain ⟨programExtra, sourceProgramResult, sourceLast, sourceProgramRun, resultRel, lastRel⟩ :=
                    programIH values targetMiddle program targetInstalled argsRun targetInstall programResult targetLast
                      [] sourceInstalled sourceProgram ⟨programRun, .nil, installedRel, programRel⟩
                  have shiftedArgs := (evaluate_addClock (C := C) (F := F)).1 sourceArgs envSource
                    { source with clock := source.clock + extra } sourceMiddle (.val sourceValues) programExtra sourceArgsRun (by simp)
                  have sourceArgsShift : evaluate sourceArgs envSource
                      { source with clock := source.clock + (extra + programExtra) } =
                        (.val sourceValues, { sourceMiddle with clock := sourceMiddle.clock + programExtra }) := by
                    simpa [Nat.add_assoc] using shiftedArgs
                  have sourceInstallShift := doInstall_success_addClock sourceValues.reverse sourceMiddle sourceInstalled
                    sourceProgram programExtra sourceInstall
                  cases programResult with
                  | err error =>
                    rw [evaluate_install_eq, argsRun] at run
                    simp only [runInstalled, targetInstall, programRun] at run
                    cases run
                    cases sourceProgramResult with
                    | val vals => cases error <;> simp [ResultRel] at resultRel
                    | err sourceError =>
                      refine ⟨extra + programExtra + traces.length, .err sourceError, sourceLast, ?_, resultRel, lastRel⟩
                      rw [wrapped, evaluate_install_eq, sourceArgsShift]
                      simp [runInstalled, sourceInstallShift, sourceProgramRun]
                  | val returned =>
                    cases sourceProgramResult with
                    | err error => cases error <;> simp [ResultRel] at resultRel
                    | val sourceReturned =>
                      have targetNonempty : program ≠ [] := by
                        intro empty
                        have lengths := code_rel_IMP_LENGTH sourceProgram program programRel
                        rw [empty] at lengths
                        exact sourceNonempty (List.eq_nil_of_length_eq_zero lengths)
                      have returnedNonempty : returned ≠ [] := by
                        intro empty
                        subst returned
                        have lengths := (evaluate_length (C := C) (F := F)).1 program [] targetInstalled targetLast [] programRun
                        exact targetNonempty (List.eq_nil_of_length_eq_zero lengths.symm)
                      have sourceReturnedNonempty : sourceReturned ≠ [] := by
                        intro empty
                        subst sourceReturned
                        cases resultRel
                        exact returnedNonempty rfl
                      have lastValueRel := forall₂_holLast resultRel sourceReturnedNonempty
                      rw [evaluate_install_eq, argsRun] at run
                      simp only [runInstalled, targetInstall, programRun] at run
                      cases run
                      refine ⟨extra + programExtra + traces.length,
                        .val [@Flapjack.holLast Value ⟨unitValue⟩ sourceReturned], sourceLast, ?_,
                        .cons lastValueRel .nil, lastRel⟩
                      rw [wrapped, evaluate_install_eq, sourceArgsShift]
                      simp [runInstalled, sourceInstallShift, sourceProgramRun]

end Flapjack.Compiler.Backend.ClosTicks
