module

public import Flapjack.Compiler.Backend.ClosLetop.Proofs.EvaluateOp
public import Flapjack.Compiler.Backend.Semantics.ClosProps.SimpleRelations
public import Flapjack.Compiler.Backend.ClosLetop.Proofs.Install
public import Flapjack.Compiler.Backend.Semantics.ClosProps.InstallStep

@[expose] public section

/-! Installation case of closure let-operation correctness. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open ClosSem
open Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL (Result)

namespace EvaluateInstallPort
/-- The closure state's canonical finite-map representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end EvaluateInstallPort

/-- Installing related code simulates errors and evaluation of the newly
installed, nonempty program. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "evaluate_let_op"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_let_op_install {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List Value) (source : State C F)
    (argsIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate args env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
        StateRel source target ∧ CodeRel args code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (programIH : ∀ (values : List Value) (middle : State C F) (program : List ClosLang.Exp)
        (installed : State C F),
      evaluate args env source = (.val values, middle) →
      doInstall values.reverse middle = (.val program, installed) →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
        evaluate program [] installed = (result, next) ∧ List.Forall₂ ValueRel [] nextEnv ∧
          StateRel installed target ∧ CodeRel program code →
        ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
          ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate [.op trace .install args] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel [.op trace .install args] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.op trace .install (compileList args)] := by
    simpa [CodeRel, compileList, compileSing] using code
  rw [codeEq]
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    obtain ⟨targetArgsResult, targetMiddle, targetArgsRun, argsRel, middleRel⟩ :=
      argsIH argsResult middle (compileList args) nextEnv target
        ⟨argsRun, envRel, states, rfl⟩
    cases argsResult with
    | err error =>
      rw [evaluate_install_eq, argsRun] at run
      cases run
      cases targetArgsResult with
      | val values => cases error <;> simp [ResultRel] at argsRel
      | err targetError =>
        exact ⟨.err targetError, targetMiddle,
          by rw [evaluate_install_eq, targetArgsRun], argsRel, middleRel⟩
    | val values =>
      cases targetArgsResult with
      | err error => cases error <;> simp [ResultRel] at argsRel
      | val targetValues =>
        have installRel := InstallPort.doInstallLemma middle targetMiddle values.reverse targetValues.reverse
          ⟨middleRel, List.rel_reverse argsRel⟩
        cases installRun : doInstall values.reverse middle with
        | mk installResult installed =>
          rw [installRun] at installRel
          cases installResult with
          | err error =>
            obtain ⟨targetError, targetInstalled, targetInstall, errors, installedRel⟩ := installRel
            rw [evaluate_install_eq, argsRun] at run
            simp only [runInstalled, installRun] at run
            cases run
            refine ⟨.err targetError, targetInstalled, ?_, ?_, installedRel⟩
            · rw [evaluate_install_eq, targetArgsRun]
              simp [runInstalled, targetInstall]
            · cases error <;> cases targetError <;>
                simp_all [ResultRel, Flapjack.SemanticPrimitivesProps.excRel]
          | val program =>
            obtain ⟨targetProgram, targetInstalled, installedRel, nonempty, programRel, targetInstall⟩ := installRel
            cases programRun : evaluate program [] installed with
            | mk programResult final =>
              obtain ⟨targetProgramResult, targetFinal, targetProgramRun, related, finalRel⟩ :=
                programIH values middle program installed argsRun installRun programResult final targetProgram []
                  targetInstalled ⟨programRun, .nil, installedRel, programRel⟩
              cases programResult with
              | err error =>
                rw [evaluate_install_eq, argsRun] at run
                simp only [runInstalled, installRun, programRun] at run
                cases run
                cases targetProgramResult with
                | val vals => cases error <;> simp [ResultRel] at related
                | err targetError =>
                  refine ⟨.err targetError, targetFinal, ?_, related, finalRel⟩
                  rw [evaluate_install_eq, targetArgsRun]
                  simp [runInstalled, targetInstall, targetProgramRun]
              | val returned =>
                cases targetProgramResult with
                | err error => cases error <;> simp [ResultRel] at related
                | val targetReturned =>
                  have returnedNonempty : returned ≠ [] := by
                    intro empty
                    subst returned
                    have length := (evaluate_length (C := C) (F := F)).1 program [] installed final [] programRun
                    exact nonempty (List.eq_nil_of_length_eq_zero length.symm)
                  have lastRel := forall₂_holLast related returnedNonempty
                  rw [evaluate_install_eq, argsRun] at run
                  simp only [runInstalled, installRun, programRun] at run
                  cases run
                  refine ⟨.val [@Flapjack.holLast Value ⟨unitValue⟩ targetReturned], targetFinal,
                    ?_, .cons lastRel .nil, finalRel⟩
                  rw [evaluate_install_eq, targetArgsRun]
                  simp [runInstalled, targetInstall, targetProgramRun]

end Flapjack.Compiler.Backend.ClosLetop
