import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluateCases
import Flapjack.Compiler.Backend.ClosMti.Proofs.Install

/-! Installation continuation for the backward closure evaluation simulation. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- Continue evaluation after an installation operator's arguments have been
evaluated. This helper uses the current Lean evaluator. -/
noncomputable def runInstalled {C F : Type} (values : List ClosSem.Value) (state : State C F) :
    EvalResult C F :=
  match doInstall values state with
  | (.err error, next) => (.err error, next)
  | (.val program, next) =>
    let (result, last) := evaluate program [] next
    match result with
    | .err error => (.err error, last)
    | .val values => (.val [@holLast ClosSem.Value ⟨unitValue⟩ values], last)

/-- An installation expression first evaluates its arguments and then runs
the installed program. -/
theorem evaluate_install_eq {C F : Type} (trace : BackendCommon.Tra) (args : List ClosLang.Exp)
    (env : List ClosSem.Value) (state : State C F) :
    evaluate [.op trace .install args] env state =
      match evaluate args env state with
      | (.err error, next) => (.err error, next)
      | (.val values, next) => runInstalled values.reverse next := by
  rw [evaluate, fixClock_evaluate]
  cases evaluated : evaluate args env state with
  | mk result next =>
    cases result with
    | err error => rfl
    | val values =>
      dsimp only
      unfold runInstalled
      split <;> simp_all
      split <;> simp_all
      rfl

/-- The final elements of nonempty related value lists are related. -/
theorem holLast_related (maxApp : Nat) {left right : List ClosSem.Value}
    (related : List.Forall₂ (ValueRel maxApp) left right) (nonempty : left ≠ []) :
    ValueRel maxApp (@holLast ClosSem.Value ⟨unitValue⟩ left)
      (@holLast ClosSem.Value ⟨unitValue⟩ right) := by
  induction related with
  | nil => exact (nonempty rfl).elim
  | @cons first nextFirst rest nextRest head tail ih =>
    cases tail with
    | nil => simpa [holLast] using head
    | @cons second nextSecond tail nextTail nextHead restRel =>
      simp only [holLast]
      exact ih (by simp)

/-- The induction hypothesis for installed programs at a smaller target
clock. Both environments are empty at the installation boundary. -/
def InstalledProgramIH {C F : Type} (clock : Nat) : Prop :=
  ∀ (targetCode : List ClosLang.Exp) (target : State C F), target.clock < clock →
    ∀ (sourceCode : List ClosLang.Exp) (source : State C F)
      (targetResult : Result (List ClosSem.Value) ClosSem.Value) (targetFinal : State C F),
      evaluate targetCode [] target = (targetResult, targetFinal) → StateRel source target →
      CodeRel source.maxApp sourceCode targetCode →
      ∃ sourceResult sourceFinal,
        evaluate sourceCode [] source = (sourceResult, sourceFinal) ∧
        resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
          sourceResult targetResult ∧ StateRel sourceFinal targetFinal

/-- Installation continuation preserves the backward simulation, using only
the smaller-clock induction hypothesis for a successfully installed program. -/
theorem runInstalled_related {C F : Type} (source target : State C F)
    (sourceValues targetValues : List ClosSem.Value)
    (targetResult : Result (List ClosSem.Value) ClosSem.Value) (targetFinal : State C F)
    (run : runInstalled targetValues target = (targetResult, targetFinal))
    (states : StateRel source target)
    (values : List.Forall₂ (ValueRel source.maxApp) sourceValues targetValues)
    (programIH : InstalledProgramIH (C := C) (F := F) target.clock) :
    ∃ sourceResult sourceFinal,
      runInstalled sourceValues source = (sourceResult, sourceFinal) ∧
      resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
        sourceResult targetResult ∧ StateRel sourceFinal targetFinal := by
  cases targetInstall : doInstall targetValues target with
  | mk installedResult targetInstalled =>
    have simulation := doInstall_reverse_related source target sourceValues targetValues
      installedResult targetInstalled states values targetInstall
    cases installedResult with
    | err targetError =>
      obtain ⟨sourceError, sourceInstalled, sourceInstall, errors, _, installedStates⟩ := simulation
      simp [runInstalled, targetInstall] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨.err sourceError, sourceInstalled, by simp [runInstalled, sourceInstall],
        by simpa [resultRel] using errors, installedStates⟩
    | val targetProgram =>
      obtain ⟨sourceProgram, sourceInstalled, ⟨maxEq, installedStates⟩, nonempty, code, sourceInstall⟩ := simulation
      have smaller : targetInstalled.clock < target.clock := by
        have consumed := doInstall_success_clock targetValues target targetInstalled targetProgram targetInstall
        omega
      cases targetProgramRun : evaluate targetProgram [] targetInstalled with
      | mk programResult targetLast =>
        obtain ⟨sourceProgramResult, sourceLast, sourceProgramRun, programRel, finalStates⟩ :=
          programIH targetProgram targetInstalled smaller sourceProgram sourceInstalled programResult targetLast
            targetProgramRun installedStates (by simpa [maxEq] using code)
        cases programResult with
        | err targetError =>
          cases sourceProgramResult with
          | val values => simp [resultRel] at programRel
          | err sourceError =>
            simp [runInstalled, targetInstall, targetProgramRun] at run
            obtain ⟨rfl, rfl⟩ := run
            exact ⟨.err sourceError, sourceLast, by simp [runInstalled, sourceInstall, sourceProgramRun],
              by simpa [resultRel, maxEq] using programRel, finalStates⟩
        | val targetOutput =>
          cases sourceProgramResult with
          | err error => simp [resultRel] at programRel
          | val sourceOutput =>
            have outputNonempty : sourceOutput ≠ [] := by
              intro empty
              subst sourceOutput
              have length := evaluate_length.1 sourceProgram [] sourceInstalled sourceLast [] sourceProgramRun
              exact nonempty (List.eq_nil_of_length_eq_zero length.symm)
            have lastRel : ValueRel source.maxApp
                (@holLast ClosSem.Value ⟨unitValue⟩ sourceOutput)
                (@holLast ClosSem.Value ⟨unitValue⟩ targetOutput) := by
              have outputRel : List.Forall₂ (ValueRel source.maxApp) sourceOutput targetOutput := by
                simpa [resultRel, maxEq] using programRel
              exact holLast_related source.maxApp outputRel outputNonempty
            simp [runInstalled, targetInstall, targetProgramRun] at run
            obtain ⟨rfl, rfl⟩ := run
            exact ⟨.val [@holLast ClosSem.Value ⟨unitValue⟩ sourceOutput], sourceLast,
              by simp [runInstalled, sourceInstall, sourceProgramRun],
              by simpa [resultRel] using List.Forall₂.cons lastRel List.Forall₂.nil, finalStates⟩

/-- Introduction preserves an installation operator and transforms its
argument list. -/
theorem introExp_eq_install (maxApp : Nat) (expression : ClosLang.Exp) (trace : BackendCommon.Tra)
    (targetArgs : List ClosLang.Exp) (unary : ClosProps.noMti expression)
    (transformed : introExp maxApp expression = .op trace .install targetArgs) :
    ∃ args, expression = .op trace .install args ∧ ClosProps.noMtiList args ∧
      targetArgs = introList maxApp args := by
  cases expression <;>
    simp_all [ClosProps.noMti, introExp_var, introExp_if, introExp_let, introExp_raise,
      introExp_handle, introExp_tick, introExp_op, introExp_app_none,
      introExp_fn_none, introExp_letrec_none]

/-- Installation expressions preserve a clock-bounded simulation using the
smaller-clock installed-program hypothesis. -/
theorem evaluateRel_installWithin {C F : Type} (limit : Nat) (trace : BackendCommon.Tra)
    (targetArgs sourceCode : List ClosLang.Exp)
    (argsIH : ∀ sourceCode, @EvaluateRelWithin C F limit sourceCode targetArgs)
    (targetEnv : List ClosSem.Value) (target : State C F) (sourceEnv : List ClosSem.Value)
    (targetFinal source : State C F) (targetResult : Result (List ClosSem.Value) ClosSem.Value)
    (sourceClock : source.clock ≤ limit)
    (programIH : InstalledProgramIH (C := C) (F := F) target.clock)
    (run : evaluate [.op trace .install targetArgs] targetEnv target = (targetResult, targetFinal))
    (env : List.Forall₂ (ValueRel source.maxApp) sourceEnv targetEnv)
    (states : StateRel source target)
    (code : CodeRel source.maxApp sourceCode [.op trace .install targetArgs]) :
    ∃ sourceResult sourceFinal,
      evaluate sourceCode sourceEnv source = (sourceResult, sourceFinal) ∧
      resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
        sourceResult targetResult ∧ StateRel sourceFinal targetFinal := by
  have length := codeRel_length code
  cases sourceCode with
  | nil => simp at length
  | cons expression rest =>
    cases rest with
    | cons next tail => simp at length
    | nil =>
      have unary : ClosProps.noMti expression := code.1 expression (by simp)
      have transformed : introExp source.maxApp expression = .op trace .install targetArgs := by
        simpa [introList] using code.2.symm
      obtain ⟨args, rfl, argsUnary, argsEq⟩ :=
        introExp_eq_install source.maxApp expression trace targetArgs unary transformed
      have argsCode : CodeRel source.maxApp args targetArgs :=
        ⟨ClosProps.noMtiList_iff args |>.mp argsUnary, argsEq⟩
      cases targetArgsRun : evaluate targetArgs targetEnv target with
      | mk argsResult targetMiddle =>
        obtain ⟨sourceArgsResult, sourceMiddle, sourceArgsRun, argsRel, middleStates⟩ :=
          argsIH args targetEnv target sourceEnv targetMiddle source argsResult sourceClock targetArgsRun env states argsCode
        have maxEq : sourceMiddle.maxApp = source.maxApp := by
          have preserved := ClosProps.evaluate_const.1 args sourceEnv source
          simpa [sourceArgsRun] using preserved
        cases argsResult with
        | err targetError =>
          cases sourceArgsResult with
          | val values => simp [resultRel] at argsRel
          | err sourceError =>
            rw [evaluate_install_eq, targetArgsRun] at run
            simp only [Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            exact ⟨.err sourceError, sourceMiddle, by rw [evaluate_install_eq, sourceArgsRun],
              argsRel, middleStates⟩
        | val targetValues =>
          cases sourceArgsResult with
          | err error => simp [resultRel] at argsRel
          | val sourceValues =>
            have valuesRel : List.Forall₂ (ValueRel sourceMiddle.maxApp)
                sourceValues.reverse targetValues.reverse := by
              have values : List.Forall₂ (ValueRel sourceMiddle.maxApp) sourceValues targetValues := by
                simpa [resultRel, maxEq] using argsRel
              exact List.rel_reverse values
            have clockLe : targetMiddle.clock ≤ target.clock := by
              have clock := evaluate_clock_le targetArgs targetEnv target
              simpa [targetArgsRun] using clock
            have smallerIH : InstalledProgramIH (C := C) (F := F) targetMiddle.clock := by
              intro program state smaller
              exact programIH program state (by omega)
            have targetContinuation : runInstalled targetValues.reverse targetMiddle =
                (targetResult, targetFinal) := by
              rw [evaluate_install_eq, targetArgsRun] at run
              exact run
            obtain ⟨sourceResult, sourceFinal, sourceContinuation, continuationRel, finalStates⟩ :=
              runInstalled_related sourceMiddle targetMiddle sourceValues.reverse targetValues.reverse
                targetResult targetFinal targetContinuation middleStates valuesRel smallerIH
            refine ⟨sourceResult, sourceFinal, ?_, ?_, finalStates⟩
            · rw [evaluate_install_eq, sourceArgsRun]
              exact sourceContinuation
            · simpa [maxEq] using continuationRel

/-- The unrestricted installation case, retained for existing callers. -/
theorem evaluateRel_install {C F : Type} (trace : BackendCommon.Tra)
    (targetArgs sourceCode : List ClosLang.Exp)
    (argsIH : ∀ sourceCode, @EvaluateRelAt C F sourceCode targetArgs)
    (targetEnv : List ClosSem.Value) (target : State C F) (sourceEnv : List ClosSem.Value)
    (targetFinal source : State C F) (targetResult : Result (List ClosSem.Value) ClosSem.Value)
    (programIH : InstalledProgramIH (C := C) (F := F) target.clock)
    (run : evaluate [.op trace .install targetArgs] targetEnv target = (targetResult, targetFinal))
    (env : List.Forall₂ (ValueRel source.maxApp) sourceEnv targetEnv)
    (states : StateRel source target)
    (code : CodeRel source.maxApp sourceCode [.op trace .install targetArgs]) :
    ∃ sourceResult sourceFinal,
      evaluate sourceCode sourceEnv source = (sourceResult, sourceFinal) ∧
      resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
        sourceResult targetResult ∧ StateRel sourceFinal targetFinal :=
  evaluateRel_installWithin source.clock trace targetArgs sourceCode
    (fun code => evaluateRelAt_within source.clock code _ (argsIH code))
    targetEnv target sourceEnv targetFinal source targetResult (by omega) programIH run env states code

end Flapjack.Compiler.Backend.ClosMti
