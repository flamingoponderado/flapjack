import Flapjack.Compiler.Backend.ClosInterp.Proofs.NoInstallInit

/-! Primitive simulation for the no-install interpreter-insertion relation.
The proof-side evaluator and carriers await HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- States related before installing the interpreter differ only in their
compiler callback and oracle. -/
theorem stateRel1_replaceCompiler {C F : Type} (source target : ClosSem.State C F)
    (related : StateRel1 source target) :
    source = { target with compile := source.compile, compileOracle := source.compileOracle } := by
  rcases related with ⟨_, sourceCode, targetCode, maxEq, _, clockEq, ffiEq, globalsEq, refsEq, _, _⟩
  cases source
  cases target
  simp_all

/-- Primitive errors agree across the no-install state relation. -/
theorem doApp_noInstall_error {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (source target : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (related : StateRelNoInstall source target) (run : ClosSem.doApp op args source = .err error) :
    ClosSem.doApp op args target = .err error := by
  have sourceEq := stateRel1_replaceCompiler source target related.1
  rw [sourceEq, doApp_replaceCompiler] at run
  cases targetRun : ClosSem.doApp op args target with
  | err targetError =>
    simp [targetRun, replaceCompilerResult] at run
    cases run
    rfl
  | val pair =>
    rcases pair with ⟨value, next⟩
    simp [targetRun, replaceCompilerResult] at run

/-- Successful ordinary primitives agree across the no-install relation,
produce a safe value, and preserve that relation. -/
theorem doApp_noInstall_relation {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (source target sourceFinal : ClosSem.State C F) (value : ClosSem.Value)
    (related : StateRelNoInstall source target) (argsOk : valuesNoInstall args = true)
    (run : ClosSem.doApp op args source = .val (value, sourceFinal)) :
    ∃ targetFinal, ClosSem.doApp op args target = .val (value, targetFinal) ∧
      StateRelNoInstall sourceFinal targetFinal ∧ valueNoInstall value = true := by
  have sourceEq := stateRel1_replaceCompiler source target related.1
  rw [sourceEq, doApp_replaceCompiler] at run
  cases targetRun : ClosSem.doApp op args target with
  | err error => simp [targetRun, replaceCompilerResult] at run
  | val pair =>
    rcases pair with ⟨targetValue, targetFinal⟩
    simp [targetRun, replaceCompilerResult] at run
    rcases run with ⟨rfl, rfl⟩
    have fields := doApp_compilerFields op args target targetFinal targetValue targetRun
    obtain ⟨valueOk, globalsOk, refsOk⟩ :=
      doApp_noInstall op args target targetFinal targetValue argsOk related.2.1 related.2.2 targetRun
    rcases fields with ⟨compileEq, oracleEq, codeEq, maxEq⟩
    rcases related with ⟨⟨safe, sourceCode, targetCode, oldMaxEq, positive, clockEq,
      ffiEq, globalsEq, refsEq, compilerEq, oracleRel⟩, _, _⟩
    refine ⟨targetFinal, rfl, ?_, valueOk⟩
    refine ⟨?_, globalsOk, refsOk⟩
    refine ⟨safe, ?_, ?_, rfl, ?_, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · simpa only using codeEq.trans targetCode
    · simpa only using codeEq.trans targetCode
    · rw [maxEq, oldMaxEq]
      exact positive
    · simpa only [compileEq] using compilerEq
    · simpa only [oracleEq] using oracleRel

/-- Ordinary operation evaluation agrees on related states when evaluation
of its arguments does, without adding clock to either execution. -/
theorem evaluate_ordinaryOp_noInstall_relation_step {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : ∀ (target last : ClosSem.State C F) (argResult : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate args env source = (argResult, last) → StateRelNoInstall source target →
      ∃ targetLast, ClosSem.evaluate args env target = (argResult, targetLast) ∧
        StateRelNoInstall last targetLast ∧ resultNoInstall argResult)
    (related : StateRelNoInstall source target)
    (run : ClosSem.evaluate [.op trace op args] env source = (result, sourceFinal)) :
    ∃ targetFinal, ClosSem.evaluate [.op trace op args] env target = (result, targetFinal) ∧
      StateRelNoInstall sourceFinal targetFinal ∧ resultNoInstall result := by
  rw [ClosSem.evaluate_ordinaryOp_eq trace op args env source notInstall notForce] at run
  cases argsRun : ClosSem.evaluate args env source with
  | mk argResult sourceLast =>
    rw [argsRun] at run
    obtain ⟨targetLast, targetArgs, lastRel, argOk⟩ := argsIH target sourceLast argResult argsRun related
    cases argResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨targetLast, ?_, lastRel, argOk⟩
      rw [ClosSem.evaluate_ordinaryOp_eq trace op args env target notInstall notForce, targetArgs]
    | val arguments =>
      cases appRun : ClosSem.doApp op arguments.reverse sourceLast with
      | err error =>
        simp [appRun] at run
        rcases run with ⟨rfl, rfl⟩
        have targetApp := doApp_noInstall_error op arguments.reverse sourceLast targetLast error lastRel appRun
        refine ⟨targetLast, ?_, lastRel, ?_⟩
        · rw [ClosSem.evaluate_ordinaryOp_eq trace op args env target notInstall notForce, targetArgs]
          simp [targetApp]
        · cases error with
          | raise value => exact False.elim (doApp_not_raise op arguments.reverse sourceLast value appRun)
          | abort _ => trivial
      | val pair =>
        rcases pair with ⟨value, final⟩
        simp [appRun] at run
        rcases run with ⟨rfl, rfl⟩
        have argumentsOk : valuesNoInstall arguments.reverse = true := (valuesNoInstall_reverse arguments).2 argOk
        obtain ⟨targetFinal, targetApp, finalRel, valueOk⟩ :=
          doApp_noInstall_relation op arguments.reverse sourceLast targetLast final value lastRel argumentsOk appRun
        refine ⟨targetFinal, ?_, finalRel, ?_⟩
        · rw [ClosSem.evaluate_ordinaryOp_eq trace op args env target notInstall notForce, targetArgs]
          simp [targetApp]
        · simp [resultNoInstall, valuesNoInstall, valueOk]

end Flapjack.Compiler.Backend.ClosInterp
