module

public import Flapjack.Compiler.Backend.DataLive.Proofs.PrimitiveAll

@[expose] public section

/-! Assignment case for evaluator simulation across related stacks. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Assignments produce the same outcome on related states with identical
local environments. Continuing results retain identical locals; stopped
results retain the empty-live relation. This untagged infrastructure is a
case of the stronger evaluator stack-swap result needed by force and call. -/
theorem evaluate_assign_sameLocals {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (args : List Nat) (names : Option NumSet) (source target sourceNext : State C F)
    (result : Option (Result (List DataSem.Value) DataSem.Value))
    (related : stateRel source target .ln) (sameLocals : source.locals = target.locals)
    (run : DataSem.evaluate (.assign dest op args names) source = (result, sourceNext)) :
    ∃ targetNext, DataSem.evaluate (.assign dest op args names) target = (result, targetNext) ∧
      stateRel sourceNext targetNext .ln ∧ (result = none → sourceNext.locals = targetNext.locals) := by
  have readEq : DataSem.getVars args source.locals = DataSem.getVars args target.locals := by rw [sameLocals]
  by_cases invalid : (DataLang.opRequiresNames op == names.isNone) = true
  · simp [DataSem.evaluate, invalid] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨target, by simp [DataSem.evaluate, invalid], related, by simp⟩
  · cases read : DataSem.getVars args source.locals with
    | none =>
      have targetRead : DataSem.getVars args target.locals = none := by rw [← readEq, read]
      simp [DataSem.evaluate, invalid, read] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨target, by simp [DataSem.evaluate, invalid, targetRead], related, by simp⟩
    | some values =>
      have targetRead : DataSem.getVars args target.locals = some values := by rw [← readEq, read]
      rcases stateRel_cutStateOpt_sameLocals source target .ln names related sameLocals with failed | ⟨sourceCut, targetCut, sourceCutRun, targetCutRun, cutRel, cutLocals⟩
      · simp [DataSem.evaluate, invalid, read, failed.1] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨target, by simp [DataSem.evaluate, invalid, targetRead, failed.2], related, by simp⟩
      · cases sourceApp : doApp op values sourceCut with
        | err error =>
          have targetApp := stateRel_doApp_error sourceCut targetCut .ln op values error cutRel sourceApp
          simp [DataSem.evaluate, invalid, read, sourceCutRun, sourceApp] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨flushState true (installSfs op targetCut), ?_, stateRel_flushInstall sourceCut targetCut .ln op cutRel, ?_⟩
          · simp [DataSem.evaluate, invalid, targetRead, targetCutRun, targetApp]
          · simp
        | val pair =>
          obtain ⟨value, sourceApplied⟩ := pair
          obtain ⟨targetApplied, targetApp, appRel, appLocals⟩ :=
            stateRel_doApp_success_sameLocals sourceCut targetCut sourceApplied .ln op values value cutRel cutLocals sourceApp
          simp [DataSem.evaluate, invalid, read, sourceCutRun, sourceApp] at run
          obtain ⟨rfl, rfl⟩ := run
          have installed := stateRel_installSfs sourceApplied targetApplied .ln op appRel
          have installedLocals : (installSfs op sourceApplied).locals = (installSfs op targetApplied).locals := appLocals
          have beforeSet := stateRel_of_sameLocals _ _ (sptDelete dest .ln) installed installedLocals
          refine ⟨setVar dest value (installSfs op targetApplied), ?_, stateRel_setVar _ _ .ln dest value beforeSet, ?_⟩
          · simp [DataSem.evaluate, invalid, targetRead, targetCutRun, targetApp]
          · intro _
            simp [setVar, installedLocals]

end Flapjack.Compiler.Backend.DataLive
