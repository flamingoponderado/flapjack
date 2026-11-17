module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutState
public import Flapjack.Compiler.Backend.DataSpace.Proofs.State

@[expose] public section

/-! Cut-state preparation for data-to-word assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- A successful optional source cut and argument read can be matched by a
target cut and argument read while retaining both state relations. The HOL
tag is pending review of the state relation and its compiler dependencies. -/
theorem stateRel_cutStateOpt_some {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (args : List Nat) (values : List DataSem.Value) (names : NumSet)
    (cut : DataSem.State C F)
    (premises : stateRel conf l1 l2 source target none locs ∧
      DataSem.getVars args source.locals = some values ∧
      DataSem.cutStateOpt (some names) source = some cut) :
    ∃ wordCut words,
      wordSemCutEnv (adjustSets names) target.locals = some wordCut ∧
      WordSemStateFiniteExact.getVars (args.map adjustVar) target = some words ∧
      args.length = values.length ∧ args.length = words.length ∧
      stateRel conf l1 l2 cut target none locs ∧
      stateRel conf l1 l2 cut { target with locals := wordCut } none locs := by
  obtain ⟨related, read, cutRun⟩ := premises
  obtain ⟨words, wordRead, sameLength⟩ :=
    stateRel_getVars conf l1 l2 source target locs args values related read
  have sourceLength : args.length = values.length := (DataSpace.getVars_length args source.locals values read).symm
  have cutRelated := stateRel_cutOpt conf l1 l2 source target locs (some names) cut ⟨related, cutRun⟩
  cases envRun : DataSem.cutEnv names source.locals with
  | none => simp [DataSem.cutStateOpt, DataSem.cutState, envRun] at cutRun
  | some env =>
    have cutEq : cut = { source with locals := env } := by
      simpa [DataSem.cutStateOpt, DataSem.cutState, envRun] using cutRun.symm
    obtain ⟨wordCut, wordCutRun⟩ := cutEnv_imp_wordCutEnv conf l1 l2 source target locs names env ⟨related, envRun⟩
    refine ⟨wordCut, words, wordCutRun, wordRead, sourceLength, sourceLength.trans sameLength,
      cutRelated, ?_⟩
    subst cut
    exact stateRel_cutEnv_cutEnv conf l1 l2 source target locs names env wordCut
      ⟨related, envRun, wordCutRun⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
