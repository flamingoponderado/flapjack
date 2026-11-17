module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutState
public import Flapjack.Compiler.Backend.DataSpace.Proofs.State

@[expose] public section

/-! Cut-state preparation for data-to-word assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- A successful restricted cut returns the normalized intersection. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "cut_state_opt_SOME_eq"]
theorem cutStateOpt_some_eq {C F : Type} (names : NumSet)
    (state result : DataSem.State C F)
    (run : DataSem.cutStateOpt (some names) state = some result) :
    result = { state with locals := sptMkWf (sptInter state.locals names) } := by
  simp only [DataSem.cutStateOpt, DataSem.cutState] at run
  unfold DataSem.cutEnv at run
  split at run
  · simpa using run.symm
  · simp at run

/-- Repeating a successful environment cut leaves its result unchanged. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "cut_env_idempotent"]
theorem cutEnv_idempotent {α : Type} (names : NumSet) (source env : Spt α)
    (run : DataSem.cutEnv names source = some env) :
    DataSem.cutEnv names env = some env := by
  unfold DataSem.cutEnv at run
  split at run
  next live =>
    simp only [Option.some.injEq] at run
    subst env
    have liveCut : ∀ key, sptMem key names → sptMem key (sptMkWf (sptInter source names)) := by
      intro key present
      obtain ⟨value, sourceFound⟩ := (sptMem_iff_lookup key source).mp (live key present)
      obtain ⟨entry, nameFound⟩ := (sptMem_iff_lookup key names).mp present
      apply (sptMem_iff_lookup _ _).mpr
      refine ⟨value, ?_⟩
      rw [sptLookup_mkWf, sptLookup_sptInterCases, sourceFound, nameFound]
    simp only [DataSem.cutEnv, if_pos liveCut, Option.some.injEq]
    apply (sptEqThm _ _ ⟨sptWf_mkWf _, sptWf_mkWf _⟩).2
    intro key
    simp only [sptLookup_mkWf, sptLookup_sptInterCases]
    cases sptLookup key source <;> cases sptLookup key names <;> rfl
  next => contradiction

/-- Inserting a binding before and after a successful cut commutes when the
inserted name is also retained. This is the sparse-tree step in the HOL proof. -/
private theorem cutEnv_insert {α : Type} (names : NumSet) (env cut : Spt α)
    (dest : Nat) (value : α) (run : DataSem.cutEnv names env = some cut) :
    DataSem.cutEnv (sptInsert dest () names) (sptInsert dest value env) =
      some (sptInsert dest value cut) := by
  unfold DataSem.cutEnv at run
  split at run
  next live =>
    simp only [Option.some.injEq] at run
    subst cut
    have liveInserted : ∀ key, sptMem key (sptInsert dest () names) →
        sptMem key (sptInsert dest value env) := by
      intro key member
      rw [sptMem_sptInsert] at member ⊢
      rcases member with same | member
      · exact Or.inl same
      · exact Or.inr (live key member)
    simp only [DataSem.cutEnv, if_pos liveInserted, Option.some.injEq]
    apply (sptEqThm _ _ ⟨sptWf_mkWf _, sptWfInsert _ _ _ (sptWf_mkWf _)⟩).2
    intro key
    rw [sptLookup_mkWf]
    by_cases same : key = dest
    · subst key
      simp [sptLookup_sptInterCases, sptLookup_sptInsert_same]
    · rw [sptLookup_sptInterCases, sptLookup_sptInsert_ne dest key value env same,
        sptLookup_sptInsert_ne dest key () names same,
        sptLookup_sptInsert_ne dest key value (sptMkWf (sptInter env names)) same,
        sptLookup_mkWf, sptLookup_sptInterCases]
  next => contradiction

/-- Cutting the original locals before a variable update preserves the full
relation. The HOL tag is pending review of the state relation's dependencies. -/
theorem stateRel_cutStateOpt_setVar {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source cut : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (dest : Nat) (value : DataSem.Value) (names : NumSet)
    (premises : stateRel conf l1 l2 (DataSem.setVar dest value source) target none locs ∧
      DataSem.cutStateOpt (some names) source = some cut) :
    stateRel conf l1 l2 (DataSem.setVar dest value cut) target none locs := by
  obtain ⟨related, cutRun⟩ := premises
  cases envRun : DataSem.cutEnv names source.locals with
  | none => simp [DataSem.cutStateOpt, DataSem.cutState, envRun] at cutRun
  | some env =>
    have cutEq : cut = { source with locals := env } := by
      simpa [DataSem.cutStateOpt, DataSem.cutState, envRun] using cutRun.symm
    subst cut
    have inserted := cutEnv_insert names source.locals env dest value envRun
    have result := stateRel_cutEnv conf l1 l2 (DataSem.setVar dest value source) target locs
      (sptInsert dest () names) (sptInsert dest value env) ⟨related, inserted⟩
    simpa [DataSem.setVar] using result

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
