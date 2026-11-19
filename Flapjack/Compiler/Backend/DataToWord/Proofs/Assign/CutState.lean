module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutState
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutLocals
public import Flapjack.Compiler.Backend.DataSpace.Proofs.State

@[expose] public section

/-! Cut-state preparation for data-to-word assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- Both environments returned by a successful word-environment cut are
well-formed sparse trees. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "cut_envs_wf"]
theorem cutEnvs_wf {α : Type} (names : WordLangCutsetsHOL) (env first second : Spt α)
    (run : wordSemCutEnvs names env = some (first, second)) :
    sptWf first = true ∧ sptWf second = true := by
  by_cases h1 : LoopSemStateFiniteExact.sptSubsetLive names.1 env <;>
    by_cases h2 : LoopSemStateFiniteExact.sptSubsetLive names.2 env <;>
    simp [wordSemCutEnvs, wordSemCutNames, h1, h2] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨sptWfInter _ _, sptWfInter _ _⟩

/-- A binding found after a successful word-environment cut was present
in the original environment. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "cut_env_lookup"]
theorem cutEnv_lookup {α : Type} (names : WordLangCutsetsHOL) (env cut : Spt α)
    (key : Nat) (value : α)
    (premises : wordSemCutEnv names env = some cut ∧ sptLookup key cut = some value) :
    sptLookup key env = some value := by
  obtain ⟨run, found⟩ := premises
  by_cases h1 : LoopSemStateFiniteExact.sptSubsetLive names.1 env <;>
    by_cases h2 : LoopSemStateFiniteExact.sptSubsetLive names.2 env <;>
    simp [wordSemCutEnv, wordSemCutEnvs, wordSemCutNames, h1, h2] at run
  subst cut
  rw [sptLookup_sptUnion, sptLookup_sptInterCases, sptLookup_sptInterCases] at found
  cases read : sptLookup key env <;> cases first : sptLookup key names.1 <;>
    cases second : sptLookup key names.2 <;> simp_all

namespace CutEnvGetVarsPort

/-- The word state uses the canonical finite-support representation. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CutEnvGetVarsPort

/-- Successful variable reads agree before and after cutting the environment. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "cut_env_get_vars_get_vars"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem cutEnv_getVars_getVars {width : Nat} [NeZero width] {C F : Type}
    (names : WordLangCutsetsHOL) (state : WordSemStateFiniteExact width C F)
    (cut : Spt (WordLocW width)) :
    ∀ (vars : List Nat) (values original : List (WordLocW width)),
      wordSemCutEnv names state.locals = some cut ∧
      WordSemStateFiniteExact.getVars vars { state with locals := cut } = some values ∧
      WordSemStateFiniteExact.getVars vars state = some original → values = original := by
  intro vars
  induction vars with
  | nil =>
    intro values original premises
    simp [WordSemStateFiniteExact.getVars] at premises
    simp_all
  | cons key rest ih =>
    intro values original ⟨cutRun, cutRead, originalRead⟩
    cases head : WordSemStateFiniteExact.getVar key { state with locals := cut } with
    | none => simp [WordSemStateFiniteExact.getVars, head] at cutRead
    | some value =>
      have originalHead : WordSemStateFiniteExact.getVar key state = some value :=
        cutEnv_lookup names state.locals cut key value ⟨cutRun, head⟩
      cases tail : WordSemStateFiniteExact.getVars rest { state with locals := cut } with
      | none => simp [WordSemStateFiniteExact.getVars, head, tail] at cutRead
      | some restValues =>
        cases oldTail : WordSemStateFiniteExact.getVars rest state with
        | none => simp [WordSemStateFiniteExact.getVars, originalHead, oldTail] at originalRead
        | some oldValues =>
          simp [WordSemStateFiniteExact.getVars, head, tail] at cutRead
          simp [WordSemStateFiniteExact.getVars, originalHead, oldTail] at originalRead
          subst values
          subst original
          rw [ih restValues oldValues ⟨cutRun, tail, oldTail⟩]

/-- A successful optional cut is equal to the total GC cut operation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "cut_state_opt_IMP_cut_locals"]
theorem cutStateOpt_imp_cutLocals {C F : Type} (names : NumSet)
    (state result : DataSem.State C F)
    (run : DataSem.cutStateOpt (some names) state = some result) :
    cutLocals names state = result := by
  cases envRun : DataSem.cutEnv names state.locals with
  | none => simp [DataSem.cutStateOpt, DataSem.cutState, envRun] at run
  | some env => simpa [DataSem.cutStateOpt, DataSem.cutState, cutLocals, envRun] using run

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

/-- A narrow cut after an argument-augmented cut equals the direct narrow
cut. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "cut_env_cut_env_list_insert"]
theorem cutEnv_cutEnv_listInsert {α : Type} (args : List Nat) (names : NumSet)
    (source wide narrow : Spt α)
    (premises : DataSem.cutEnv (sptListInsert args names) source = some wide ∧
      DataSem.cutEnv names source = some narrow) :
    DataSem.cutEnv names wide = some narrow := by
  obtain ⟨wideRun, narrowRun⟩ := premises
  have includeNames : ∀ keys base key, sptMem key base → sptMem key (sptListInsert keys base) := by
    intro keys
    induction keys with
    | nil => intro base key h; exact h
    | cons head tail ih =>
      intro base key h
      apply ih
      exact (sptMem_sptInsert key head () base).mpr (Or.inr h)
  unfold DataSem.cutEnv at wideRun narrowRun
  split at wideRun
  next wideLive =>
    split at narrowRun
    next narrowLive =>
      simp only [Option.some.injEq] at wideRun narrowRun
      subst wide
      subst narrow
      have narrowWide : ∀ key, sptMem key names →
          sptMem key (sptMkWf (sptInter source (sptListInsert args names))) := by
        intro key member
        obtain ⟨v, sourceFound⟩ := (sptMem_iff_lookup key source).mp (narrowLive key member)
        obtain ⟨u, wideFound⟩ := (sptMem_iff_lookup key (sptListInsert args names)).mp
          (includeNames args names key member)
        apply (sptMem_iff_lookup _ _).mpr
        refine ⟨v, ?_⟩
        rw [sptLookup_mkWf, sptLookup_sptInterCases, sourceFound, wideFound]
      simp only [DataSem.cutEnv, if_pos narrowWide, Option.some.injEq]
      apply (sptEqThm _ _ ⟨sptWf_mkWf _, sptWf_mkWf _⟩).2
      intro key
      simp only [sptLookup_mkWf, sptLookup_sptInterCases]
      cases sourceLookup : sptLookup key source <;> cases nameLookup : sptLookup key names with
      | none => cases sptLookup key (sptListInsert args names) <;> rfl
      | some entry =>
        have wideMember := includeNames args names key
          ((sptMem_iff_lookup key names).mpr ⟨entry, nameLookup⟩)
        obtain ⟨u, wideLookup⟩ := (sptMem_iff_lookup key (sptListInsert args names)).mp wideMember
        simp [wideLookup]
    next => contradiction
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
relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "state_rel_cut_state_opt_set_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_cutStateOpt_setVar {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source cut : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (dest : Nat) (value : Flapjack.Compiler.Backend.DataSem.Value) (names : NumSet)
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
target cut and argument read while retaining both complete state relations. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "state_rel_cut_state_opt_SOME"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_cutStateOpt_some {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat)
    (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (args : List Nat) (values : List Flapjack.Compiler.Backend.DataSem.Value) (names : NumSet)
    (cut : Flapjack.Compiler.Backend.DataSem.State C F)
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
