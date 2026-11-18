module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.JoinEnv
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StackPermute
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env

@[expose] public section

/-! State-relation preservation when source locals are cut. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace cutStateMap
/-- Canonical target-state roundtrip for cut-environment theorems. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end cutStateMap

/-- Cutting source locals preserves the full relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_cut_env"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_cutEnv {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (names : NumSet) (cut : Spt Flapjack.Compiler.Backend.DataSem.Value)
    (premises : stateRel conf l1 l2 source target none locs ∧
      DataSem.cutEnv names source.locals = some cut) :
    stateRel conf l1 l2 { source with locals := cut } target none locs := by
  obtain ⟨related, cutRun⟩ := premises
  rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
  refine ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
    hzero, ?_, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, ?_⟩
  · intro key present
    obtain ⟨value, found⟩ := Option.isSome_iff_exists.mp present
    apply hpresent key
    apply Option.isSome_iff_exists.mpr
    exact ⟨value, cutEnv_lookup_retained names source.locals cut cutRun key value found⟩
  · change memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      (joinEnv cut (sptToAList (sptInter target.locals (adjustSet cut))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
    simp only [Option.getD_none, List.nil_append] at hmem
    obtain ⟨heap, limit, a, sp, sp1, gens, hstore, hinv, hbound, hspace⟩ := hmem
    refine ⟨heap, limit, a, sp, sp1, gens, hstore, ?_, hbound, hspace⟩
    apply wordMlInv_rearrange heap target.be a sp sp1 gens limit (holThe source.tstamps)
      conf source.refs _ _ ?_ hinv
    intro pair member
    simp only [List.mem_append] at member ⊢
    rcases member with (member | member) | member
    · apply Or.inl
      apply Or.inl
      apply Assign.joinEnv_submap_mem cut source.locals target.locals target.locals pair
      exact ⟨fun key value found => cutEnv_lookup_retained names source.locals cut cutRun key value found,
        fun _ _ found => found, member⟩
    · exact Or.inl (Or.inr member)
    · exact Or.inr member

/-- A successful optional cut preserves the full state relation. This factors
the source assignment proof and has no separate HOL declaration. -/
theorem stateRel_cutOpt {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (names : Option NumSet) (cut : DataSem.State C F)
    (premises : stateRel conf l1 l2 source target none locs ∧
      DataSem.cutStateOpt names source = some cut) :
    stateRel conf l1 l2 cut target none locs := by
  obtain ⟨related, cutRun⟩ := premises
  cases names with
  | none =>
    simp [DataSem.cutStateOpt] at cutRun
    subst cut
    exact related
  | some names =>
    cases envRun : DataSem.cutEnv names source.locals with
    | none => simp [DataSem.cutStateOpt, DataSem.cutState, envRun] at cutRun
    | some env =>
      have cutEq : cut = { source with locals := env } := by
        simpa [DataSem.cutStateOpt, DataSem.cutState, envRun] using cutRun.symm
      subst cut
      exact stateRel_cutEnv conf l1 l2 source target locs names env ⟨related, envRun⟩

/-- A successful source cut has a corresponding successful target cut. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "cut_env_IMP_cut_env"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem cutEnv_imp_wordCutEnv {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (names : NumSet) (cut : Spt Flapjack.Compiler.Backend.DataSem.Value)
    (premises : stateRel conf l1 l2 source target none locs ∧
      DataSem.cutEnv names source.locals = some cut) :
    ∃ wordCut, wordSemCutEnv (adjustSets names) target.locals = some wordCut := by
  obtain ⟨related, cutRun⟩ := premises
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, hzero, hpresent, _⟩
  have sourcePresent : ∀ key, sptMem key names → sptMem key source.locals := by
    unfold DataSem.cutEnv at cutRun
    split at cutRun
    · assumption
    · contradiction
  have first : LoopSemStateFiniteExact.sptSubsetLive (.ls ()) target.locals := by
    intro key present
    have keyZero : key = 0 := by
      obtain ⟨v, found⟩ := (sptMem_iff_lookup key (.ls ())).mp present
      cases key <;> simp_all [sptLookup]
    subst key
    exact (sptMem_iff_lookup 0 target.locals).mpr ⟨_, hzero rfl⟩
  have second : LoopSemStateFiniteExact.sptSubsetLive (adjustSet names) target.locals := by
    intro key present
    obtain ⟨n, keyEq, namePresent⟩ := (adjustSet_domain names key).mp present
    subst key
    have sourceSome : (sptLookup n source.locals).isSome := by
      obtain ⟨value, found⟩ := (sptMem_iff_lookup n source.locals).mp (sourcePresent n namePresent)
      simp [found]
    obtain ⟨word, found⟩ := Option.isSome_iff_exists.mp (hpresent n sourceSome)
    exact (sptMem_iff_lookup _ _).mpr ⟨word, found⟩
  simp [wordSemCutEnv, wordSemCutEnvs, wordSemCutNames, adjustSets, first, second]

/-- Cutting both environments preserves the complete state relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_cut_env_cut_env"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_cutEnv_cutEnv {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (names : NumSet) (cut : Spt Flapjack.Compiler.Backend.DataSem.Value) (wordCut : Spt (WordLocW width))
    (premises : stateRel conf l1 l2 source target none locs ∧
      DataSem.cutEnv names source.locals = some cut ∧
      wordSemCutEnv (adjustSets names) target.locals = some wordCut) :
    stateRel conf l1 l2 { source with locals := cut } { target with locals := wordCut } none locs := by
  obtain ⟨related, cutRun, wordRun⟩ := premises
  have cutNames : ∀ n, sptMem n cut → sptMem n names := by
    intro n present
    obtain ⟨value, found⟩ := (sptMem_iff_lookup n cut).mp present
    unfold DataSem.cutEnv at cutRun
    split at cutRun
    · simp only [Option.some.injEq] at cutRun
      subst cut
      rw [sptLookup_mkWf, sptLookup_sptInterCases] at found
      cases hn : sptLookup n names with
      | none => simp [hn] at found
      | some entry => exact (sptMem_iff_lookup n names).mpr ⟨entry, hn⟩
    · contradiction
  have wordCutEq : wordCut = sptUnion (sptInter target.locals (adjustSet names))
      (sptInter target.locals (.ls ())) := by
    by_cases h1 : LoopSemStateFiniteExact.sptSubsetLive (.ls ()) target.locals <;>
      by_cases h2 : LoopSemStateFiniteExact.sptSubsetLive (adjustSet names) target.locals <;>
      simp [wordSemCutEnv, wordSemCutEnvs, wordSemCutNames, adjustSets, h1, h2] at wordRun
    exact wordRun.symm
  have wordLookup : ∀ key, key = 0 ∨ sptMem key (adjustSet names) →
      sptLookup key wordCut = sptLookup key target.locals := by
    intro key live
    rw [wordCutEq, sptLookup_sptUnion, sptLookup_sptInterCases, sptLookup_sptInterCases]
    rcases live with zero | live
    · subst key
      cases sptLookup 0 target.locals <;> cases sptLookup 0 (adjustSet names) <;> simp [sptLookup]
    · obtain ⟨v, found⟩ := (sptMem_iff_lookup key (adjustSet names)).mp live
      cases sptLookup key target.locals <;> simp [found]
  have adjustedCut : ∀ key, sptMem key (adjustSet cut) → sptMem key (adjustSet names) := by
    intro key live
    obtain ⟨n, eq, member⟩ := (adjustSet_domain cut key).mp live
    exact (adjustSet_domain names key).mpr ⟨n, eq, cutNames n member⟩
  have rootsEq : sptInter wordCut (adjustSet cut) = sptInter target.locals (adjustSet cut) := by
    apply (sptEqThm _ _ ⟨sptWfInter _ _, sptWfInter _ _⟩).2
    intro key
    rw [sptLookup_sptInterCases, sptLookup_sptInterCases]
    cases lookup : sptLookup key (adjustSet cut) with
    | none => simp
    | some value =>
      have member := (sptMem_iff_lookup key (adjustSet cut)).mpr ⟨value, lookup⟩
      rw [wordLookup key (Or.inr (adjustedCut key member))]
  have cutRelated := stateRel_cutEnv conf l1 l2 source target locs names cut ⟨related, cutRun⟩
  rcases cutRelated with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
  refine ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
    ?_, ?_, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, ?_⟩
  · intro h
    change sptLookup 0 wordCut = some (.loc l1 l2)
    rw [wordLookup 0 (Or.inl rfl)]
    exact hzero h
  · intro n present
    change (sptLookup (adjustVar n) wordCut).isSome
    have member : sptMem (adjustVar n) (adjustSet cut) := by
      apply (adjustSet_domain cut _).mpr
      exact ⟨n, rfl, (sptMem_iff_lookup n cut).mpr (Option.isSome_iff_exists.mp present)⟩
    rw [wordLookup _ (Or.inr (adjustedCut _ member))]
    exact hpresent n present
  · change memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      ([] ++ joinEnv cut (sptToAList (sptInter wordCut (adjustSet cut))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
    rw [rootsEq]
    exact hmem

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
