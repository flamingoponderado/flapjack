module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.JoinEnv
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StackPermute
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env

@[expose] public section

/-! State-relation preservation when source locals are cut. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Cutting source locals preserves the full relation. The HOL tag is pending
review of the state relation and its compiler dependencies. -/
theorem stateRel_cutEnv {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (names : NumSet) (cut : Spt DataSem.Value)
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
    · exact Or.inl (Or.inl (joinEnv_cutEnv_mem_general pair target.locals names
        source.locals cut member cutRun))
    · exact Or.inl (Or.inr member)
    · exact Or.inr member

/-- A successful optional cut preserves the full state relation. The HOL tag
is pending review of the state relation and its compiler dependencies. -/
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

/-- A successful source cut has a corresponding successful target cut. The
HOL tag is pending review of the state relation and its compiler dependencies. -/
theorem cutEnv_imp_wordCutEnv {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (names : NumSet) (cut : Spt DataSem.Value)
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

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
