module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutEnvProperties
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CallEnv
public import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PermuteSwapStack

@[expose] public section

/-! Call-entry simulation after pushing the cut environments. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace pushCallEnvMap
/-- Canonical target-state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end pushCallEnvMap

/-- Pushing the cut environments and entering a call preserves the full
state relation, for either kind of saved handler frame. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_call_env_push_opt"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_callEnv_pushOpt {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 q l : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List DataSem.Value) (words : List (WordLocW width)) (size : Option Nat)
    (names : NumSet) (cutData : Spt DataSem.Value) (cutWords : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (premises : stateRel conf l1 l2 source target (some (values.zip words)) locs ∧
      sptLookup 0 target.locals = some (.loc l1 l2) ∧ values.length = words.length ∧
      DataSem.cutEnv names source.locals = some cutData ∧
      wordSemCutEnvs (adjustSets names) target.locals = some cutWords) :
    stateRel conf q l
      (DataSem.callEnv values size (DataSem.pushEnv cutData handler.isSome (DataSem.decClock source)))
      (WordSemStateFiniteExact.callEnv (.loc q l :: words) size
        (WordSemStateFiniteExact.pushEnv cutWords handler (WordSemStateFiniteExact.decClock target)))
      none ((l1,l2)::locs) := by
  obtain ⟨related, zero, lengthEq, dataCut, wordCut⟩ := premises
  cases envList : wordSemEnvToList cutWords.2 target.permute with
  | mk entries permutation =>
    have entryLookup := (wordSemEnvToListLookupEquiv cutWords.2 target.permute entries permutation envList).1
    have entryMem := (wordSemEnvToListLookupEquiv cutWords.2 target.permute entries permutation envList).2
    have cutProp := adjustVar_cutEnvs_imp_mem names target.locals cutWords
    have cutZero := cutEnvs_adjust_lookup_zero names target cutWords wordCut
    have cutSecondZero := cutEnvs_adjust_second_zero names target.locals cutWords wordCut
    have gcKeys : ∀ pair ∈ entries, pair.1 ≠ 0 ∧ pair.1 % 2 = 0 := by
      intro ⟨key, value⟩ member
      have found := entryMem key value member
      have present : sptDomain cutWords.2 key := (sptMem_iff_lookup _ _).mpr ⟨value, found⟩
      have even := (cutProp key wordCut).1 key present
      have nonzero : key ≠ 0 := by
        intro eq
        subst key
        rw [cutSecondZero] at found
        cases found
      exact ⟨nonzero, even⟩
    have gcDistinct : (entries.map Prod.fst).Nodup := envToListAllDistinct _ _ _ _ envList
    have nonGcKeys : ∀ pair ∈ sptToAList cutWords.1, pair.1 = 0 := by
      intro ⟨key, value⟩ member
      have found := (sptMemToAList _ key value).mp member
      have shape : cutWords.1 = sptInter target.locals (adjustSets names).1 := by
        by_cases h1 : LoopSemStateFiniteExact.sptSubsetLive (adjustSets names).1 target.locals <;>
          by_cases h2 : LoopSemStateFiniteExact.sptSubsetLive (adjustSets names).2 target.locals <;>
          simp [wordSemCutEnvs, wordSemCutNames, h1, h2] at wordCut
        exact (congrArg Prod.fst wordCut).symm
      rw [shape, sptLookup_sptInterCases] at found
      cases key with
      | zero => rfl
      | succ key => simp [adjustSets, sptLookup] at found
    have sourceLength : source.localsSize = target.localsSize := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm
    have lookupRel : ∀ key, (sptLookup key cutData).isSome = true ↔
        (sptLookup (adjustVar key) (sptFromAList entries)).isSome = true := by
      intro key
      rw [sptLookup_sptFromAList, entryLookup]
      exact (cutEnv_imp_mem names source.locals cutData key dataCut).trans (cutProp key wordCut).2.symm
    have savedMem : ∀ pair, pair ∈ joinEnv cutData entries →
        pair ∈ joinEnv source.locals (sptToAList
          (sptInter target.locals (adjustSet source.locals))) := by
      intro pair member
      simp only [joinEnv, List.mem_map, List.mem_filter] at member ⊢
      obtain ⟨⟨key, word⟩, ⟨entry, valid⟩, pairEq⟩ := member
      have found := entryMem key word entry
      have keyEq : key = adjustVar ((key - 2) / 2) := by
        simp only [decide_eq_true_eq] at valid
        simp only [adjustVar]
        omega
      have present : (sptLookup ((key - 2) / 2) cutData).isSome = true := by
        apply (lookupRel _).mpr
        rw [sptLookup_sptFromAList, entryLookup, ← keyEq, found]
        rfl
      obtain ⟨value, dataFound⟩ := Option.isSome_iff_exists.mp present
      have inNames : sptDomain names ((key - 2) / 2) := by
        have h := (cutEnv_imp_mem names source.locals cutData ((key - 2) / 2) dataCut).mp present
        exact (sptMem_iff_lookup _ _).mpr (Option.isSome_iff_exists.mp h)
      have sourceFound : sptLookup ((key - 2) / 2) source.locals = some value := by
        rw [cutEnv_imp_lookup_eq names source.locals cutData _ ⟨dataCut, inNames⟩] at dataFound
        exact dataFound
      have shape : cutWords.2 = sptInter target.locals (adjustSets names).2 := by
        by_cases h1 : LoopSemStateFiniteExact.sptSubsetLive (adjustSets names).1 target.locals <;>
          by_cases h2 : LoopSemStateFiniteExact.sptSubsetLive (adjustSets names).2 target.locals <;>
          simp [wordSemCutEnvs, wordSemCutNames, h1, h2] at wordCut
        exact (congrArg Prod.snd wordCut).symm
      have wordFound : sptLookup key target.locals = some word := by
        rw [shape, sptLookup_sptInterCases] at found
        cases hw : sptLookup key target.locals <;>
          cases hn : sptLookup key (adjustSets names).2 <;> simp [hw, hn] at found ⊢
        exact found
      have adjusted : sptLookup key (adjustSet source.locals) = some () := by
        rw [keyEq, lookup_adjustSet_map, sourceFound]
        rfl
      have entry' : (key, word) ∈ sptToAList (sptInter target.locals (adjustSet source.locals)) := by
        apply (sptMemToAList _ _ _).mpr
        rw [sptLookup_sptInterCases, wordFound, adjusted]
      refine ⟨(key, word), ⟨entry', valid⟩, ?_⟩
      simpa [dataFound, sourceFound, holThe] using pairEq
    cases handler with
    | none =>
      rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
        htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
      simp only [DataSem.callEnv, DataSem.pushEnv, DataSem.decClock,
        WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
        WordSemStateFiniteExact.decClock, envList, Option.isSome_none, Bool.false_eq_true,
        ↓reduceIte, stateRel]
      refine ⟨hffi, ?_, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
        ?_, ?_, ?_, ?_, ?_, ?_, hsizes, True.intro, hlim, ?_⟩
      · exact congrArg (fun n : Nat => n - 1) hclock
      · intro _
        simp [WordToStackProofs.fromList2Lookup]
      · intro key present
        rw [lookup_adjustVar_fromList2, sptLookupFromList_getElem?] at *
        apply Option.isSome_iff_exists.mpr
        have inRange : key < values.length := by simpa using present
        have wordRange : key < words.length := by omega
        exact ⟨words[key], by simp [wordRange]⟩
      · exact .cons ⟨gcKeys, sourceLength, nonGcKeys, gcDistinct, lookupRel⟩ hstack
      · apply List.Forall₂.cons _ hlocs
        change sptAListLookup 0 (sptToAList cutWords.1) = some (.loc l1 l2)
        rw [← sptLookup_sptFromAList, sptLookup_sptFromAList_sptToAList, cutZero, zero]
      · have optAdd (a b : Option Nat) : Option.map₂ (· + ·) a b = wordSemOptionAdd a b := by
          cases a <;> cases b <;> rfl
        rw [optAdd, WordSemStateFiniteExact.wordSemOptionMax_eq, optionLe_max_right]
        exact Or.inr (optionLe_refl _)
      · have optAdd (a b : Option Nat) : Option.map₂ (· + ·) a b = wordSemOptionAdd a b := by
          cases a <;> cases b <;> rfl
        have stackEq := stackRel_sizeOfStack (List.Forall₂.cons
          (show stackRel (.env source.localsSize cutData)
            (.stackFrame target.localsSize (sptToAList cutWords.1) entries none) from
              ⟨gcKeys, sourceLength, nonGcKeys, gcDistinct, lookupRel⟩) hstack)
        rw [WordSemStateFiniteExact.wordSemOptionMax_eq,
          WordSemStateFiniteExact.wordSemOptionMax_eq, stackEq, ← optAdd, optionLe_max]
        constructor
        · rw [optionLe_max]
          constructor
          · rw [optionLe_max_right, optionLe_max_right]
            exact Or.inl (Or.inl hmax)
          · rw [optionLe_max_right, optionLe_max_right]
            exact Or.inl (Or.inr (optionLe_refl _))
        · rw [optionLe_max_right]
          exact Or.inr (optionLe_refl _)
      · obtain ⟨heap, limit, a, sp, sp1, gens, hstore, hinv, hbound, hspace⟩ := hmem
        refine ⟨heap, limit, a, sp, sp1, gens, hstore, ?_, hbound, hspace⟩
        apply wordMlInv_rearrange heap target.be a sp sp1 gens limit (holThe source.tstamps)
          conf source.refs _ _ ?_ hinv
        intro pair member
        simp only [Option.getD_some, Option.getD_none, List.nil_append, flatStack,
          List.mem_append, List.mem_singleton] at member ⊢
        rcases member with (root | global) | saved | old
        · exact Or.inl (Or.inl (Or.inl (callJoin_mem values words (.loc q l) pair root)))
        · exact Or.inl (Or.inr global)
        · exact Or.inl (Or.inl (Or.inr (savedMem pair saved)))
        · exact Or.inr old
    | some opt =>
      rcases opt with ⟨ret, prog, h1, h2⟩
      rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
        htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
      simp only [DataSem.callEnv, DataSem.pushEnv, DataSem.decClock,
        WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
        WordSemStateFiniteExact.decClock, envList, Option.isSome_some,
        ↓reduceIte, stateRel]
      refine ⟨hffi, ?_, ?_, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
        ?_, ?_, ?_, ?_, ?_, ?_, hsizes, True.intro, hlim, ?_⟩
      · exact congrArg (fun n : Nat => n - 1) hclock
      · exact hstack.length_eq.symm
      · intro _
        simp [WordToStackProofs.fromList2Lookup]
      · intro key present
        rw [lookup_adjustVar_fromList2, sptLookupFromList_getElem?] at *
        apply Option.isSome_iff_exists.mpr
        have inRange : key < values.length := by simpa using present
        have wordRange : key < words.length := by omega
        exact ⟨words[key], by simp [wordRange]⟩
      · exact .cons ⟨⟨gcKeys, sourceLength, nonGcKeys, gcDistinct, lookupRel⟩, hhandler⟩ hstack
      · apply List.Forall₂.cons _ hlocs
        change sptAListLookup 0 (sptToAList cutWords.1) = some (.loc l1 l2)
        rw [← sptLookup_sptFromAList, sptLookup_sptFromAList_sptToAList, cutZero, zero]
      · have optAdd (a b : Option Nat) : Option.map₂ (· + ·) a b = wordSemOptionAdd a b := by
          cases a <;> cases b <;> rfl
        rw [optAdd, WordSemStateFiniteExact.wordSemOptionMax_eq, optionLe_max_right]
        exact Or.inr (optionLe_refl _)
      · have optAdd (a b : Option Nat) : Option.map₂ (· + ·) a b = wordSemOptionAdd a b := by
          cases a <;> cases b <;> rfl
        have stackEq := stackRel_sizeOfStack (List.Forall₂.cons
          (show stackRel (.exc source.localsSize cutData source.handler)
            (.stackFrame target.localsSize (sptToAList cutWords.1) entries (some (target.handler, h1, h2))) from
              ⟨⟨gcKeys, sourceLength, nonGcKeys, gcDistinct, lookupRel⟩, hhandler⟩) hstack)
        rw [WordSemStateFiniteExact.wordSemOptionMax_eq,
          WordSemStateFiniteExact.wordSemOptionMax_eq, stackEq, ← optAdd, optionLe_max]
        constructor
        · rw [optionLe_max]
          constructor
          · rw [optionLe_max_right, optionLe_max_right]
            exact Or.inl (Or.inl hmax)
          · rw [optionLe_max_right, optionLe_max_right]
            exact Or.inl (Or.inr (optionLe_refl _))
        · rw [optionLe_max_right]
          exact Or.inr (optionLe_refl _)
      · obtain ⟨heap, limit, a, sp, sp1, gens, hstore, hinv, hbound, hspace⟩ := hmem
        refine ⟨heap, limit, a, sp, sp1, gens, hstore, ?_, hbound, hspace⟩
        apply wordMlInv_rearrange heap target.be a sp sp1 gens limit (holThe source.tstamps)
          conf source.refs _ _ ?_ hinv
        intro pair member
        simp only [Option.getD_some, Option.getD_none, List.nil_append, flatStack,
          List.mem_append, List.mem_singleton] at member ⊢
        rcases member with (root | global) | saved | old
        · exact Or.inl (Or.inl (Or.inl (callJoin_mem values words (.loc q l) pair root)))
        · exact Or.inl (Or.inr global)
        · exact Or.inl (Or.inl (Or.inr (savedMem pair saved)))
        · exact Or.inr old

/-- Pushing a non-handler frame and entering a call preserves the full
state relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_call_env_push"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_callEnv_push {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 q l : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (words : List (WordLocW width)) (size : Option Nat)
    (names : NumSet) (cutData : Spt Flapjack.Compiler.Backend.DataSem.Value) (cutWords : Spt (WordLocW width) × Spt (WordLocW width))
    (premises : stateRel conf l1 l2 source target (some (values.zip words)) locs ∧
      values.length = words.length ∧ sptLookup 0 target.locals = some (.loc l1 l2) ∧
      DataSem.cutEnv names source.locals = some cutData ∧
      wordSemCutEnvs (adjustSets names) target.locals = some cutWords) :
    stateRel conf q l
      (DataSem.callEnv values size (DataSem.pushEnv cutData false (DataSem.decClock source)))
      (WordSemStateFiniteExact.callEnv (.loc q l :: words) size
        (WordSemStateFiniteExact.pushEnv cutWords none (WordSemStateFiniteExact.decClock target)))
      none ((l1,l2)::locs) := by
  apply stateRel_callEnv_pushOpt conf l1 l2 q l source target locs values words size names cutData cutWords none
  obtain ⟨related, lengthEq, zero, sourceCut, targetCut⟩ := premises
  exact ⟨related, zero, lengthEq, sourceCut, targetCut⟩

/-- Argument reads and successful cuts establish the pushed call relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_call_env_push_env"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_callEnv_pushEnv {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 q l : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (args : List Nat) (values : List DataSem.Value) (words : List (WordLocW width)) (size : Option Nat)
    (names : NumSet) (cutData : Spt DataSem.Value) (cutWords : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (premises : stateRel conf l1 l2 source target none locs ∧
      DataSem.getVars args source.locals = some values ∧
      WordSemStateFiniteExact.getVars (args.map adjustVar) target = some words ∧
      DataSem.cutEnv names source.locals = some cutData ∧
      wordSemCutEnvs (adjustSets names) target.locals = some cutWords) :
    stateRel conf q l
      (DataSem.callEnv values size (DataSem.pushEnv cutData handler.isSome (DataSem.decClock source)))
      (WordSemStateFiniteExact.callEnv (.loc q l :: words) size
        (WordSemStateFiniteExact.pushEnv cutWords handler (WordSemStateFiniteExact.decClock target)))
      none ((l1,l2)::locs) := by
  obtain ⟨related, sourceRead, targetRead, sourceCut, targetCut⟩ := premises
  have eqLen : values.length = words.length := by
    have hs := getVars_imp_length args values source.locals sourceRead
    have ht := wordGetVars_imp_length (args.map adjustVar) words target targetRead
    simp only [List.length_map] at ht
    exact hs.symm.trans ht
  rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
  have zero := hzero rfl
  apply stateRel_callEnv_pushOpt conf l1 l2 q l source target locs values words size names cutData cutWords handler
  refine ⟨⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
    ?_, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, ?_⟩, zero, eqLen, sourceCut, targetCut⟩
  · simp
  · obtain ⟨heap, limit, a, sp, sp1, gens, hstore, hinv, hbound, hspace⟩ := hmem
    refine ⟨heap, limit, a, sp, sp1, gens, hstore, ?_, hbound, hspace⟩
    simpa only [Option.getD_some, List.append_assoc] using wordMlInv_getVars heap target.be a sp sp1 gens limit (holThe source.tstamps)
      conf source.refs source.locals target args values words
      ([(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
      ⟨by simpa using hinv, sourceRead, targetRead⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
