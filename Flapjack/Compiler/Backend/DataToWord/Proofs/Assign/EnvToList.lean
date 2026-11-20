module

public import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutEnvProperties

@[expose] public section

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- Converting a word environment to a list preserves its domain. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "env_to_list_domain"
  (words_as_type_indexed_bitvec)]
theorem envToList_domain {width : Nat} [NeZero width]
    (env : Spt (WordLocW width)) (p : Nat → Nat → Nat)
    (entries : List (Nat × WordLocW width)) (permute : Nat → Nat → Nat)
    (run : wordSemEnvToList env p = (entries, permute)) :
    sptDomain (sptFromAList entries) = sptDomain env := by
  have equiv := (wordSemEnvToListLookupEquiv env p entries permute run).1
  funext key
  apply propext
  simp [sptDomain, sptLookup_sptFromAList, equiv key]

/-- The reserved location survives the first cut and is absent from the
association list produced from the second cut. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "cut_envs_lookup_0"
  (words_as_type_indexed_bitvec)]
theorem cutEnvs_lookup_zero {width : Nat} [NeZero width] {α : Type} (names : Spt α)
    (target first second : Spt (WordLocW width)) (p : Nat → Nat → Nat)
    (entries : List (Nat × WordLocW width)) (permute : Nat → Nat → Nat)
    (l1 l2 : Nat)
    (premises : wordSemCutEnvs (adjustSets names) target = some (first, second) ∧
      wordSemEnvToList second p = (entries, permute) ∧
      sptLookup 0 target = some (.loc l1 l2)) :
    sptAListLookup 0 entries = none ∧ sptLookup 0 first = some (.loc l1 l2) := by
  have eqLookup := (wordSemEnvToListLookupEquiv second p entries permute premises.2.1).1 0
  have secondZero := cutEnvs_adjust_second_zero names target (first, second) premises.1
  constructor
  · simpa [eqLookup] using secondZero
  · have run := premises.1
    by_cases h1 : LoopSemStateFiniteExact.sptSubsetLive (adjustSets names).1 target <;>
      by_cases h2 : LoopSemStateFiniteExact.sptSubsetLive (adjustSets names).2 target <;>
      simp [wordSemCutEnvs, wordSemCutNames, h1, h2] at run
    obtain ⟨firstEq, _⟩ := run
    rw [← firstEq, sptLookup_sptInterCases]
    simp [adjustSets, sptLookup, premises.2.2]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
