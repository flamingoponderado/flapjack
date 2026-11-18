module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AdjustedSet
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackRel

@[expose] public section

/-! Environment membership used by data-to-word assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- Extending both environments by lookup-preserving maps retains every
joined pair. The pair itself supplies the inhabitant used by HOL's `THE`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "join_env_submap_MEM"]
theorem joinEnv_submap_mem {α β : Type} (first first' : Spt α) (second second' : Spt β)
    (pair : α × β)
    (premises : (∀ key value, sptLookup key first = some value → sptLookup key first' = some value) ∧
      (∀ key value, sptLookup key second = some value → sptLookup key second' = some value) ∧
      pair ∈ @joinEnv α β ⟨pair.1⟩ first (sptToAList (sptInter second (adjustSet first)))) :
    pair ∈ @joinEnv α β ⟨pair.1⟩ first' (sptToAList (sptInter second' (adjustSet first'))) := by
  obtain ⟨firstSub, secondSub, member⟩ := premises
  simp only [joinEnv, List.mem_map, List.mem_filter] at member ⊢
  obtain ⟨⟨key, word⟩, ⟨inList, valid⟩, equal⟩ := member
  have intersection := (sptMemToAList _ key word).mp inList
  rw [sptLookup_sptInterCases] at intersection
  cases wordFound : sptLookup key second with
  | none => simp [wordFound] at intersection
  | some wordValue =>
    cases adjustedFound : sptLookup key (adjustSet first) with
    | none => simp [wordFound, adjustedFound] at intersection
    | some u =>
      have present : sptDomain (adjustSet first) key := by simp [sptDomain, adjustedFound]
      obtain ⟨n, keyEq, firstPresent⟩ := (adjustSet_domain first key).mp present
      obtain ⟨value, firstFound⟩ := (sptMem_iff_lookup n first).mp firstPresent
      have firstFound' := firstSub n value firstFound
      have firstPresent' : sptDomain first' n := (sptMem_iff_lookup n first').mpr ⟨value, firstFound'⟩
      have adjustedPresent' : sptDomain (adjustSet first') key :=
        (adjustSet_domain first' key).mpr ⟨n, keyEq, firstPresent'⟩
      obtain ⟨u', adjustedFound'⟩ := (sptMem_iff_lookup key (adjustSet first')).mp adjustedPresent'
      have wordEq : wordValue = word := by simpa [wordFound, adjustedFound] using intersection
      subst wordValue
      have wordFound' := secondSub key word wordFound
      have targetList : (key, word) ∈ sptToAList (sptInter second' (adjustSet first')) := by
        apply (sptMemToAList _ _ _).mpr
        rw [sptLookup_sptInterCases, wordFound', adjustedFound']
      have index : (key - 2) / 2 = n := by rw [keyEq]; simp [adjustVar]
      refine ⟨(key, word), ⟨targetList, valid⟩, ?_⟩
      simpa [index, firstFound, firstFound', holThe] using equal

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
