module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordMlInvLookup

@[expose] public section

/-! Local updates in the data-to-word word/ML invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Every root after matching source and target inserts is either the new
pair or an old joined root. This Flapjack-specific helper discharges the
membership argument in the original `word_ml_inv_insert` proof. -/
theorem joinEnv_insert_subset {width : Nat} [NeZero width]
    (source : Spt DataSem.Value) (target : Spt (WordLocW width))
    (dest : Nat) (value : DataSem.Value) (word : WordLocW width)
    (pair : DataSem.Value × WordLocW width)
    (h : pair ∈ joinEnv (sptInsert dest value source)
      (sptToAList (sptInter (sptInsert (adjustVar dest) word target)
        (adjustSet (sptInsert dest value source))))) :
    pair = (value, word) ∨ pair ∈ joinEnv source (sptToAList (sptInter target (adjustSet source))) := by
  simp only [joinEnv, List.mem_map, List.mem_filter] at h
  obtain ⟨⟨key, w⟩, ⟨inList, live⟩, equal⟩ := h
  have intersection := (sptMemToAList _ key w).mp inList
  rw [sptLookup_sptInterCases] at intersection
  cases htarget : sptLookup key (sptInsert (adjustVar dest) word target) with
  | none => simp [htarget] at intersection
  | some current =>
    cases hadjusted : sptLookup key (adjustSet (sptInsert dest value source)) with
    | none => simp [htarget, hadjusted] at intersection
    | some unitValue =>
      have currentEq : current = w := by simpa [htarget, hadjusted] using intersection
      subst current
      have domainNew : sptDomain (adjustSet (sptInsert dest value source)) key := by
        simp [sptDomain, hadjusted]
      obtain ⟨index, keyEq, domainSource⟩ := (adjustSet_domain _ key).mp domainNew
      obtain ⟨sourceValue, sourceLookup⟩ := (sptMem_iff_lookup index _).mp domainSource
      have decoded : (key - 2) / 2 = index := by rw [keyEq]; simp [adjustVar]
      by_cases same : index = dest
      · have keyDest : key = adjustVar dest := keyEq.trans (congrArg adjustVar same)
        have wordEq : word = w := by
          simpa [keyDest, sptLookup_sptInsert_same] using htarget
        left
        rw [← equal]
        simp [decoded, same, sptLookup_sptInsert_same, holThe, ← wordEq]
      · have keyNe : key ≠ adjustVar dest := by
          rw [keyEq]
          simp only [adjustVar]
          omega
        have oldSource : sptLookup index source = some sourceValue := by
          rw [sptLookup_sptInsert_ne dest index value source same] at sourceLookup
          exact sourceLookup
        have oldTarget : sptLookup key target = some w := by
          rw [sptLookup_sptInsert_ne (adjustVar dest) key word target keyNe] at htarget
          exact htarget
        have oldAdjusted : sptLookup key (adjustSet source) = some () := by
          rw [keyEq, lookup_adjustSet_map, oldSource]
          rfl
        have oldEntry : (key, w) ∈ sptToAList (sptInter target (adjustSet source)) := by
          apply (sptMemToAList _ key w).mpr
          rw [sptLookup_sptInterCases, oldTarget, oldAdjusted]
        right
        simp only [joinEnv, List.mem_map, List.mem_filter]
        refine ⟨(key, w), ⟨oldEntry, live⟩, ?_⟩
        simpa [decoded, oldSource, sourceLookup, holThe] using equal

/-- Inserting a related pair in both local trees preserves the word/ML
invariant when that pair is already among its roots. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_ml_inv_insert"
  (words_as_type_indexed_bitvec)]
theorem wordMlInv_insert {width : Nat} [NeZero width]
    (heap : ValueHeap width) (be : Bool) (a sp sp1 : Nat) (gens : GcCombined.GenState)
    (limit next : Nat) (conf : Config) (refs : Spt (BvlSem.Ref DataSem.Value))
    (source : Spt DataSem.Value) (target : Spt (WordLocW width))
    (dest : Nat) (value : DataSem.Value) (word : WordLocW width)
    (xs : List (DataSem.Value × WordLocW width))
    (invariant : wordMlInv (heap, be, a, sp, sp1, gens) limit next conf refs
      ([(value, word)] ++ joinEnv source (sptToAList (sptInter target (adjustSet source))) ++ xs)) :
    wordMlInv (heap, be, a, sp, sp1, gens) limit next conf refs
      (joinEnv (sptInsert dest value source)
        (sptToAList (sptInter (sptInsert (adjustVar dest) word target)
          (adjustSet (sptInsert dest value source)))) ++ xs) := by
  apply wordMlInv_rearrange heap be a sp sp1 gens limit next conf refs _ _ ?_ invariant
  intro pair inNew
  simp only [List.mem_append, List.mem_singleton] at inNew ⊢
  rcases inNew with inJoin | inXs
  · rcases joinEnv_insert_subset source target dest value word pair inJoin with same | old
    · exact Or.inl (Or.inl same)
    · exact Or.inl (Or.inr old)
  · exact Or.inr inXs

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
