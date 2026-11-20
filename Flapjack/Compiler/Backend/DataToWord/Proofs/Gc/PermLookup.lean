module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.FrameRoots

@[expose] public section

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Classical

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "PERM_lookup_toList_lemma"
  (total_function_inhabitants := [β])]
theorem perm_lookup_toList {α β : Type} [Nonempty β] (l : List (Nat × α)) (s : Spt β)
    (h : (∀ n, (sptLookup n s).isSome = true ↔ (sptAListLookup (adjustVar n) l).isSome = true) ∧
      (l.map Prod.fst).Nodup) :
    (((l.filter (fun pair => pair.1 ≠ 0 ∧ pair.1 % 2 = 0)).map
      (fun (n, v) => (holThe (sptLookup ((n - 2) / 2) s), v))).map Prod.fst).Perm (sptToList s) := by
  let entries := l.filter (fun pair => pair.1 ≠ 0 ∧ pair.1 % 2 = 0)
  let keys := entries.map (fun pair => (pair.1 - 2) / 2)
  have valid : ∀ pair ∈ entries, pair.1 ≠ 0 ∧ pair.1 % 2 = 0 := by
    intro pair member
    simpa [entries] using (List.mem_filter.mp member).2
  have uniqueEntries : (entries.map Prod.fst).Nodup := by
    exact h.2.sublist (List.filter_sublist.map _)
  have unique : keys.Nodup := decodedFrameKeys_nodup entries valid uniqueEntries
  have dom : ∀ key, key ∈ keys ↔ (sptLookup key s).isSome = true := by
    intro key
    have adjustedValid : adjustVar key ≠ 0 ∧ adjustVar key % 2 = 0 := by
      simp only [adjustVar]
      omega
    have present : (sptAListLookup (adjustVar key) l).isSome = true ↔ adjustVar key ∈ l.map Prod.fst := by
      rw [← sptLookup_sptFromAList]
      change sptDomain (sptFromAList l) (adjustVar key) ↔ _
      rw [sptDomainFromAList]
    rw [h.1 key, present]
    constructor
    · intro member
      obtain ⟨pair, inEntries, eq⟩ := List.mem_map.mp member
      have validPair := valid pair inEntries
      have decoded := adjustVar_decode pair.1 validPair
      have inList : pair ∈ l := (List.mem_filter.mp inEntries).1
      exact List.mem_map.mpr ⟨pair, inList, by rw [← eq, decoded]⟩
    · intro member
      obtain ⟨pair, inList, eq⟩ := List.mem_map.mp member
      have v : pair.1 ≠ 0 ∧ pair.1 % 2 = 0 := by simpa [eq] using adjustedValid
      have inEntries : pair ∈ entries := by
        apply List.mem_filter.mpr
        exact ⟨inList, by simpa using v⟩
      apply List.mem_map.mpr
      refine ⟨pair, inEntries, ?_⟩
      rw [eq]
      simp [adjustVar]
  have entriesPerm := sptToAList_perm_of_keys s keys unique dom
  have values := (entriesPerm.map Prod.snd).trans (sptToAList_values_perm s)
  have same : (((entries.map (fun (n,v) => (holThe (sptLookup ((n-2)/2) s),v))).map Prod.fst)) =
      (keys.map fun key => (key, holThe (sptLookup key s))).map Prod.snd := by
    simp only [List.map_map, keys]
    rfl
  change (((entries.map (fun (n,v) => (holThe (sptLookup ((n-2)/2) s),v))).map Prod.fst)).Perm _
  rw [same]
  exact values

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
