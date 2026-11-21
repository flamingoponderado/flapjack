module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.GenerationalSplit
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.CollectorGenerational
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Preliminaries
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialSplit

@[expose] public section

/-!
# Data/reference partition lemmas for the generational collector

Counterparts of `gc_move_data_refs_split` through `isRef_heap_expand` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`. HOL
`EVERY P l` is `∀ x ∈ l, P x`; the collector configuration's Boolean `isRef`
is compared with `= true`, as in the reviewed `gen_gc_data_refs_split`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend

/-- `dataRefsSplit` stated over the concatenated segments. -/
theorem dataRefsSplit_iff {α β : Type} (s : GcState α (HeapTag × β)) :
    dataRefsSplit s ↔
      (∀ x ∈ s.h1 ++ s.h2, isDataElement x) ∧ (∀ x ∈ s.h1 ++ s.h2, ¬ isRef x) ∧
        ∀ x ∈ s.r1 ++ s.r2 ++ s.r3 ++ s.r4, isRef x := by
  simp only [dataRefsSplit, List.mem_append, or_imp, forall_and]
  constructor
  · rintro ⟨⟨h1d, h1r⟩, ⟨h2d, h2r⟩, r1, r2, r3, r4⟩
    exact ⟨⟨h1d, h2d⟩, ⟨h1r, h2r⟩, ⟨⟨r1, r2⟩, r3⟩, r4⟩
  · rintro ⟨⟨h1d, h2d⟩, ⟨h1r, h2r⟩, ⟨⟨r1, r2⟩, r3⟩, r4⟩
    exact ⟨⟨h1d, h1r⟩, ⟨h2d, h2r⟩, r1, r2, r3, r4⟩

/-- HOL `gc_move_data_refs_split`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gc_move_data_refs_split"]
theorem gcMove_dataRefsSplit_source {α β : Type} (cc : GenGc.Config (HeapTag × β))
    (s : GcState α (HeapTag × β)) (x x1 : HeapAddress α) (s1 : GcState α (HeapTag × β)) :
    GenGc.gcMove cc s x = (x1, s1) ∧ (∀ t r, cc.isRef (t, r) = true ↔ isMutTag t) ∧
      (∀ e ∈ s.h2, isDataElement e) ∧ (∀ e ∈ s.h2, ¬ isRef e) ∧ (∀ e ∈ s.r4, isRef e) →
    (∀ e ∈ s1.h2, isDataElement e) ∧ (∀ e ∈ s1.h2, ¬ isRef e) ∧ ∀ e ∈ s1.r4, isRef e := by
  rintro ⟨run, classify, data, notRef, refs⟩
  have result := gcMove_pendingDataRefsSplit cc s x classify ⟨data, notRef, refs⟩
  rw [run] at result
  exact result

/-- HOL `gc_move_list_data_refs_split`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gc_move_list_data_refs_split"]
theorem gcMoveList_dataRefsSplit_source {α β : Type} (cc : GenGc.Config (HeapTag × β)) :
    ∀ (x x1 : List (HeapAddress α)) (s s1 : GcState α (HeapTag × β)),
      GenGc.gcMoveList cc s x = (x1, s1) ∧ (∀ t r, cc.isRef (t, r) = true ↔ isMutTag t) ∧
        (∀ e ∈ s.h2, isDataElement e) ∧ (∀ e ∈ s.h2, ¬ isRef e) ∧ (∀ e ∈ s.r4, isRef e) →
      (∀ e ∈ s1.h2, isDataElement e) ∧ (∀ e ∈ s1.h2, ¬ isRef e) ∧ ∀ e ∈ s1.r4, isRef e := by
  rintro x x1 s s1 ⟨run, classify, data, notRef, refs⟩
  have result := gcMoveList_pendingDataRefsSplit cc s x classify ⟨data, notRef, refs⟩
  rw [run] at result
  exact result

/-- HOL `gc_move_refs_data_refs_split`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gc_move_refs_data_refs_split"]
theorem gcMoveRefs_dataRefsSplit_source {α β : Type} :
    ∀ (cc : GenGc.Config (HeapTag × β)) (s s1 : GcState α (HeapTag × β)),
      GenGc.gcMoveRefs cc s = s1 ∧ (∀ t r, cc.isRef (t, r) = true ↔ isMutTag t) ∧
        (∀ e ∈ s.h1 ++ s.h2, isDataElement e) ∧ (∀ e ∈ s.h1 ++ s.h2, ¬ isRef e) ∧
        (∀ e ∈ s.r1 ++ s.r2 ++ s.r3 ++ s.r4, isRef e) →
      (∀ e ∈ s1.h1 ++ s1.h2, isDataElement e) ∧ (∀ e ∈ s1.h1 ++ s1.h2, ¬ isRef e) ∧
        ∀ e ∈ s1.r1 ++ s1.r2 ++ s1.r3 ++ s1.r4, isRef e := by
  rintro cc s s1 ⟨rfl, classify, data, notRef, refs⟩
  exact (dataRefsSplit_iff _).mp
    (gcMoveRefs_dataRefsSplit cc s classify ((dataRefsSplit_iff s).mpr ⟨data, notRef, refs⟩))

/-- HOL `gc_move_data_data_refs_split`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gc_move_data_data_refs_split"]
theorem gcMoveData_dataRefsSplit_source {α β : Type} :
    ∀ (cc : GenGc.Config (HeapTag × β)) (s s1 : GcState α (HeapTag × β)),
      GenGc.gcMoveData cc s = s1 ∧ (∀ t r, cc.isRef (t, r) = true ↔ isMutTag t) ∧
        (∀ e ∈ s.h1 ++ s.h2, ¬ isRef e) ∧ (∀ e ∈ s.h1 ++ s.h2, isDataElement e) ∧
        (∀ e ∈ s.r1 ++ s.r2 ++ s.r3 ++ s.r4, isRef e) →
      (∀ e ∈ s1.h1 ++ s1.h2, isDataElement e) ∧ (∀ e ∈ s1.h1 ++ s1.h2, ¬ isRef e) ∧
        ∀ e ∈ s1.r1 ++ s1.r2 ++ s1.r3 ++ s1.r4, isRef e := by
  rintro cc s s1 ⟨rfl, classify, notRef, data, refs⟩
  exact (dataRefsSplit_iff _).mp
    (gcMoveData_dataRefsSplit cc s classify ((dataRefsSplit_iff s).mpr ⟨data, notRef, refs⟩))

/-- HOL `gc_move_loop_data_refs_split`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gc_move_loop_data_refs_split"]
theorem gcMoveLoop_dataRefsSplit_source {α β : Type} :
    ∀ (clock : Nat) (cc : GenGc.Config (HeapTag × β)) (s s1 : GcState α (HeapTag × β)),
      GenGc.gcMoveLoop cc s clock = s1 ∧ (∀ t r, cc.isRef (t, r) = true ↔ isMutTag t) ∧
        (∀ e ∈ s.h1 ++ s.h2, isDataElement e) ∧ (∀ e ∈ s.h1 ++ s.h2, ¬ isRef e) ∧
        (∀ e ∈ s.r1 ++ s.r2 ++ s.r3 ++ s.r4, isRef e) →
      (∀ e ∈ s1.h1 ++ s1.h2, isDataElement e) ∧ (∀ e ∈ s1.h1 ++ s1.h2, ¬ isRef e) ∧
        ∀ e ∈ s1.r1 ++ s1.r2 ++ s1.r3 ++ s1.r4, isRef e := by
  rintro clock cc s s1 ⟨rfl, classify, data, notRef, refs⟩
  exact (dataRefsSplit_iff _).mp
    (gcMoveLoop_dataRefsSplit cc s clock classify ((dataRefsSplit_iff s).mpr ⟨data, notRef, refs⟩))

/-- HOL `heap_expand_not_isRef`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_expand_not_isRef"]
theorem heapExpand_not_isRef {α β : Type} (n : Nat) :
    ∀ x ∈ (heapExpand n : List (HeapElement α (HeapTag × β))), ¬ isRef x := by
  intro x member
  unfold heapExpand at member
  split at member
  · simp at member
  · simp only [List.mem_singleton] at member
    subst member
    simp [isRef]

/-- A heap prefix of zero words is empty. -/
theorem heapLength_eq_zero {α β : Type} (heap : List (HeapElement α β)) (h : heapLength heap = 0) :
    heap = [] := by
  cases heap with
  | nil => rfl
  | cons x xs =>
    have : 0 < elLength x := by cases x <;> simp [elLength]
    simp [heapLength] at h
    omega

/-- HOL `heap_split_heap_split`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_split_heap_split"]
theorem heapSplit_heapSplit {α β : Type} :
    ∀ (heap : List (HeapElement α β)) (n1 n2 : Nat) (h1 h2 h3 h4 : List (HeapElement α β)),
      heapSplit n2 heap = some (h3, h4) ∧ heapSplit n1 heap = some (h1, h2) ∧ n1 ≤ n2 →
      ∃ m, h2 = m ++ h4 ∧ h3 = h1 ++ m ∧ heap = h1 ++ m ++ h4 ∧
        heapSplit (n2 - heapLength h1) h2 = some (m, h4) := by
  intro heap n1 n2 h1 h2 h3 h4 ⟨s2, s1, le⟩
  obtain ⟨len1, -, rfl⟩ := heapSplit_heapLength heap h1 h2 n1 s1
  obtain ⟨len3, -, eq⟩ := heapSplit_heapLength (h1 ++ h2) h3 h4 n2 s2
  rcases List.append_eq_append_iff.mp eq.symm with ⟨m, rfl, rfl⟩ | ⟨c, rfl, rfl⟩
  · refine ⟨m, rfl, rfl, by simp, ?_⟩
    have : n2 - heapLength h1 = heapLength m := by
      rw [← len3, heapLength_append]; omega
    rw [this]
    exact DataToWord.Proofs.Gc.heapSplit_append m h4
  · rw [heapLength_append] at len1
    have c0 : c = [] := heapLength_eq_zero c (by omega)
    subst c0
    refine ⟨[], by simp, by simp, by simp, ?_⟩
    have : n2 - heapLength (h3 ++ []) = 0 := by simp at len1 ⊢; omega
    rw [this]
    cases h2 <;> simp [heapSplit]

/-- HOL `heap_split_LESS_EQ`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_split_LESS_EQ"]
theorem heapSplit_le {α β : Type} :
    ∀ (heap : List (HeapElement α β)) (n : Nat) (x : List (HeapElement α β) × List (HeapElement α β)),
      heapSplit n heap = some x → n ≤ heapLength heap := by
  rintro heap n ⟨first, second⟩ split
  obtain ⟨len, -, rfl⟩ := heapSplit_heapLength heap first second n split
  rw [heapLength_append]
  omega

/-- HOL `isRef_heap_expand`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "isRef_heap_expand"]
theorem isRef_heapExpand {α β : Type} :
    ∀ x : Nat, ∀ y ∈ (heapExpand x : List (HeapElement α (HeapTag × β))), ¬ isRef y :=
  fun x => heapExpand_not_isRef x

/-- HOL `gen_state_ok_reset`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gen_state_ok_reset"]
theorem genStateOk_reset {α β : Type} (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (h r : List (HeapElement α β)) (n l : Nat) :
    heapOk (h ++ heapExpand n ++ r) l →
      genStateOk (heapLength h) (n + heapLength h) (h ++ heapExpand n ++ r)
        (resetGens conf (heapLength h)) := by
  intro ok
  have split : heapSplit (heapLength h) (h ++ heapExpand n ++ r) = some (h, heapExpand n ++ r) := by
    rw [List.append_assoc]
    exact DataToWord.Proofs.Gc.heapSplit_append h _
  have startOk : genStartOk (h ++ heapExpand n ++ r) (n + heapLength h) (heapLength h) := by
    refine ⟨h, heapExpand n ++ r, split, ?_⟩
    rintro xs len data ptr value ⟨element, pointer⟩
    have target := ok.2.2 xs len data ptr value
      ⟨List.mem_append_left _ (List.mem_append_left _ element), pointer⟩
    by_contra bad
    simp only [not_or, Nat.not_lt] at bad
    rw [List.append_assoc, heapLookup_append1 h ptr _ bad.1] at target
    have pos : 0 < n := by omega
    have expand : (heapExpand n : List (HeapElement α β)) = [.unused (n - 1)] := by
      simp [heapExpand, show n ≠ 0 by omega]
    rw [expand] at target
    obtain ⟨xs', len', data', found⟩ := target
    by_cases z : ptr - heapLength h = 0
    · simp [heapLookup, z] at found
    · have inside : ptr - heapLength h < elLength (HeapElement.unused (α := α) (β := β) (n - 1)) := by
        simp [elLength]; omega
      simp [heapLookup, z, inside] at found
  unfold resetGens
  split
  · refine ⟨?_, ?_⟩ <;> intro start member <;> simp only [List.mem_map] at member <;>
      obtain ⟨_, _, rfl⟩ := member
    · exact Nat.le_refl _
    · exact startOk
  · exact ⟨by simp, by simp⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
