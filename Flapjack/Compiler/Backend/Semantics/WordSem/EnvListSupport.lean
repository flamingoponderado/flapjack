import Flapjack.Compiler.Backend.Semantics.WordSem.Env

/-!
# Environment-list lookup support

Flapjack-specific support for the exact `wordSemEnvToList` port. The HOL
`PERM_list_rearrange` fact used by Cake's `env_to_list_lookup_equiv` belongs to
the external HOL list library rather than a CakeML declaration, so this
membership lemma is intentionally untagged.
-/

namespace Flapjack

/-- The exact HOL `list_rearrange` rendering used by `wordSemEnvToList`
preserves list membership. This is Flapjack-specific infrastructure for
reconstructing the external HOL permutation fact without weakening the tagged
`env_to_list_lookup_equiv` theorem. -/
theorem wordSemListRearrange_mem_iff {α : Type} (mover : Nat → Nat)
    (xs : List α) (value : α) :
    value ∈ wordSemListRearrange mover xs ↔ value ∈ xs := by
  unfold wordSemListRearrange
  by_cases hbij : wordSemBijCount mover xs.length
  · simp only [dif_pos hbij, List.mem_map]
    constructor
    · rintro ⟨⟨index, hindex⟩, _hmem, hvalue⟩
      have hbound : index < xs.length := List.mem_range.mp hindex
      have hmoved : mover index < xs.length := hbij.1.1 index hbound
      rw [← hvalue]
      exact List.getElem_mem hmoved
    · intro hvalue
      obtain ⟨index, hindex, hvalue⟩ := List.mem_iff_getElem.mp hvalue
      obtain ⟨source, hsource, hmove⟩ := hbij.2.2 index hindex
      refine ⟨⟨source, List.mem_range.mpr hsource⟩, ?_, ?_⟩
      · exact List.mem_attach _ _
      · simp [hmove, hvalue]
  · simp [hbij]

/-- Membership in the exact HOL `merge_tail` rendering is membership in one of
its two input lists or its accumulator. This is untagged Flapjack support for
the external permutation argument in Cake's `env_to_list_lookup_equiv`. -/
theorem wordSemMergeTail_mem_iff {α : Type} (negate : Bool)
    (compare : α → α → Bool) (left right accumulator : List α) (value : α) :
    value ∈ Basis.Pure.MlList.mergeTail negate compare left right accumulator ↔
      value ∈ left ∨ value ∈ right ∨ value ∈ accumulator := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          rw [Basis.Pure.MlList.mergeTail.eq_1]
          simp
      | cons head tail =>
          rw [Basis.Pure.MlList.mergeTail.eq_3]
          · simp [List.mem_append, List.mem_reverse, or_assoc, or_left_comm,
              or_comm]
          · simp
  | cons head tail =>
      cases right with
      | nil =>
          rw [Basis.Pure.MlList.mergeTail.eq_2]
          · simp [List.mem_append, List.mem_reverse, or_assoc, or_left_comm,
              or_comm]
          · simp
      | cons rightHead rightTail =>
          rw [Basis.Pure.MlList.mergeTail.eq_4]
          by_cases h : (compare head rightHead != negate) = true
          · rw [if_pos h]
            have ih := wordSemMergeTail_mem_iff negate compare tail
              (rightHead :: rightTail) (head :: accumulator) value
            simpa [or_assoc, or_left_comm, or_comm] using ih
          · rw [if_neg h]
            have ih := wordSemMergeTail_mem_iff negate compare
              (head :: tail) rightTail (rightHead :: accumulator) value
            simpa [or_assoc, or_left_comm, or_comm] using ih
termination_by left.length + right.length
decreasing_by all_goals simp_wf

/-- Membership in `mergesortN_tail` is exactly membership in the sorted prefix
of the requested length. This is untagged support for the external
`sort_PERM` fact used by the CakeML `env_to_list_lookup_equiv` proof. -/
theorem wordSemMergeSortN_mem_take {α : Type} (compare : α → α → Bool) :
    ∀ (size : Nat) (negate : Bool) (xs : List α) (value : α),
      size ≤ xs.length →
      (value ∈ Basis.Pure.MlList.mergesortNTail negate compare size xs ↔
        value ∈ xs.take size) := by
  intro size negate
  induction size using Nat.strongRecOn generalizing negate with
  | ind size ih =>
      intro xs value hsize
      cases size with
      | zero =>
          simp [Basis.Pure.MlList.mergesortNTail.eq_1]
      | succ size =>
          cases size with
          | zero =>
              cases xs with
              | nil => simp at hsize
              | cons head tail =>
                  rw [Basis.Pure.MlList.mergesortNTail.eq_2]
                  simp
          | succ size =>
              cases size with
              | zero =>
                  cases xs with
                  | nil => simp at hsize
                  | cons first rest =>
                      cases rest with
                      | nil => simp at hsize
                      | cons second tail =>
                          rw [Basis.Pure.MlList.mergesortNTail.eq_4]
                          by_cases h : compare first second = negate <;>
                            simp_all [Basis.Pure.MlList.sort2Tail, or_comm]
              | succ size =>
                  cases size with
                  | zero =>
                      cases xs with
                      | nil => simp at hsize
                      | cons first rest =>
                          cases rest with
                          | nil => simp at hsize
                          | cons second rest =>
                              cases rest with
                              | nil => simp at hsize
                              | cons third tail =>
                                  rw [Basis.Pure.MlList.mergesortNTail.eq_7]
                                  by_cases h12 : compare first second = negate
                                  · by_cases h23 : compare second third = negate
                                    · by_cases h13 : compare first third = negate <;>
                                        simp_all [Basis.Pure.MlList.sort3Tail,
                                          or_left_comm, or_comm]
                                    · by_cases h13 : compare first third = negate <;>
                                        simp_all [Basis.Pure.MlList.sort3Tail,
                                          or_left_comm, or_comm]
                                  · by_cases h23 : compare second third = negate
                                    · by_cases h13 : compare first third = negate <;>
                                        simp_all [Basis.Pure.MlList.sort3Tail,
                                          or_left_comm, or_comm]
                                    · by_cases h13 : compare first third = negate <;>
                                        simp_all [Basis.Pure.MlList.sort3Tail,
                                          or_comm]
                  | succ size =>
                      let total := size + 4
                      let first := total / 2
                      let second := total - first
                      rw [Basis.Pure.MlList.mergesortNTail.eq_11]
                      have hfirst : first ≤ xs.length := by
                        dsimp [first, total]
                        omega
                      have hsecond : second ≤ (xs.drop first).length := by
                        dsimp [second, total]
                        simp only [List.length_drop]
                        omega
                      have hfirstLt : first < total := by
                        dsimp [first, total]
                        omega
                      have hsecondLt : second < total := by
                        dsimp [second, total]
                        omega
                      have hleft := ih first hfirstLt (!negate) xs value hfirst
                      have hright := ih second hsecondLt (!negate)
                        (xs.drop first) value hsecond
                      rw [wordSemMergeTail_mem_iff]
                      simp only [List.not_mem_nil, or_false]
                      rw [hleft, hright]
                      constructor
                      · rintro (hfirstMem | hsecondMem)
                        · rcases List.mem_take_iff_getElem.mp hfirstMem with ⟨index, hindex, hvalue⟩
                          apply List.mem_take_iff_getElem.mpr
                          refine ⟨index, ?_, ?_⟩
                          · omega
                          · exact hvalue
                        · rcases List.mem_take_iff_getElem.mp hsecondMem with ⟨index, hindex, hvalue⟩
                          apply List.mem_take_iff_getElem.mpr
                          refine ⟨first + index, ?_, ?_⟩
                          · omega
                          · rw [List.getElem_drop] at hvalue
                            simpa [Nat.add_comm] using hvalue
                      · intro hmem
                        rcases List.mem_take_iff_getElem.mp hmem with ⟨index, hindex, hvalue⟩
                        by_cases hbefore : index < first
                        · apply Or.inl
                          apply List.mem_take_iff_getElem.mpr
                          exact ⟨index, by
                            omega, hvalue⟩
                        · apply Or.inr
                          apply List.mem_take_iff_getElem.mpr
                          refine ⟨index - first, ?_, ?_⟩
                          · omega
                          · have hindexEq : first + (index - first) = index := by omega
                            simpa [List.getElem_drop, hindexEq] using hvalue

/-- The exact HOL mergesort implementation preserves membership. This is
untagged infrastructure for `env_to_list_lookup_equiv`, not a CakeML
declaration of its own. -/
theorem wordSemSort_mem_iff {α : Type} (compare : α → α → Bool)
    (xs : List α) (value : α) :
    value ∈ Basis.Pure.MlList.sort compare xs ↔ value ∈ xs := by
  have h := wordSemMergeSortN_mem_take compare xs.length false xs value (by simp)
  simpa [Basis.Pure.MlList.sort, Basis.Pure.MlList.mergesortTail] using h

/-- The exact HOL `env_to_list` implementation preserves the association-list
entries from `toAList`: its `sort` and `list_rearrange` stages preserve
membership. -/
theorem wordSemEnvToList_mem_iff {width : Nat} [NeZero width]
    (env : Spt (WordLocW width)) (bijSeq : Nat → Nat → Nat)
    (entry : Nat × WordLocW width) :
    entry ∈ (wordSemEnvToList env bijSeq).1 ↔ entry ∈ sptToAList env := by
  simp [wordSemEnvToList, wordSemListRearrange_mem_iff,
    wordSemSort_mem_iff]

/-- An association emitted by the exact HOL Sptree `toAList` traversal is
exactly a successful lookup. The proof uses the external HOL Sptree
`foldi`/`spt_acc` address argument, rendered untagged in `Misc.Sptree`. -/
theorem sptToAList_mem_iff_lookup {α : Type} (tree : Spt α)
    (key : Nat) (value : α) :
    (key, value) ∈ sptToAList tree ↔ sptLookup key tree = some value := by
  constructor
  · intro hmem
    have hfold :
        (key, value) ∈
          sptFoldi (fun k v entries => (k, v) :: entries) 0 [] tree := by
      simpa [sptToAList] using hmem
    rcases sptFoldi_mem_address tree 0 [] key value hfold with hacc |
      ⟨localKey, haddr, hlookup⟩
    · simp at hacc
    · have hkey : key = localKey := by
        simpa [sptAcc_eq, lrNext] using haddr
      subst localKey
      exact hlookup
  · intro hlookup
    have hfold := sptFoldi_lookup_mem tree 0 [] key value hlookup
    simpa [sptToAList, sptAcc_eq, lrNext] using hfold

/-- Exact HOL `env_to_list_lookup_equiv` from
`cakeml/compiler/backend/semantics/wordPropsScript.sml:4636-4663`. Given the
HOL environment-list result equation, both source conclusions are preserved:
association-list lookup agrees with Spt lookup, and every emitted association
has that same source lookup value. The Spt carrier is exact; HOL's indexed word
dimension is represented by `WordLocW width`. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml"
  "env_to_list_lookup_equiv" (words_as_type_indexed_bitvec)]
theorem wordSemEnvToListLookupEquiv {width : Nat} [NeZero width]
    (env : Spt (WordLocW width)) (bijSeq : Nat → Nat → Nat)
    (entries : List (Nat × WordLocW width)) (permutation : Nat → Nat → Nat)
    (hresult : wordSemEnvToList env bijSeq = (entries, permutation)) :
    (∀ key, sptAListLookup key entries = sptLookup key env) ∧
    (∀ key value, (key, value) ∈ entries → sptLookup key env = some value) := by
  have hentries : entries = (wordSemEnvToList env bijSeq).1 :=
    (congrArg Prod.fst hresult).symm
  constructor
  · intro key
    by_cases hnone : sptLookup key env = none
    · cases halookup : sptAListLookup key entries with
      | none => simp [hnone]
      | some value =>
          have hqmem : (key, value) ∈ entries :=
            sptAListLookup_mem key entries value halookup
          have hpipeline :
              (key, value) ∈ (wordSemEnvToList env bijSeq).1 := by
            simpa [hentries] using hqmem
          have hsourceMem :=
            (wordSemEnvToList_mem_iff env bijSeq (key, value)).mp hpipeline
          have hsourceLookup :=
            (sptToAList_mem_iff_lookup env key value).mp hsourceMem
          rw [hnone] at hsourceLookup
          cases hsourceLookup
    · have hexists : ∃ value, sptLookup key env = some value := by
        cases hlookup : sptLookup key env with
        | none => exact (hnone hlookup).elim
        | some value => exact ⟨value, rfl⟩
      obtain ⟨value, hlookup⟩ := hexists
      have hsourceMem : (key, value) ∈ sptToAList env :=
        (sptToAList_mem_iff_lookup env key value).mpr hlookup
      have hpipeline :=
        (wordSemEnvToList_mem_iff env bijSeq (key, value)).mpr hsourceMem
      have hqmem : (key, value) ∈ entries := by
        simpa [hentries] using hpipeline
      have hunique : ∀ other, (key, other) ∈ entries → other = value := by
        intro other hother
        have hotherPipeline :
            (key, other) ∈ (wordSemEnvToList env bijSeq).1 := by
          simpa [hentries] using hother
        have hotherSourceMem :=
          (wordSemEnvToList_mem_iff env bijSeq (key, other)).mp hotherPipeline
        have hotherLookup :=
          (sptToAList_mem_iff_lookup env key other).mp hotherSourceMem
        rw [hlookup] at hotherLookup
        injection hotherLookup with hvalue
        exact hvalue.symm
      have halookup :=
        sptAListLookup_eq_of_mem_unique key value entries hqmem hunique
      exact halookup.trans hlookup.symm
  · intro key value hqmem
    have hpipeline :
        (key, value) ∈ (wordSemEnvToList env bijSeq).1 := by
      simpa [hentries] using hqmem
    have hsourceMem :=
      (wordSemEnvToList_mem_iff env bijSeq (key, value)).mp hpipeline
    exact (sptToAList_mem_iff_lookup env key value).mp hsourceMem

end Flapjack
