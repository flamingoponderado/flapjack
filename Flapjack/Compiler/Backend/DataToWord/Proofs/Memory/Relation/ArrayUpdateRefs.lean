import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values.Stack
import Flapjack.HolRef

/-! Reference-graph invariants for value-array replacement. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- If the replacement array's values are already on the stack, inserting it
can introduce no value outside the original traversal. -/
theorem allValues_insertValueArray_subset (refs : Spt (BvlSem.Ref Value))
    (values stack : List Value) (ptr : Nat) (value : Value) :
    allValues (sptInsert ptr (.valueArray values) refs) (values ++ stack) value →
      allValues refs (values ++ stack) value := by
  intro member
  rcases member with ⟨index, items, lookup, nested⟩ | ⟨index, mode, child, lookup, nested⟩ |
    ⟨index, tag, finalised, left, child, right, lookup, nested⟩ | stackMember
  · by_cases same : index = ptr
    · subst index
      simp only [sptLookup_sptInsert_same, Option.some.injEq, BvlSem.Ref.valueArray.injEq] at lookup
      subst items
      apply Or.inr (Or.inr (Or.inr ?_))
      rw [valueListValues_append, List.mem_append]
      exact Or.inl nested
    · rw [sptLookup_sptInsert_ne ptr index _ refs same] at lookup
      exact Or.inl ⟨index, items, lookup, nested⟩
  · by_cases same : index = ptr
    · subst index
      simp [sptLookup_sptInsert_same] at lookup
    · rw [sptLookup_sptInsert_ne ptr index _ refs same] at lookup
      exact Or.inr (Or.inl ⟨index, mode, child, lookup, nested⟩)
  · by_cases same : index = ptr
    · subst index
      simp [sptLookup_sptInsert_same] at lookup
    · rw [sptLookup_sptInsert_ne ptr index _ refs same] at lookup
      exact Or.inr (Or.inr (Or.inl ⟨index, tag, finalised, left, child, right, lookup, nested⟩))
  · exact Or.inr (Or.inr (Or.inr stackMember))

/-- A value-array replacement preserves block uniqueness when its new values
are also included among the stack roots. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_update_ref"]
theorem blocksUnique_updateRef (next : Nat) (refs : Spt (BvlSem.Ref Value))
    (values : List Value) (bit : Bool) (ptr : Nat) (stack : List Value) :
    blocksUnique next (allValues refs (values ++ .refPtr bit ptr :: stack)) →
      blocksUnique next (allValues (sptInsert ptr (.valueArray values) refs) (values ++ .refPtr bit ptr :: stack)) := by
  intro unique stamp tag1 xs1 tag2 xs2 h
  exact unique stamp tag1 xs1 tag2 xs2
    ⟨allValues_insertValueArray_subset refs values _ ptr _ h.1, h.2.1,
      allValues_insertValueArray_subset refs values _ ptr _ h.2.2.1, h.2.2.2⟩

/-- A single array element can be replaced without introducing new traversed
values if the replacement is already a stack root. -/
theorem allValues_insertValueArray_set_subset (refs : Spt (BvlSem.Ref Value))
    (roots stack old : List Value) (ptr i : Nat) (replacement value : Value)
    (found : sptLookup ptr refs = some (.valueArray old)) (root : replacement ∈ roots) :
    allValues (sptInsert ptr (.valueArray (old.set i replacement)) refs) (roots ++ stack) value →
      allValues refs (roots ++ stack) value := by
  intro member
  rcases member with ⟨index, items, lookup, nested⟩ | ⟨index, mode, child, lookup, nested⟩ |
    ⟨index, tag, finalised, left, child, right, lookup, nested⟩ | stackMember
  · by_cases same : index = ptr
    · subst index
      simp only [sptLookup_sptInsert_same, Option.some.injEq, BvlSem.Ref.valueArray.injEq] at lookup
      subst items
      obtain ⟨child, childMember, childNested⟩ := valueListValues_member_origin _ value nested
      rcases List.mem_or_eq_of_mem_set childMember with oldMember | newEq
      · exact Or.inl ⟨ptr, old, found, valueListValues_singleton_subset old child value oldMember childNested⟩
      · subst child
        apply Or.inr (Or.inr (Or.inr ?_))
        rw [valueListValues_append, List.mem_append]
        exact Or.inl (valueListValues_singleton_subset roots replacement value root childNested)
    · rw [sptLookup_sptInsert_ne ptr index _ refs same] at lookup
      exact Or.inl ⟨index, items, lookup, nested⟩
  · by_cases same : index = ptr
    · subst index
      simp [sptLookup_sptInsert_same] at lookup
    · rw [sptLookup_sptInsert_ne ptr index _ refs same] at lookup
      exact Or.inr (Or.inl ⟨index, mode, child, lookup, nested⟩)
  · by_cases same : index = ptr
    · subst index
      simp [sptLookup_sptInsert_same] at lookup
    · rw [sptLookup_sptInsert_ne ptr index _ refs same] at lookup
      exact Or.inr (Or.inr (Or.inl ⟨index, tag, finalised, left, child, right, lookup, nested⟩))
  · exact Or.inr (Or.inr (Or.inr stackMember))

/-- Block uniqueness is preserved by updating one array entry with an existing
root. This generalized infrastructure is used to recover the HOL head case. -/
theorem blocksUnique_updateRef_set (next : Nat) (refs : Spt (BvlSem.Ref Value))
    (roots stack old : List Value) (ptr i : Nat) (replacement : Value)
    (found : sptLookup ptr refs = some (.valueArray old)) (root : replacement ∈ roots)
    (unique : blocksUnique next (allValues refs (roots ++ stack))) :
    blocksUnique next (allValues (sptInsert ptr (.valueArray (old.set i replacement)) refs) (roots ++ stack)) := by
  intro stamp tag1 xs1 tag2 xs2 h
  exact unique stamp tag1 xs1 tag2 xs2
    ⟨allValues_insertValueArray_set_subset refs roots stack old ptr i replacement _ found root h.1, h.2.1,
      allValues_insertValueArray_set_subset refs roots stack old ptr i replacement _ found root h.2.2.1, h.2.2.2⟩

/-- Replacing an array entry with the first stack root preserves block
uniqueness. The default in `headD` is unreachable under the nonempty premise. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_update_ref1"]
theorem blocksUnique_updateRef1 (next : Nat) (refs : Spt (BvlSem.Ref Value))
    (roots old : List Value) (bit : Bool) (ptr i : Nat) (stack : List Value) :
    0 < roots.length ∧ sptLookup ptr refs = some (.valueArray old) ∧
      blocksUnique next (allValues refs (roots ++ .refPtr bit ptr :: stack)) →
    blocksUnique next (allValues (sptInsert ptr (.valueArray (old.set i (roots.headD (.number 0)))) refs)
      (roots ++ .refPtr bit ptr :: stack)) := by
  rintro ⟨nonempty, found, unique⟩
  apply blocksUnique_updateRef_set next refs roots (.refPtr bit ptr :: stack) old ptr i _ found
  · cases roots with
    | nil => simp at nonempty
    | cons head tail => simp
  · exact unique

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
