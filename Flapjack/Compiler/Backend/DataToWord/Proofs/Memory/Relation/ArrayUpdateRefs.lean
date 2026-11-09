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

/-- Replacing an array with values that are already roots or belonged to the
old array does not introduce newly reachable references. The pointer to the
updated array must itself be a root. -/
theorem reachableRefs_insertValueArray_subset (refs : Spt (BvlSem.Ref Value))
    (roots replacement : List Value) (ptr : Nat) (bit : Bool)
    (pointerRoot : .refPtr bit ptr ∈ roots)
    (origin : ∀ value ∈ replacement, value ∈ roots ∨
      ∃ old, sptLookup ptr refs = some (.valueArray old) ∧ value ∈ old)
    (target : Nat) :
    reachableRefs roots (sptInsert ptr (.valueArray replacement) refs) target → reachableRefs roots refs target := by
  have step : ∀ source dest, reachableRefs roots refs source →
      refEdge (sptInsert ptr (.valueArray replacement) refs) source dest → reachableRefs roots refs dest := by
    intro source dest reachable edge
    by_cases same : source = ptr
    · subst source
      simp only [refEdge, sptLookup_sptInsert_same, getRefs, List.mem_flatMap] at edge
      obtain ⟨value, member, reference⟩ := edge
      rcases origin value member with rootMember | ⟨old, oldLookup, oldMember⟩
      · exact ⟨value, dest, rootMember, reference, Relation.ReflTransGen.refl⟩
      · have oldEdge : refEdge refs ptr dest := by
          simp only [refEdge, oldLookup, getRefs, List.mem_flatMap]
          exact ⟨value, oldMember, reference⟩
        exact ⟨.refPtr bit ptr, ptr, pointerRoot, by simp [getRefs],
          Relation.ReflTransGen.single oldEdge⟩
    · have oldEdge : refEdge refs source dest := by
        simpa [refEdge, sptLookup_sptInsert_ne ptr source _ refs same] using edge
      obtain ⟨root, start, member, reference, path⟩ := reachable
      exact ⟨root, start, member, reference, path.tail oldEdge⟩
  rintro ⟨root, start, rootMember, reference, path⟩
  have startReach : reachableRefs roots refs start := ⟨root, start, rootMember, reference, Relation.ReflTransGen.refl⟩
  induction path with
  | refl => exact startReach
  | tail path edge ih => exact step _ _ ih edge

/-- Replacing an array with a stack prefix cannot make new references reachable. -/
theorem reachableRefs_updateValueArray (refs : Spt (BvlSem.Ref Value))
    (values stack : List Value) (ptr : Nat) (bit : Bool) (target : Nat) :
    reachableRefs (values ++ .refPtr bit ptr :: stack) (sptInsert ptr (.valueArray values) refs) target →
      reachableRefs (values ++ .refPtr bit ptr :: stack) refs target := by
  apply reachableRefs_insertValueArray_subset refs _ values ptr bit
  · simp
  · intro value member
    exact Or.inl (List.mem_append_left _ member)

/-- Updating a single array entry with a root cannot make new references
reachable, even when the index is out of bounds. -/
theorem reachableRefs_updateValueArray_set (refs : Spt (BvlSem.Ref Value))
    (roots stack old : List Value) (ptr i : Nat) (bit : Bool) (replacement : Value)
    (found : sptLookup ptr refs = some (.valueArray old)) (root : replacement ∈ roots) (target : Nat) :
    reachableRefs (roots ++ .refPtr bit ptr :: stack) (sptInsert ptr (.valueArray (old.set i replacement)) refs) target →
      reachableRefs (roots ++ .refPtr bit ptr :: stack) refs target := by
  apply reachableRefs_insertValueArray_subset refs _ _ ptr bit
  · simp
  · intro value member
    rcases List.mem_or_eq_of_mem_set member with oldMember | equal
    · exact Or.inr ⟨old, found, oldMember⟩
    · subst value
      exact Or.inl (List.mem_append_left _ root)

/-- Replacing an array with values already on the stack or in the old array
cannot introduce new timestamps into the stack/reference invariant. -/
theorem allTimestamps_insertValueArray_subset (refs : Spt (BvlSem.Ref Value))
    (roots replacement : List Value) (ptr : Nat)
    (origin : ∀ value ∈ replacement, value ∈ roots ∨
      ∃ old, sptLookup ptr refs = some (.valueArray old) ∧ value ∈ old)
    (stamp : Nat) :
    allTimestamps (sptInsert ptr (.valueArray replacement) refs) roots stamp → allTimestamps refs roots stamp := by
  rintro ⟨value, fromRefs | fromRoots, timestamp⟩
  · obtain ⟨index, cell, lookup, contains⟩ := fromRefs
    by_cases same : index = ptr
    · subst index
      simp only [sptLookup_sptInsert_same, Option.some.injEq] at lookup
      subst cell
      simp only [findRef] at contains
      rcases origin value contains with rootMember | ⟨old, oldLookup, oldMember⟩
      · exact ⟨value, Or.inr rootMember, timestamp⟩
      · exact ⟨value, Or.inl ⟨ptr, .valueArray old, oldLookup, oldMember⟩, timestamp⟩
    · rw [sptLookup_sptInsert_ne ptr index _ refs same] at lookup
      exact ⟨value, Or.inl ⟨index, cell, lookup, contains⟩, timestamp⟩
  · exact ⟨value, Or.inr fromRoots, timestamp⟩

/-- The single-element update case of timestamp inclusion. -/
theorem allTimestamps_updateValueArray_set_subset (refs : Spt (BvlSem.Ref Value))
    (roots stack old : List Value) (ptr i : Nat) (replacement : Value)
    (found : sptLookup ptr refs = some (.valueArray old)) (root : replacement ∈ roots) (stamp : Nat) :
    allTimestamps (sptInsert ptr (.valueArray (old.set i replacement)) refs) (roots ++ stack) stamp →
      allTimestamps refs (roots ++ stack) stamp := by
  apply allTimestamps_insertValueArray_subset refs _ _ ptr
  intro value member
  rcases List.mem_or_eq_of_mem_set member with oldMember | equal
  · exact Or.inr ⟨old, found, oldMember⟩
  · subst value
    exact Or.inl (List.mem_append_left _ root)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
