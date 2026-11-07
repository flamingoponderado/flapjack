import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values.Stack
import Flapjack.HolRef

/-! Reference-graph invariants for byte-array replacement. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- A byte array contains no nested values, so inserting one can only remove
values from the reference traversal. -/
theorem allValues_insertByteArray_subset (refs : Spt (BvlSem.Ref Value)) (stack : List Value)
    (ptr : Nat) (flag : Bool) (bytes : List (BitVec 8)) (value : Value) :
    allValues (sptInsert ptr (.byteArray flag bytes) refs) stack value → allValues refs stack value := by
  intro member
  rcases member with ⟨index, values, lookup, nested⟩ | ⟨index, mode, child, lookup, nested⟩ |
    ⟨index, tag, finalised, left, child, right, lookup, nested⟩ | stackMember
  · by_cases same : index = ptr
    · subst index
      simp [sptLookup_sptInsert_same] at lookup
    · rw [sptLookup_sptInsert_ne ptr index _ refs same] at lookup
      exact Or.inl ⟨index, values, lookup, nested⟩
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

/-- Replacing an existing byte array preserves all reachable values because
neither its old nor its new byte payload contains references or values. -/
theorem allValues_replaceByteArray (refs : Spt (BvlSem.Ref Value)) (stack : List Value)
    (ptr : Nat) (oldFlag newFlag : Bool) (oldBytes newBytes : List (BitVec 8))
    (found : sptLookup ptr refs = some (.byteArray oldFlag oldBytes)) :
    allValues (sptInsert ptr (.byteArray newFlag newBytes) refs) stack = allValues refs stack := by
  funext value
  apply propext
  constructor
  · exact allValues_insertByteArray_subset refs stack ptr newFlag newBytes value
  · intro member
    rcases member with ⟨index, values, lookup, nested⟩ | ⟨index, mode, child, lookup, nested⟩ |
      ⟨index, tag, finalised, left, child, right, lookup, nested⟩ | stackMember
    · by_cases same : index = ptr
      · subst index
        rw [found] at lookup
        cases lookup
      · exact Or.inl ⟨index, values, by rw [sptLookup_sptInsert_ne ptr index _ refs same]; exact lookup, nested⟩
    · by_cases same : index = ptr
      · subst index
        rw [found] at lookup
        cases lookup
      · exact Or.inr (Or.inl ⟨index, mode, child, by rw [sptLookup_sptInsert_ne ptr index _ refs same]; exact lookup, nested⟩)
    · by_cases same : index = ptr
      · subst index
        rw [found] at lookup
        cases lookup
      · exact Or.inr (Or.inr (Or.inl ⟨index, tag, finalised, left, child, right,
          by rw [sptLookup_sptInsert_ne ptr index _ refs same]; exact lookup, nested⟩))
    · exact Or.inr (Or.inr (Or.inr stackMember))

/-- Replacing a byte payload does not alter any reference edge. -/
theorem refEdge_replaceByteArray (refs : Spt (BvlSem.Ref Value)) (ptr : Nat)
    (oldFlag newFlag : Bool) (oldBytes newBytes : List (BitVec 8))
    (found : sptLookup ptr refs = some (.byteArray oldFlag oldBytes)) :
    refEdge (sptInsert ptr (.byteArray newFlag newBytes) refs) = refEdge refs := by
  funext index target
  by_cases same : index = ptr
  · subst index
    simp [refEdge, sptLookup_sptInsert_same, found]
  · simp [refEdge, sptLookup_sptInsert_ne ptr index _ refs same]

/-- All reference reachability paths are unchanged by a byte payload update. -/
theorem reachableRefs_replaceByteArray (refs : Spt (BvlSem.Ref Value)) (roots : List Value) (ptr : Nat)
    (oldFlag newFlag : Bool) (oldBytes newBytes : List (BitVec 8))
    (found : sptLookup ptr refs = some (.byteArray oldFlag oldBytes)) :
    reachableRefs roots (sptInsert ptr (.byteArray newFlag newBytes) refs) = reachableRefs roots refs := by
  funext target
  unfold reachableRefs
  rw [refEdge_replaceByteArray refs ptr oldFlag newFlag oldBytes newBytes found]

/-- The directly stored values are unchanged when only a byte payload changes. -/
theorem findRef_replaceByteArray (refs : Spt (BvlSem.Ref Value)) (ptr index : Nat) (value : Value)
    (oldFlag newFlag : Bool) (oldBytes newBytes : List (BitVec 8))
    (found : sptLookup ptr refs = some (.byteArray oldFlag oldBytes)) :
    (∃ cell, sptLookup index (sptInsert ptr (.byteArray newFlag newBytes) refs) = some cell ∧ findRef cell value) ↔
      (∃ cell, sptLookup index refs = some cell ∧ findRef cell value) := by
  by_cases same : index = ptr
  · subst index
    simp [sptLookup_sptInsert_same, found, findRef]
  · simp only [sptLookup_sptInsert_ne ptr index _ refs same]

/-- A byte payload update leaves the set of all referenced timestamps intact. -/
theorem allTimestamps_replaceByteArray (refs : Spt (BvlSem.Ref Value)) (stack : List Value) (ptr : Nat)
    (oldFlag newFlag : Bool) (oldBytes newBytes : List (BitVec 8))
    (found : sptLookup ptr refs = some (.byteArray oldFlag oldBytes)) :
    allTimestamps (sptInsert ptr (.byteArray newFlag newBytes) refs) stack = allTimestamps refs stack := by
  funext stamp
  apply propext
  simp only [allTimestamps, findRef_replaceByteArray refs ptr _ _ oldFlag newFlag oldBytes newBytes found]

/-- Replacing a reference cell by a byte array preserves block uniqueness. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_insert_ByteArray"]
theorem blocksUnique_insertByteArray (next : Nat) (refs : Spt (BvlSem.Ref Value))
    (bit : Bool) (ptr : Nat) (stack : List Value) (flag : Bool) (bytes : List (BitVec 8)) :
    blocksUnique next (allValues refs (.refPtr bit ptr :: stack)) →
      blocksUnique next (allValues (sptInsert ptr (.byteArray flag bytes) refs) (.refPtr bit ptr :: stack)) := by
  intro unique stamp tag1 xs1 tag2 xs2 h
  exact unique stamp tag1 xs1 tag2 xs2
    ⟨allValues_insertByteArray_subset refs _ ptr flag bytes _ h.1, h.2.1,
      allValues_insertByteArray_subset refs _ ptr flag bytes _ h.2.2.1, h.2.2.2⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
