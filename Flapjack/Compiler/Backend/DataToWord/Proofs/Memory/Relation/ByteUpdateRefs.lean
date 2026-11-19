module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values.Stack
public import Flapjack.HolRef

@[expose] public section

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

/-- Inserting a byte array at an absent or byte-array key preserves all reachable
values because byte payloads contain no references or values. -/
theorem allValues_safeInsertByteArray (refs : Spt (BvlSem.Ref Value)) (stack : List Value)
    (ptr : Nat) (newFlag : Bool) (newBytes : List (BitVec 8))
    (safe : sptLookup ptr refs = none ∨ ∃ oldFlag oldBytes,
      sptLookup ptr refs = some (.byteArray oldFlag oldBytes)) :
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
        rcases safe with absent | ⟨oldFlag, oldBytes, found⟩ <;> simp_all
      · exact Or.inl ⟨index, values, by rw [sptLookup_sptInsert_ne ptr index _ refs same]; exact lookup, nested⟩
    · by_cases same : index = ptr
      · subst index
        rcases safe with absent | ⟨oldFlag, oldBytes, found⟩ <;> simp_all
      · exact Or.inr (Or.inl ⟨index, mode, child, by rw [sptLookup_sptInsert_ne ptr index _ refs same]; exact lookup, nested⟩)
    · by_cases same : index = ptr
      · subst index
        rcases safe with absent | ⟨oldFlag, oldBytes, found⟩ <;> simp_all
      · exact Or.inr (Or.inr (Or.inl ⟨index, tag, finalised, left, child, right,
          by rw [sptLookup_sptInsert_ne ptr index _ refs same]; exact lookup, nested⟩))
    · exact Or.inr (Or.inr (Or.inr stackMember))

/-- Inserting at an absent or byte-array key does not alter reference edges. -/
theorem refEdge_safeInsertByteArray (refs : Spt (BvlSem.Ref Value)) (ptr : Nat)
    (newFlag : Bool) (newBytes : List (BitVec 8))
    (safe : sptLookup ptr refs = none ∨ ∃ oldFlag oldBytes,
      sptLookup ptr refs = some (.byteArray oldFlag oldBytes)) :
    refEdge (sptInsert ptr (.byteArray newFlag newBytes) refs) = refEdge refs := by
  funext index target
  by_cases same : index = ptr
  · subst index
    rcases safe with absent | ⟨oldFlag, oldBytes, found⟩ <;>
      simp [refEdge, sptLookup_sptInsert_same, *]
  · simp [refEdge, sptLookup_sptInsert_ne ptr index _ refs same]

/-- Reference reachability paths are unchanged by a safe byte-array insertion. -/
theorem reachableRefs_safeInsertByteArray (refs : Spt (BvlSem.Ref Value)) (roots : List Value) (ptr : Nat)
    (newFlag : Bool) (newBytes : List (BitVec 8))
    (safe : sptLookup ptr refs = none ∨ ∃ oldFlag oldBytes,
      sptLookup ptr refs = some (.byteArray oldFlag oldBytes)) :
    reachableRefs roots (sptInsert ptr (.byteArray newFlag newBytes) refs) = reachableRefs roots refs := by
  funext target
  unfold reachableRefs
  rw [refEdge_safeInsertByteArray refs ptr newFlag newBytes safe]

/-- The directly stored values are unchanged by a safe byte-array insertion. -/
theorem findRef_safeInsertByteArray (refs : Spt (BvlSem.Ref Value)) (ptr index : Nat) (value : Value)
    (newFlag : Bool) (newBytes : List (BitVec 8))
    (safe : sptLookup ptr refs = none ∨ ∃ oldFlag oldBytes,
      sptLookup ptr refs = some (.byteArray oldFlag oldBytes)) :
    (∃ cell, sptLookup index (sptInsert ptr (.byteArray newFlag newBytes) refs) = some cell ∧ findRef cell value) ↔
      (∃ cell, sptLookup index refs = some cell ∧ findRef cell value) := by
  by_cases same : index = ptr
  · subst index
    rcases safe with absent | ⟨oldFlag, oldBytes, found⟩ <;>
      simp [sptLookup_sptInsert_same, findRef, *]
  · simp only [sptLookup_sptInsert_ne ptr index _ refs same]

/-- A safe byte-array insertion leaves the set of referenced timestamps intact. -/
theorem allTimestamps_safeInsertByteArray (refs : Spt (BvlSem.Ref Value)) (stack : List Value) (ptr : Nat)
    (newFlag : Bool) (newBytes : List (BitVec 8))
    (safe : sptLookup ptr refs = none ∨ ∃ oldFlag oldBytes,
      sptLookup ptr refs = some (.byteArray oldFlag oldBytes)) :
    allTimestamps (sptInsert ptr (.byteArray newFlag newBytes) refs) stack = allTimestamps refs stack := by
  funext stamp
  apply propext
  simp only [allTimestamps, findRef_safeInsertByteArray refs ptr _ _ newFlag newBytes safe]

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
