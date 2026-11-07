import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Reachability
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Heap pointer enumeration and its size bound. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Data-element start offsets in a heap are distinct. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "ALL_DISTINCT_data_pointers"]
theorem dataPointers_nodup {α β : Type} (heap : List (HeapElement α β)) :
    (dataPointers heap).Nodup := by
  induction heap with
  | nil => simp [dataPointers]
  | cons head tail ih =>
    cases head with
    | unused len =>
      simp only [dataPointers]
      exact ih.map (fun _ _ eq => Nat.add_right_cancel eq)
    | forwardPointer ptr value len =>
      simp only [dataPointers]
      exact ih.map (fun _ _ eq => Nat.add_right_cancel eq)
    | dataElement roots len payload =>
      simp only [dataPointers, List.nodup_cons]
      constructor
      · intro member
        obtain ⟨offset, _, equal⟩ := List.mem_map.mp member
        simp [elLength] at equal
      · exact ih.map (fun _ _ eq => Nat.add_right_cancel eq)

/-- A duplicate-free list of addresses from a larger list cannot have a
larger sum of heap element lengths. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "SUM_MAP_lookup_len_LESS_EQ"]
theorem sum_lookupLen_le {α β : Type} (heap : List (HeapElement α β)) (first second : List Nat)
    (subset : ∀ p ∈ first, p ∈ second) (distinct : first.Nodup) :
    ((first.map (lookupLen heap)).sum) ≤ ((second.map (lookupLen heap)).sum) := by
  obtain ⟨part, perm, sub⟩ := distinct.subperm subset
  have monotone : ∀ xs ys : List Nat, xs.Sublist ys →
      ((xs.map (lookupLen heap)).sum) ≤ ((ys.map (lookupLen heap)).sum) := by
    intro xs ys inclusion
    induction inclusion with
    | slnil => simp
    | cons x _ ih => simp only [List.map_cons, List.sum_cons]; omega
    | cons_cons x _ ih => simp only [List.map_cons, List.sum_cons]; omega
  have less := monotone part second sub
  have equal : (part.map (lookupLen heap)).sum = (first.map (lookupLen heap)).sum :=
    (perm.map (lookupLen heap)).sum_eq
  omega

/-- Flapjack infrastructure: a data pointer is enumerated exactly when heap
lookup finds a data element at that address. -/
theorem mem_dataPointers_iff {α β : Type} (heap : List (HeapElement α β)) (ptr : Nat) :
    ptr ∈ dataPointers heap ↔ isSomeDataElement (heapLookup ptr heap) := by
  induction heap generalizing ptr with
  | nil => simp [dataPointers, heapLookup, isSomeDataElement]
  | cons head tail ih =>
    have shifted (len : Nat) : ptr ∈ (dataPointers tail).map (fun offset => offset + len) ↔
        len ≤ ptr ∧ ptr - len ∈ dataPointers tail := by
      constructor
      · intro member
        obtain ⟨offset, present, equal⟩ := List.mem_map.mp member
        constructor
        · omega
        · have : ptr - len = offset := by omega
          simpa [this] using present
      · rintro ⟨bound, present⟩
        apply List.mem_map.mpr
        exact ⟨ptr - len, present, by omega⟩
    cases head with
    | unused len =>
      by_cases zero : ptr = 0
      · subst ptr; simp [dataPointers, heapLookup, isSomeDataElement, shifted, elLength]
      · by_cases inside : ptr < len + 1
        · simp [dataPointers, heapLookup, isSomeDataElement, shifted, elLength, zero, inside, Nat.not_le.mpr inside]
        · simp [dataPointers, heapLookup, isSomeDataElement, shifted, elLength, zero, inside, Nat.le_of_not_gt inside, ih]
    | forwardPointer dest value len =>
      by_cases zero : ptr = 0
      · subst ptr; simp [dataPointers, heapLookup, isSomeDataElement, shifted, elLength]
      · by_cases inside : ptr < len + 1
        · simp [dataPointers, heapLookup, isSomeDataElement, shifted, elLength, zero, inside, Nat.not_le.mpr inside]
        · simp [dataPointers, heapLookup, isSomeDataElement, shifted, elLength, zero, inside, Nat.le_of_not_gt inside, ih]
    | dataElement children len payload =>
      by_cases zero : ptr = 0
      · subst ptr; simp [dataPointers, heapLookup, isSomeDataElement]
      · by_cases inside : ptr < len + 1
        · simp [dataPointers, heapLookup, isSomeDataElement, shifted, elLength, zero, inside, Nat.not_le.mpr inside]
        · simp [dataPointers, heapLookup, isSomeDataElement, shifted, elLength, zero, inside, Nat.le_of_not_gt inside, ih]

/-- The set of enumerated data pointers equals the data-element lookup domain. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "set_data_pointers"]
theorem set_dataPointers {α β : Type} (heap : List (HeapElement α β)) :
    {ptr | ptr ∈ dataPointers heap} = {ptr | isSomeDataElement (heapLookup ptr heap)} := by
  funext ptr
  exact propext (mem_dataPointers_iff heap ptr)

/-- Flapjack infrastructure: when all data objects are reachable, any list
covering the reachable addresses accounts for at least their total size. -/
theorem dataLength_le_reachableCover {α β γ : Type}
    (roots : List (HeapAddress α)) (heap : List (HeapElement β γ)) (cover : List Nat)
    (reachable : allReachableFromRoots roots heap)
    (covers : ∀ ptr, reachableAddresses roots heap ptr → ptr ∈ cover) :
    dataLength heap ≤ ((cover.map (lookupLen heap)).sum) := by
  apply sum_lookupLen_le heap (dataPointers heap) cover
  · intro ptr member
    obtain ⟨children, len, payload, found⟩ := (mem_dataPointers_iff heap ptr).mp member
    exact covers ptr (reachable ptr children len payload found)
  · exact dataPointers_nodup heap

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
