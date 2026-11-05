import Flapjack.Compiler.Backend.GcShared.Reachability

/-! Abstract collector reachability conditions. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend

/-- Every data element in a heap is reachable from its roots. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_reachable_from_roots_def"]
def allReachableFromRoots {α β γ : Type} (roots : List (HeapAddress α)) (heap : List (HeapElement β γ)) : Prop :=
  ∀ ptr children len payload, heapLookup ptr heap = some (.dataElement children len payload) →
    reachableAddresses roots heap ptr

/-- Starting addresses of data elements in a heap. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "data_pointers_def"]
def dataPointers {α β : Type} : List (HeapElement α β) → List Nat
  | [] => []
  | .dataElement roots len payload :: tail =>
    0 :: (dataPointers tail).map (fun offset => offset + elLength (.dataElement roots len payload))
  | head :: tail => (dataPointers tail).map (fun offset => offset + elLength head)

/-- Encoded length of the element at an address, or zero if none starts there. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "lookup_len_def"]
def lookupLen {α β : Type} (heap : List (HeapElement α β)) (ptr : Nat) : Nat :=
  match heapLookup ptr heap with
  | none => 0
  | some element => elLength element

/-- Total encoded size at the data-element addresses. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "data_length_def"]
def dataLength {α β : Type} (heap : List (HeapElement α β)) : Nat :=
  ((dataPointers heap).map (lookupLen heap)).sum

/-- Appending an unused heap expansion adds no data addresses. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "data_pointers_heap_expand"]
theorem dataPointers_heapExpand {α β : Type} (heap : List (HeapElement α β)) (n : Nat) :
    dataPointers (heap ++ heapExpand n) = dataPointers heap := by
  have empty : dataPointers (heapExpand n : List (HeapElement α β)) = [] := by
    cases n <;> simp [heapExpand, dataPointers]
  induction heap with
  | nil => simpa [dataPointers] using empty
  | cons head tail ih => cases head <;> simp [dataPointers, ih]

/-- A heap expansion contains no data elements. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "data_length_heap_expand"]
theorem dataLength_heapExpand {α β : Type} (n : Nat) :
    dataLength (heapExpand n : List (HeapElement α β)) = 0 := by
  cases n <;> simp [dataLength, heapExpand, dataPointers]

/-- Looking up beyond a leading element is a lookup in its tail. -/
theorem lookupLen_cons_shift {α β : Type} (head : HeapElement α β) (tail : List (HeapElement α β)) (n : Nat) :
    lookupLen (head :: tail) (n + elLength head) = lookupLen tail n := by
  have positive : 0 < elLength head := by cases head <;> simp [elLength]
  have notZero : n + elLength head ≠ 0 := by omega
  have notInside : ¬ n + elLength head < elLength head := by omega
  simp only [lookupLen, heapLookup, notZero, notInside, if_false, Nat.add_sub_cancel]

/-- Data length is additive across the head of a heap. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "data_length_CONS"]
theorem dataLength_cons {α β : Type} (head : HeapElement α β) (tail : List (HeapElement α β)) :
    dataLength (head :: tail) = dataLength [head] + dataLength tail := by
  cases head <;>
    simp only [dataLength, dataPointers, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.map_map, Function.comp_def, lookupLen_cons_shift] <;>
    simp [lookupLen, heapLookup] <;> rfl

/-- Data length is additive under heap concatenation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "data_length_APPEND"]
theorem dataLength_append {α β : Type} (xs ys : List (HeapElement α β)) :
    dataLength (xs ++ ys) = dataLength xs + dataLength ys := by
  induction xs with
  | nil => simp [dataLength, dataPointers]
  | cons head tail ih =>
    rw [List.cons_append, dataLength_cons head (tail ++ ys), ih, dataLength_cons head tail,
      Nat.add_assoc]

/-- Appending unused space preserves data length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "data_length_APPEND_heap_expand"]
theorem dataLength_append_heapExpand {α β : Type} (heap : List (HeapElement α β)) (n : Nat) :
    dataLength (heap ++ heapExpand n) = dataLength heap := by
  simp [dataLength_append, dataLength_heapExpand]

/-- A heap consisting entirely of data elements has no non-data length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "data_length_heap_length"]
theorem dataLength_heapLength {α β : Type} (heap : List (HeapElement α β))
    (allData : ∀ element ∈ heap, isDataElement element) :
    dataLength heap = heapLength heap := by
  induction heap with
  | nil => simp [dataLength, dataPointers, heapLength]
  | cons head tail ih =>
    have headData : isDataElement head := allData head (by simp)
    have tailData : ∀ element ∈ tail, isDataElement element := by
      intro element member
      exact allData element (by simp [member])
    obtain ⟨ptrs, len, payload, rfl⟩ := headData
    rw [dataLength_cons, ih tailData]
    simp [dataLength, dataPointers, lookupLen, heapLookup, heapLength, elLength]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
