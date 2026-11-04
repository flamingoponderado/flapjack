import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ArrayUpdateValue

/-! The abstract heap-store operation used by data-to-word memory proofs. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack

/-- Replace the heap element at a word offset with a list of heap elements.
The returned flag records whether the replacement has exactly the old size. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_store_def"]
def heapStore {α β : Type} (offset : Nat) (replacement : List (HeapElement α β)) :
    List (HeapElement α β) → List (HeapElement α β) × Bool
  | [] => ([], false)
  | head :: tail =>
      if offset = 0 then (replacement ++ tail, decide (elLength head = heapLength replacement))
      else if offset < elLength head then (head :: tail, false)
      else let (rest, success) := heapStore (offset - elLength head) replacement tail
        (head :: rest, success)

/-- Storing at a heap-pre boundary replaces exactly the next element and
reports whether its allocated length matches the replacement. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_store_lemma"]
theorem heapStore_atPrefix {α β : Type} (pre replacement : List (HeapElement α β))
    (cell : HeapElement α β) (suffix : List (HeapElement α β)) :
    heapStore (heapLength pre) replacement (pre ++ cell :: suffix) =
      (pre ++ replacement ++ suffix, decide (heapLength replacement = elLength cell)) := by
  induction pre with
  | nil =>
    by_cases same : (replacement.map elLength).sum = elLength cell <;>
      simp [heapStore, heapLength, eq_comm, same]
  | cons head tail ih =>
    have positive : 0 < elLength head := by cases head <;> simp [elLength]
    change heapStore (elLength head + heapLength tail) replacement (head :: (tail ++ cell :: suffix)) = _
    simp only [heapStore, show ¬ elLength head + heapLength tail = 0 by omega, ↓reduceIte,
      show ¬ elLength head + heapLength tail < elLength head by omega, Nat.add_sub_cancel_left, ih]
    rfl

/-- Equal-sized reference blocks can be replaced at their heap-pre boundary. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_store_RefBlock_thm"]
theorem heapStore_refBlock {α β : Type} (pre suffix : List (HeapElement α (HeapTag × List β)))
    (after before : List (HeapAddress α)) :
    after.length = before.length →
      heapStore (heapLength pre) [refBlock after] (pre ++ refBlock before :: suffix) =
        (pre ++ refBlock after :: suffix, true) := by
  intro sameLength
  rw [heapStore_atPrefix]
  simp [heapLength, refBlock, elLength, sameLength]

/-- Equal-sized reference-block replacement preserves data-cell lookup at every
heap offset. Unlike payload-only updates, the pointer fields may change. -/
theorem refBlock_replace_isSomeData {α β : Type} (pre post : List (HeapElement α (HeapTag × List β)))
    (before after : List (HeapAddress α)) (sameLength : before.length = after.length) (offset : Nat) :
    isSomeDataElement (heapLookup offset (pre ++ [refBlock before] ++ post)) ↔
      isSomeDataElement (heapLookup offset (pre ++ [refBlock after] ++ post)) := by
  by_cases here : offset = heapLength pre
  · subst offset
    rw [heapLookup_refBlock_here, heapLookup_refBlock_here]
    simp [isSomeDataElement, refBlock]
  · have size : elLength (refBlock (β := β) before) = elLength (refBlock (β := β) after) := by
      simp [refBlock, elLength, sameLength]
    rw [heapLookup_replace_ne pre post _ _ size offset here]

/-- Storing an equally sized reference block gives an explicit new heap,
preserves other data-cell locations and leaves every other lookup unchanged.
This is Flapjack infrastructure toward the original local heap-store lemma. -/
theorem heapStore_refBlock_effect {α β : Type} (heap : List (HeapElement α (HeapTag × List β)))
    (offset : Nat) (before after : List (HeapAddress α))
    (sameLength : before.length = after.length)
    (found : heapLookup offset heap = some (refBlock before)) :
    ∃ heap2, heapStore offset [refBlock after] heap = (heap2, true) ∧
      refBlockInv heap heap2 ∧ heapLookup offset heap2 = some (refBlock after) ∧
      heapLength heap2 = heapLength heap ∧
      heap2.filter isForwardPointer = heap.filter isForwardPointer ∧
      (∀ pointers len data, .dataElement pointers len data ∈ heap2 →
        .dataElement pointers len data = refBlock after ∨ .dataElement pointers len data ∈ heap) ∧
      (∀ n, isSomeDataElement (heapLookup n heap2) ↔ isSomeDataElement (heapLookup n heap)) ∧
      ∀ n cell, n ≠ offset → heapLookup n heap = some cell → heapLookup n heap2 = some cell := by
  obtain ⟨pre, post, heapEq, offsetEq⟩ := heapLookup_split heap offset _ found
  subst heap
  subst offset
  refine ⟨pre ++ [refBlock after] ++ post, ?_, ?_, heapLookup_refBlock_here pre post after, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [List.append_assoc] using heapStore_refBlock pre post after before sameLength.symm
  · simpa only [List.append_assoc, List.singleton_append] using refBlockInv_replace pre post before after sameLength
  · simp [heapLength, refBlock, elLength, sameLength, List.map_append, List.sum_append]
  · simp [List.filter_append, refBlock, isForwardPointer]
  · intro pointers len data member
    simp only [List.mem_append, List.mem_cons] at member ⊢
    rcases member with (inPre | equal) | inPost <;> simp_all
  · intro n
    simpa only [List.append_assoc, List.singleton_append] using
      (refBlock_replace_isSomeData pre post before after sameLength n).symm
  · intro n cell different old
    have size : elLength (refBlock (β := β) before) = elLength (refBlock (β := β) after) := by
      simp [refBlock, elLength, sameLength]
    rw [← heapLookup_replace_ne pre post _ _ size n different]
    simpa only [List.append_assoc, List.singleton_append] using old

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
