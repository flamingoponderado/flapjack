module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.LeafAllocate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Word64Push
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Allocating a Word64 cell and dropping corresponding stack prefixes
preserves the complete abstract machine invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word64_alt_thm"
  (words_as_type_indexed_bitvec)]
theorem word64Alt {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (ws stack : List Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (rs roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (be : Bool) (a sp sp1 : Nat) (gens : GenState) (limit ts : Nat)
    (word : BitVec 64) (len : Nat) (xs : List (WordLocW width))
    (inv : absMlInv conf (ws ++ stack) refs (rs ++ roots, heap, be, a, sp, sp1, gens) limit ts)
    (lengths : ws.length = rs.length)
    (rep : (word64Rep word : HeapElement (WordLocW width) (HeapTag × List (WordLocW width))) =
      .dataElement [] len (.word64Tag, xs)) (room : xs.length < sp) :
    ∃ heap2, heapStoreUnusedAlt a (sp + sp1) (word64Rep word) heap = (heap2, true) ∧
      absMlInv conf (.word64 word :: stack) refs
        (.pointer a (.word 0) :: roots, heap2, be, a + len + 1, sp - len - 1, sp1, gens) limit ts := by
  have lenEq : xs.length = len := by
    unfold word64Rep at rep
    split at rep <;> cases rep <;> rfl
  have fits : len + 1 ≤ sp := by omega
  obtain ⟨heap2, stored, lookup, _rel, popped⟩ := absMlInv_allocateLeaf conf ws stack refs rs roots heap
    be a sp sp1 gens limit ts len .word64Tag xs inv lengths (by simp [isMutTag]) fits
  refine ⟨heap2, ?_, ?_⟩
  · simpa [rep] using stored
  · refine ⟨?_, popped.2.1, popped.2.2.1, popped.2.2.2.1, ?_⟩
    · intro ptr value member
      rcases List.mem_cons.mp member with eq | old
      · cases eq
        rw [lookup]
        simp [isSomeDataElement]
      · exact popped.1 ptr value old
    · apply bcStackRefInv_pushWord64 conf ts stack refs roots heap2 be a word
      · simpa [rep] using lookup
      · exact popped.2.2.2.2
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
