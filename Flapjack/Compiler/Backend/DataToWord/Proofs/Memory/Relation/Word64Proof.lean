module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Word64Allocate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Word64Push
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.HeapStoreRel
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
  obtain ⟨heap2, stored, unused2, lookup, rel, roots2, heapValid⟩ :=
    heapStoreUnusedAlt_leaf_valid a (sp + sp1) len limit (.word64Tag, xs) (.word 0) heap (rs ++ roots)
      inv.2.2.2.1 (by omega) inv.1 inv.2.1
  have positive : sp + sp1 ≠ 0 := by omega
  have found := inv.2.2.2.1.1 positive
  obtain ⟨pre, post, shape, aEq⟩ := heapLookup_split heap a _ found
  have expand : (heapExpand (sp + sp1) : ValueHeap width) = [.unused (sp + sp1 - 1)] := by
    unfold heapExpand
    rw [if_neg positive]
  have gcOld : gcKindInv conf (heapLength pre) sp sp1 gens (pre ++ heapExpand (sp + sp1) ++ post) := by
    simpa [shape, aEq, expand, List.append_assoc] using inv.2.2.1
  have gcNew := gcKindInv_allocateData conf pre post [] xs .word64Tag sp sp1 len gens (by simp [isMutTag]) fits gcOld
  let newHeap := pre ++ [.dataElement [] len (.word64Tag, xs)] ++ heapExpand (sp + sp1 - (len + 1)) ++ post
  have heapEq : heap2 = newHeap := by
    unfold heapStoreUnusedAlt at stored
    classical
    simp only [found, show elLength (.dataElement [] len (.word64Tag, xs) : HeapElement (WordLocW width) (HeapTag × List (WordLocW width))) ≤ sp + sp1 by simp [elLength]; omega, and_self, ↓reduceIte] at stored
    rw [shape, aEq, heapStore_atPrefix] at stored
    have eq := congrArg Prod.fst stored
    simpa [newHeap, elLength, List.append_assoc] using eq.symm
  have gcResult : gcKindInv conf (a + len + 1) (sp - len - 1) sp1 gens heap2 := by
    have arith : sp - len - 1 = sp - (len + 1) := by omega
    simpa [heapEq, newHeap, aEq, arith, Nat.add_assoc] using gcNew
  have unusedResult : unusedSpaceInv (a + len + 1) (sp - len - 1 + sp1) heap2 := by
    have arith : sp + sp1 - (len + 1) = sp - len - 1 + sp1 := by omega
    simpa [arith, Nat.add_assoc] using unused2
  have oldRoots : rootsOk (rs ++ roots) heap2 := by
    intro ptr value member
    exact roots2 ptr value (List.mem_cons_of_mem _ member)
  have stack2 := bcStackRefInv_heapStoreRel conf ts (ws ++ stack) refs (rs ++ roots) heap heap2 be rel inv.2.2.2.2
  have inv2 : absMlInv conf (ws ++ stack) refs (rs ++ roots, heap2, be, a + len + 1, sp - len - 1, sp1, gens) limit ts :=
    ⟨oldRoots, heapValid, gcResult, unusedResult, stack2⟩
  have popped := popThm conf ws stack refs rs roots heap2 be (a + len + 1) (sp - len - 1) sp1 gens limit ts ⟨inv2, lengths⟩
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
