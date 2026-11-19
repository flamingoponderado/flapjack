module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Word64Allocate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.HeapStoreRel
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StackOperations
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Allocating an immutable pointer-free cell and dropping aligned prefixes
preserves the abstract invariant. This Flapjack helper shares the allocation
bookkeeping used in HOL's Word64 and bignum proofs. -/
theorem absMlInv_allocateLeaf {width : Nat} [NeZero width] (conf : Config)
    (ws stack : List Value) (refs : Spt (BvlSem.Ref Value))
    (rs roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (be : Bool) (a sp sp1 : Nat) (gens : GenState) (limit ts len : Nat)
    (tag : HeapTag) (xs : List (WordLocW width))
    (inv : absMlInv conf (ws ++ stack) refs (rs ++ roots, heap, be, a, sp, sp1, gens) limit ts)
    (lengths : ws.length = rs.length) (immutable : ¬ isMutTag tag) (fits : len + 1 ≤ sp) :
    ∃ heap2, heapStoreUnusedAlt a (sp + sp1) (.dataElement [] len (tag, xs)) heap = (heap2, true) ∧
      heapLookup a heap2 = some (.dataElement [] len (tag, xs)) ∧
      absMlInv conf stack refs (roots, heap2, be, a + len + 1, sp - len - 1, sp1, gens) limit ts := by
  obtain ⟨heap2, stored, unused2, lookup, rel, roots2, heapValid⟩ :=
    heapStoreUnusedAlt_leaf_valid a (sp + sp1) len limit (tag, xs) (.word 0) heap (rs ++ roots)
      inv.2.2.2.1 (by omega) inv.1 inv.2.1
  have positive : sp + sp1 ≠ 0 := by omega
  have found := inv.2.2.2.1.1 positive
  obtain ⟨pre, post, shape, aEq⟩ := heapLookup_split heap a _ found
  have expand : (heapExpand (sp + sp1) : ValueHeap width) = [.unused (sp + sp1 - 1)] := by
    unfold heapExpand
    rw [if_neg positive]
  have gcOld : gcKindInv conf (heapLength pre) sp sp1 gens (pre ++ heapExpand (sp + sp1) ++ post) := by
    simpa [shape, aEq, expand, List.append_assoc] using inv.2.2.1
  have gcNew := gcKindInv_allocateData conf pre post [] xs tag sp sp1 len gens immutable fits gcOld
  let newHeap := pre ++ [.dataElement [] len (tag, xs)] ++ heapExpand (sp + sp1 - (len + 1)) ++ post
  have heapEq : heap2 = newHeap := by
    unfold heapStoreUnusedAlt at stored
    classical
    simp only [found, show elLength (.dataElement [] len (tag, xs) : HeapElement (WordLocW width) (HeapTag × List (WordLocW width))) ≤ sp + sp1 by simp [elLength]; omega, and_self, ↓reduceIte] at stored
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
  exact ⟨heap2, stored, lookup,
    popThm conf ws stack refs rs roots heap2 be (a + len + 1) (sp - len - 1) sp1 gens limit ts ⟨inv2, lengths⟩⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
