module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.HeapAllocate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StackOperations
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Allocating a nonempty constructor consumes its field roots and preserves the abstract ML invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "cons_thm_alt"
  (words_as_type_indexed_bitvec)]
theorem consThm_alt {width : Nat} [NeZero width] {β γ : Type} (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (xs stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (be : Bool) (a sp sp1 : Nat) (gens : GenState) (limit ts tag : Nat)
    (inv : absMlInv conf (xs ++ stack) refs (roots, heap, be, a, sp, sp1, gens) limit ts)
    (enough : xs.length < sp) (nonempty : xs ≠ []) :
    ∃ rs roots2 heap2, roots = rs ++ roots2 ∧ rs.length = xs.length ∧
      heapStoreUnusedAlt a (sp + sp1) (blockRep tag rs) heap = (heap2, true) ∧
      absMlInv conf (.block ts tag xs :: stack) refs
        (.pointer a (.word (ptrBits conf tag xs.length : BitVec width)) :: roots2,
         heap2, be, a + elLength (blockRep (β := β) tag rs), sp - elLength (blockRep (β := γ) tag rs), sp1, gens) limit (ts + 1) := by
  obtain ⟨rs, roots2, rootEq, rootLen⟩ := split1Thm conf xs stack refs roots heap be a sp sp1 gens limit ts inv
  have sizeAny (δ : Type) : elLength (blockRep (β := δ) tag rs) = rs.length + 1 := by simp [blockRep, elLength]
  have size : elLength (blockRep (β := WordLocW width) tag rs) = rs.length + 1 := by simp [blockRep, elLength]
  have fit : elLength (blockRep (β := WordLocW width) tag rs) ≤ sp := by rw [size, rootLen]; omega
  have alloc := heapStoreUnusedAlt_exists a (sp + sp1) heap (blockRep tag rs) inv.2.2.2.1 (by omega)
  obtain ⟨heap2, stored, unused2, lookup, old, len, forward, member, positions, preserved⟩ := alloc
  have positive : sp + sp1 ≠ 0 := by omega
  have found := inv.2.2.2.1.1 positive
  obtain ⟨pre, post, shape, aEq⟩ := heapLookup_split heap a _ found
  have expand : (heapExpand (sp + sp1) : ValueHeap width) = [.unused (sp + sp1 - 1)] := by
    unfold heapExpand
    rw [if_neg positive]
  have inv1 : absMlInv conf (xs ++ stack) refs (rs ++ roots2, pre ++ heapExpand (sp + sp1) ++ post, be,
      heapLength pre, sp, sp1, gens) limit ts := by
    simpa [rootEq, shape, aEq, expand, List.append_assoc] using inv
  have sizeEq : xs.length = rs.length := rootLen.symm
  have result := absMlInv_allocateBlock conf xs stack rs roots2 refs pre post sp sp1 ts tag limit be gens nonempty sizeEq
    (by rw [rootLen]; omega) inv1
  let newHeap := pre ++ [blockRep tag rs] ++ heapExpand (sp + sp1 - (rs.length + 1)) ++ post
  have heapEq : heap2 = newHeap := by
    unfold heapStoreUnusedAlt at stored
    classical
    simp only [found, show elLength (blockRep (β := WordLocW width) tag rs) ≤ sp + sp1 by omega, and_self, ↓reduceIte] at stored
    rw [shape, aEq, heapStore_atPrefix] at stored
    have eq := congrArg Prod.fst stored
    simpa [newHeap, size, List.append_assoc] using eq.symm
  have moved := moveThm conf stack refs roots2 newHeap be (a + elLength (blockRep (β := β) tag rs))
    (sp - elLength (blockRep (β := γ) tag rs)) sp1 gens limit (ts + 1)
    [] [] [.block ts tag xs] [.pointer a (.word (ptrBits conf tag xs.length))] xs rs
    (by
      refine ⟨?_, by simp, by simp, rootLen.symm⟩
      simpa [newHeap, aEq, sizeAny, rootLen, List.append_assoc] using result)
  have popped := popThm conf xs (.block ts tag xs :: stack) refs rs
    (.pointer a (.word (ptrBits conf tag xs.length)) :: roots2) newHeap be
    (a + elLength (blockRep (β := β) tag rs)) (sp - elLength (blockRep (β := γ) tag rs)) sp1 gens limit (ts + 1)
    (by simpa [List.append_assoc] using And.intro moved rootLen.symm)
  exact ⟨rs, roots2, heap2, rootEq, rootLen, stored, by simpa [heapEq] using popped⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
