module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.HeapAllocate
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.GcCombined

/-- Allocation of a pointer-free data cell preserves the root and heap
invariants. This Flapjack proof helper supplies the heap-validity steps in
HOL's `word64_alt_thm`. -/
theorem heapStoreUnusedAlt_leaf_valid {α β : Type}
    (a sp len limit : Nat) (payload : β) (annotation : α)
    (heap : List (HeapElement α β)) (roots : List (HeapAddress α))
    (unused : unusedSpaceInv a sp heap) (fits : len + 1 ≤ sp)
    (rootsValid : rootsOk roots heap) (heapValid : heapOk heap limit) :
    ∃ heap2, heapStoreUnusedAlt a sp (.dataElement [] len payload) heap = (heap2, true) ∧
      unusedSpaceInv (a + (len + 1)) (sp - (len + 1)) heap2 ∧
      heapLookup a heap2 = some (.dataElement [] len payload) ∧
      heapStoreRel heap heap2 ∧
      rootsOk (.pointer a annotation :: roots) heap2 ∧ heapOk heap2 limit := by
  obtain ⟨heap2, stored, unused2, found, oldNot, lengthEq, forward, members, positions, rel⟩ :=
    heapStoreUnusedAlt_exists a sp heap (.dataElement [] len payload) unused (by simpa [elLength] using fits)
  have preserved (ptr : Nat) (old : isSomeDataElement (heapLookup ptr heap)) :
      isSomeDataElement (heapLookup ptr heap2) := by
    rw [rel ptr old]
    exact old
  refine ⟨heap2, stored, ?_, found, rel, ?_, ?_⟩
  · simpa [elLength] using unused2 (by simp [isDataElement])
  · intro ptr value member
    rcases List.mem_cons.mp member with eq | old
    · cases eq
      rw [found]
      simp [isSomeDataElement]
    · exact preserved ptr (rootsValid ptr value old)
  · refine ⟨lengthEq.trans heapValid.1, ?_, ?_⟩
    · exact (forward (by simp [isForwardPointer])).trans heapValid.2.1
    · intro xs l d ptr value ⟨member, pointer⟩
      rcases (members xs l d).mp member with new | old
      · cases new
        simp at pointer
      · exact preserved ptr (heapValid.2.2 xs l d ptr value ⟨old, pointer⟩)
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
