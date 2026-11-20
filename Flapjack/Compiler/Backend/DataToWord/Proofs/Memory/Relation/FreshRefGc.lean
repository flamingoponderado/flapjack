module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.HeapAllocate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.FreshBlockGc

@[expose] public section

/-! Collector bookkeeping for reference allocation in HOL's `new_ref_thm`. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Allocating a reference at the end of unused space moves the collector's
reference boundary. This Flapjack helper proves the GC case of `new_ref_thm`. -/
theorem gcKindInv_allocateFreshRef {α β : Type} (conf : DataToWord.Config) (addresses : List (HeapAddress α))
    (heap heap2 : List (HeapElement α (HeapTag × List β))) (a sp sp1 : Nat) (gens : GenState)
    (fits : addresses.length + 1 ≤ sp)
    (valid : gcKindInv conf a sp sp1 gens heap)
    (store : heapStoreUnused a (sp + sp1) (refBlock addresses) heap = (heap2, true))
    (unused : unusedSpaceInv a (sp + sp1 - (addresses.length + 1)) heap2) :
    gcKindInv conf a (sp - (addresses.length + 1)) sp1 gens heap2 := by
  cases kind : conf.gcKind with
  | none => simpa [gcKindInv, kind] using valid
  | simple => simpa [gcKindInv, kind] using valid
  | generational sizes =>
    simp only [gcKindInv, kind] at valid ⊢
    obtain ⟨oldGens, first, second, oldSplit, noRefs, refs⟩ := valid
    have newGens := heapStoreUnused_genStateOk a (sp + sp1) (refBlock addresses) heap heap2 gens ⟨store, by simpa [Nat.add_assoc] using oldGens⟩
    have elemLength : elLength (refBlock addresses : HeapElement α (HeapTag × List β)) = addresses.length + 1 := by simp [refBlock, elLength]
    have unused' : unusedSpaceInv a (sp + sp1 - elLength (refBlock addresses : HeapElement α (HeapTag × List β))) heap2 := by simpa [elemLength] using unused
    obtain ⟨before, firstEq, whole, aEq, heapEq⟩ := heapStoreUnused_shape a (sp + sp1) heap first second heap2 (refBlock addresses) ⟨by simpa [Nat.add_assoc] using oldSplit, store, unused'⟩
    let newPrefix := before ++ heapExpand (sp + sp1 - (addresses.length + 1))
    have newPrefixLength : heapLength newPrefix = a + (sp - (addresses.length + 1)) + sp1 := by
      simp [newPrefix, heapLength_append, heapLength_heapExpand, aEq]
      omega
    refine ⟨?_, newPrefix, refBlock addresses :: second, ?_, ?_, ?_⟩
    · have boundary : a + (sp + sp1) - (addresses.length + 1) = a + (sp - (addresses.length + 1)) + sp1 := by omega
      simpa [elemLength, boundary] using newGens
    · rw [← newPrefixLength, heapEq]
      simpa [newPrefix, elemLength, List.append_assoc] using Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.heapSplit_append newPrefix (refBlock addresses :: second)
    · intro element member
      simp only [newPrefix, List.mem_append] at member
      rcases member with old | free
      · apply noRefs element
        rw [firstEq]
        exact List.mem_append_left _ old
      · by_cases zero : sp + sp1 - (addresses.length + 1) = 0
        · simp [heapExpand, zero] at free
        · simp [heapExpand, zero] at free
          subst element
          simp [isRef]
    · intro element member
      rcases List.mem_cons.mp member with same | old
      · subst element
        simp [isRef, refBlock, isMutTag]
      · exact refs element old

/-- Allocate a reference block and preserve the root, heap and collector
components of the invariant. This supplies the allocation case of HOL's
`new_ref_thm`; the stack/reference component is proved separately. -/
theorem heapStoreUnused_freshRef_valid {α β : Type} (conf : DataToWord.Config)
    (a sp sp1 limit : Nat) (gens : GenState)
    (heap : List (HeapElement α (HeapTag × List β))) (fields roots : List (HeapAddress α))
    (zero : α) (unused : unusedSpaceInv a (sp + sp1) heap)
    (fits : fields.length + 1 ≤ sp) (rootsValid : rootsOk (fields ++ roots) heap)
    (heapValid : heapOk heap limit) (gcValid : gcKindInv conf a sp sp1 gens heap) :
    ∃ heap2, heapStoreUnused a (sp + sp1) (refBlock fields) heap = (heap2, true) ∧
      unusedSpaceInv a (sp - (fields.length + 1) + sp1) heap2 ∧
      heapLookup (a + sp + sp1 - (fields.length + 1)) heap2 = some (refBlock fields) ∧
      ¬ isSomeDataElement (heapLookup (a + sp + sp1 - (fields.length + 1)) heap) ∧
      heapStoreRel heap heap2 ∧
      rootsOk (fields ++ .pointer (a + sp + sp1 - (fields.length + 1)) zero :: roots) heap2 ∧
      heapOk heap2 limit ∧ gcKindInv conf a (sp - (fields.length + 1)) sp1 gens heap2 := by
  have len : elLength (refBlock fields : HeapElement α (HeapTag × List β)) = fields.length + 1 := by
    simp [refBlock, elLength]
  obtain ⟨heap2, stored, unused2, found, oldNot, lengthEq, forward, members, positions, rel⟩ :=
    heapStoreUnused_exists a (sp + sp1) heap (refBlock fields) unused (by rw [len]; omega)
  have preserved (ptr : Nat) (old : isSomeDataElement (heapLookup ptr heap)) :
      isSomeDataElement (heapLookup ptr heap2) := by
    rw [rel ptr old]
    exact old
  have newGc := gcKindInv_allocateFreshRef conf fields heap heap2 a sp sp1 gens fits gcValid stored
    (by simpa [len] using unused2)
  refine ⟨heap2, stored, ?_, ?_, ?_, rel, ?_, ?_, newGc⟩
  · have same : sp + sp1 - (fields.length + 1) = sp - (fields.length + 1) + sp1 := by omega
    simpa [len, same] using unused2
  · simpa [len, Nat.add_assoc] using found
  · simpa [len, Nat.add_assoc] using oldNot
  · intro ptr value member
    rcases List.mem_append.mp member with inFields | inTail
    · exact preserved ptr (rootsValid ptr value (List.mem_append_left _ inFields))
    · rcases List.mem_cons.mp inTail with equal | inRoots
      · cases equal
        rw [show a + sp + sp1 - (fields.length + 1) = a + (sp + sp1) - elLength (refBlock fields : HeapElement α (HeapTag × List β)) by rw [len]; omega, found]
        simp [isSomeDataElement, refBlock]
      · exact preserved ptr (rootsValid ptr value (List.mem_append_right _ inRoots))
  · refine ⟨lengthEq.trans heapValid.1, ?_, ?_⟩
    · exact (forward (by simp [isForwardPointer, refBlock])).trans heapValid.2.1
    · intro xs l d ptr value ⟨member, pointer⟩
      rcases (members xs l d).mp member with new | old
      · simp only [refBlock, HeapElement.dataElement.injEq] at new
        obtain ⟨rfl, _, _⟩ := new
        exact preserved ptr (rootsValid ptr value (List.mem_append_left _ pointer))
      · exact preserved ptr (heapValid.2.2 xs l d ptr value ⟨old, pointer⟩)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
