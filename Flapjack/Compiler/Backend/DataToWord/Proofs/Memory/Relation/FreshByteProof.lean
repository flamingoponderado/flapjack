module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.FreshByteStack
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.LeafAllocate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BytePacking
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Allocating a fresh byte array preserves the complete abstract invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "new_byte_alt_thm"
  (words_as_type_indexed_bitvec)]
theorem newByteAlt {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (stack : List Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (be : Bool) (a sp sp1 : Nat) (gens : GenState) (limit ts ws ptr : Nat)
    (flag bit : Bool) (bytes : List (BitVec 8))
    (inv : absMlInv conf stack refs (roots, heap, be, a, sp, sp1, gens) limit ts)
    (size : ws = bytes.length / (width / 8) + 1) (fresh : ¬ sptDomain refs ptr)
    (fits : ws + 1 ≤ sp) :
    ∃ heap2, heapStoreUnusedAlt a (sp + sp1) (bytesRep be flag bytes (List.replicate ws 0)) heap = (heap2, true) ∧
      absMlInv conf (.refPtr bit ptr :: stack) (sptInsert ptr (.byteArray flag bytes) refs)
        (.pointer a (.word 0) :: roots, heap2, be, a + ws + 1, sp - (ws + 1), sp1, gens) limit ts := by
  have freshRef : sptLookup ptr refs = none := by
    cases found : sptLookup ptr refs with
    | none => rfl
    | some value => exact False.elim (fresh ((sptDomain_iff_lookup refs ptr).mpr ⟨value, found⟩))
  let payload := (DataToWord.writeBytes bytes (List.replicate ws (0 : BitVec width)) be).map WordLocW.word
  have cellEq : bytesRep be flag bytes (List.replicate ws 0) =
      .dataElement [] ws (.bytesTag flag bytes.length, payload) := by
    simp [bytesRep, payload, writeBytes_wordCount]
  have initial : absMlInv conf ([] ++ stack) refs ([] ++ roots, heap, be, a, sp, sp1, gens) limit ts := by
    simpa using inv
  obtain ⟨heap2, stored, lookup, rel, after⟩ := absMlInv_allocateLeaf conf [] stack refs [] roots heap
    be a sp sp1 gens limit ts ws (.bytesTag flag bytes.length) payload initial rfl (by simp [isMutTag]) fits
  have oldNot : ¬ isSomeDataElement (heapLookup a heap) := by
    have positive : sp + sp1 ≠ 0 := by omega
    have found := inv.2.2.2.1.1 positive
    rw [found]
    simp [isSomeDataElement]
  have newCell : heapLookup a heap2 = some (bytesRep be flag bytes (List.replicate (bytes.length / (width / 8) + 1) 0)) := by
    rw [← size, cellEq]
    exact lookup
  have stackAfter := bcStackRefInv_freshByte conf ts stack refs roots heap heap2 be flag bit bytes ptr a
    freshRef oldNot rel newCell inv.2.2.2.2
  refine ⟨heap2, ?_, ?_⟩
  · rw [cellEq]
    exact stored
  · refine ⟨?_, after.2.1, ?_, ?_, stackAfter⟩
    · intro index value member
      rcases List.mem_cons.mp member with equal | old
      · cases equal
        rw [lookup]
        simp [isSomeDataElement]
      · exact after.1 index value old
    · simpa [Nat.sub_sub] using after.2.2.1
    · simpa [Nat.sub_sub] using after.2.2.2.1
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
