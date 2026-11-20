module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.FreshByteValue
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.FreshBlock
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values.Timestamps
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Inserting a fresh byte array and allocating its heap cell preserves the
full stack/reference invariant. This helper supplies the stack portion of
HOL's `new_byte_alt_thm`. -/
theorem bcStackRefInv_freshByte {width : Nat} [NeZero width] (conf : Config) (next : Nat)
    (stack : List Value) (refs : Spt (BvlSem.Ref Value))
    (roots : List (HeapAddress (WordLocW width))) (heap heap1 : ValueHeap width)
    (be flag bit : Bool) (bytes : List (BitVec 8)) (ptr a : Nat)
    (freshRef : sptLookup ptr refs = none) (oldNot : ¬ isSomeDataElement (heapLookup a heap))
    (rel : heapStoreRel heap heap1)
    (newCell : heapLookup a heap1 = some (bytesRep be flag bytes (List.replicate (bytes.length / (width / 8) + 1) 0)))
    (valid : bcStackRefInv conf next stack refs (roots, heap, be)) :
    bcStackRefInv conf next (.refPtr bit ptr :: stack) (sptInsert ptr (.byteArray flag bytes) refs)
      (.pointer a (.word 0) :: roots, heap1, be) := by
  obtain ⟨f, tf, injF, domainF, injTf, timestamps, nextBound, endian, unique, stackInv, refsInv⟩ := valid
  have freshMap : f.lookup ptr = none := by
    cases found : f.lookup ptr with
    | none => rfl
    | some mapped =>
      obtain ⟨cell, lookup⟩ := domainF ptr ⟨mapped, found⟩
      simp [freshRef] at lookup
  have preserved (index : Nat) (old : isSomeDataElement (heapLookup index heap)) :
      isSomeDataElement (heapLookup index heap1) := by
    rw [rel index old]
    exact old
  have newData : isSomeDataElement (heapLookup a heap1) := by
    rw [newCell]
    simp [isSomeDataElement, bytesRep]
  have freshTarget : ∀ n, mapDomain f n → holFapply f n ≠ a := by
    intro n domain same
    apply oldNot
    rw [← same]
    exact injF.1 n domain
  have injF1 := freshBlock_timestampMap_injective f ptr a
    (fun p => isSomeDataElement (heapLookup p heap)) (fun p => isSomeDataElement (heapLookup p heap1))
    injF preserved newData freshTarget
  have injTf1 : mapInjInto tf (fun p => isSomeDataElement (heapLookup p heap1)) :=
    ⟨fun n domain => preserved _ (injTf.1 n domain), injTf.2⟩
  have newLookup : (f.update (ptr, a)).lookup ptr = some a := by simp [HolFiniteMapExact.update, FUPDATE]
  refine ⟨f.update (ptr, a), tf, injF1, ?_, injTf1, ?_, nextBound, endian, ?_, ?_, ?_⟩
  · intro n domain
    by_cases same : n = ptr
    · subst n
      exact ⟨.byteArray flag bytes, sptLookup_sptInsert_same _ _ _⟩
    · obtain ⟨mapped, lookup⟩ := domain
      have old : f.lookup n = some mapped := by
        simpa [HolFiniteMapExact.update, FUPDATE, same, Ne.symm same] using lookup
      obtain ⟨cell, found⟩ := domainF n ⟨mapped, old⟩
      exact ⟨cell, by simpa [sptLookup_sptInsert_ne ptr n _ refs same] using found⟩
  · intro stamp domain
    rw [allTimestamps_safeInsertByteArray refs (.refPtr bit ptr :: stack) ptr flag bytes (Or.inl freshRef)]
    rw [allTimestamps_consNoBlock refs stack (.refPtr bit ptr) (by simp)]
    exact timestamps stamp domain
  · exact blocksUnique_newByte next refs stack ptr flag bit bytes unique
  · apply List.Forall₂.cons
    · intro ck
      have refFound : sptLookup ptr (sptInsert ptr (.byteArray flag bytes) refs) = some (.byteArray flag bytes) :=
        sptLookup_sptInsert_same _ _ _
      have applied : holFapply (f.update (ptr, a)) ptr = a := holFapply_of_lookup newLookup
      have head := ClockValueInv.refPtr bit ck conf ptr (sptInsert ptr (.byteArray flag bytes) refs)
        (f.update (ptr, a)) tf heap1 ⟨a, newLookup⟩
        (by intro mode value; simp [refFound])
        (by intro tag finalised left child right h; simp [refFound] at h)
      simpa [applied, refFound, refPtrAnnot] using head
    · exact stackInv.imp (fun value address related =>
        valueInv_freshByte_heap conf refs ptr a flag bytes f tf heap heap1 value address freshRef freshMap rel related)
  · intro n ⟨reachable, domain⟩
    by_cases same : n = ptr
    · subst n
      simpa [bcRefInv, HolFiniteMapExact.update, FUPDATE, sptLookup_sptInsert_same] using newCell
    · obtain ⟨mapped, lookup⟩ := domain
      have oldLookup : f.lookup n = some mapped := by
        simpa [HolFiniteMapExact.update, FUPDATE, same, Ne.symm same] using lookup
      have oldReach := reachableRefs_freshByte_old refs stack ptr n bit flag bytes freshRef same reachable
      exact bcRefInv_freshByte_heap conf refs ptr a n flag bytes f tf heap heap1 be
        freshRef freshMap same rel (refsInv n ⟨oldReach, ⟨mapped, oldLookup⟩⟩)
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
