module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdateValue
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv.Submap
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- A fresh byte-array reference and its heap location can be added while
preserving an existing value invariant. This Flapjack helper composes the
source's byte insertion and submap lemmas for `new_byte_alt_thm`. -/
theorem valueInv_freshByte_heap {width : Nat} [NeZero width] (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (ptr a : Nat) (flag : Bool) (bytes : List (BitVec 8))
    (f tf : HolFiniteMapExact Nat Nat) (heap heap1 : ValueHeap width)
    (value : Value) (address : HeapAddress (WordLocW width))
    (freshRef : sptLookup ptr refs = none) (freshMap : f.lookup ptr = none)
    (rel : heapStoreRel heap heap1) (valid : valueInv conf value refs (address, f, tf, heap)) :
    valueInv conf value (sptInsert ptr (.byteArray flag bytes) refs)
      (address, f.update (ptr, a), tf, heap1) := by
  have refSubmap : f.submap (f.update (ptr, a)) := by
    intro key target found
    by_cases same : key = ptr
    · subst key
      simp [freshMap] at found
    · simpa [HolFiniteMapExact.update, FUPDATE, same, Ne.symm same] using found
  have inserted := valueInv_insertByteArray conf value refs address f tf heap ptr flag bytes
    ⟨valid, by intro mem; simp [sptMem, sptDomain, freshRef] at mem⟩
  exact valueInv_submap conf (sptInsert ptr (.byteArray flag bytes) refs)
    f (f.update (ptr, a)) tf tf heap heap1 value address
    ⟨refSubmap, HolFiniteMapExact.submap_refl tf, rel, inserted⟩
/-- Existing reference-cell invariants survive a fresh byte-array insertion
and preservation of old heap cells. This supports HOL's `new_byte_alt_thm`. -/
theorem bcRefInv_freshByte_heap {width : Nat} [NeZero width] (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (ptr a n : Nat) (flag : Bool) (bytes : List (BitVec 8))
    (f tf : HolFiniteMapExact Nat Nat) (heap heap1 : ValueHeap width) (be : Bool)
    (freshRef : sptLookup ptr refs = none) (freshMap : f.lookup ptr = none)
    (different : n ≠ ptr) (rel : heapStoreRel heap heap1)
    (valid : bcRefInv conf n refs (f, tf, heap, be)) :
    bcRefInv conf n (sptInsert ptr (.byteArray flag bytes) refs)
      (f.update (ptr, a), tf, heap1, be) := by
  have fLookup : (f.update (ptr, a)).lookup n = f.lookup n := by
    simp [HolFiniteMapExact.update, FUPDATE, Ne.symm different]
  have refsLookup : sptLookup n (sptInsert ptr (.byteArray flag bytes) refs) = sptLookup n refs := by
    simp [sptLookup_sptInsert_ne ptr n _ refs different]
  have cells : ∀ index cell, isDataElement cell → heapLookup index heap = some cell → heapLookup index heap1 = some cell := by
    intro index cell data found
    obtain ⟨xs, len, d, rfl⟩ := data
    exact (rel index ⟨xs, len, d, found⟩).trans found
  have values : ∀ value address, valueInv conf value refs (address, f, tf, heap) →
      valueInv conf value (sptInsert ptr (.byteArray flag bytes) refs) (address, f.update (ptr, a), tf, heap1) := by
    intro value address inv
    exact valueInv_freshByte_heap conf refs ptr a flag bytes f tf heap heap1 value address freshRef freshMap rel inv
  cases mapFound : f.lookup n with
  | none => simp [bcRefInv, mapFound] at valid
  | some index =>
    cases refFound : sptLookup n refs with
    | none => simp [bcRefInv, mapFound, refFound] at valid
    | some cell =>
      cases cell with
      | valueArray items =>
        simp only [bcRefInv, fLookup, refsLookup, mapFound, refFound] at valid ⊢
        obtain ⟨addresses, found, related⟩ := valid
        exact ⟨addresses, cells index _ (by simp [isDataElement, refBlock]) found,
          related.imp (fun address value h => values value address h)⟩
      | byteArray oldFlag oldBytes =>
        simp only [bcRefInv, fLookup, refsLookup, mapFound, refFound] at valid ⊢
        exact cells index _ (by simp [isDataElement, bytesRep]) valid
      | thunk mode value =>
        simp only [bcRefInv, fLookup, refsLookup, mapFound, refFound] at valid ⊢
        obtain ⟨address, found, safe, related⟩ := valid
        refine ⟨address, cells index _ (by simp [isDataElement, thunkBlock]) found, ?_, values value address related⟩
        intro evaluated
        exact destThunk_notThunk_insertByteArray value refs ptr flag bytes (safe evaluated)
      | mutBlock tag finalised left value right =>
        simp only [bcRefInv, fLookup, refsLookup, mapFound, refFound] at valid ⊢
        obtain ⟨gc, noStamp, addresses, found, related⟩ := valid
        exact ⟨gc, noStamp, addresses, cells index _ (by simp [isDataElement, blockRep]) found,
          related.imp (fun address value h => values value address h)⟩
/-- Any reachable old reference remains reachable from the old stack after
adding a fresh byte-array reference. This is a proof helper for
HOL's `new_byte_alt_thm`. -/
theorem reachableRefs_freshByte_old (refs : Spt (BvlSem.Ref Value)) (stack : List Value)
    (ptr n : Nat) (bit flag : Bool) (bytes : List (BitVec 8))
    (fresh : sptLookup ptr refs = none) (different : n ≠ ptr)
    (reachable : reachableRefs (.refPtr bit ptr :: stack) (sptInsert ptr (.byteArray flag bytes) refs) n) :
    reachableRefs stack refs n := by
  rw [reachableRefs_safeInsertByteArray refs (.refPtr bit ptr :: stack) ptr flag bytes (Or.inl fresh)] at reachable
  obtain ⟨value, start, member, reference, path⟩ := reachable
  rcases List.mem_cons.mp member with same | inStack
  · subst value
    have startEq : start = ptr := by simpa [getRefs] using reference
    subst start
    rcases Relation.ReflTransGen.cases_head path with same | ⟨next, edge, _⟩
    · exact False.elim (different same.symm)
    · simp [refEdge, fresh] at edge
  · exact ⟨value, start, inStack, reference, path⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
