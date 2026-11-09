module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdateValueHeap

@[expose] public section

/-! Reference-cell invariants across byte-array updates. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Any distinct mapped reference points outside the updated byte cell. -/
theorem byteUpdate_mappedAddress_ne {width : Nat} [NeZero width]
    (f : HolFiniteMapExact Nat Nat) (pre : ValueHeap width) (oldHeap : ValueHeap width)
    (ptr n mapped : Nat) (ptrMap : f.lookup ptr = some (heapLength pre))
    (nMap : f.lookup n = some mapped)
    (injective : mapInjInto f (fun index => isSomeDataElement (heapLookup index oldHeap)))
    (different : n ≠ ptr) : mapped ≠ heapLength pre := by
  intro equal
  apply different
  apply injective.2 n ptr ⟨⟨mapped, nMap⟩, ⟨heapLength pre, ptrMap⟩⟩
  rw [holFapply_of_lookup nMap, holFapply_of_lookup ptrMap, equal]

/-- The changed byte array has the corresponding new reference invariant
when its length and the allocated word count are preserved. -/
theorem bcRefInv_byteUpdate_here {width : Nat} [NeZero width] (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (f tf : HolFiniteMapExact Nat Nat)
    (pre post : ValueHeap width) (be flag : Bool) (before after : List (BitVec 8))
    (ptr : Nat) (sameLength : before.length = after.length)
    (ptrMap : f.lookup ptr = some (heapLength pre)) :
    let words := List.replicate (before.length / (width / 8) + 1) (0 : BitVec width)
    bcRefInv conf ptr (sptInsert ptr (.byteArray flag after) refs)
      (f, tf, pre ++ [bytesRep be flag after words] ++ post, be) := by
  simp only [bcRefInv, ptrMap, sptLookup_sptInsert_same]
  rw [← sameLength]
  exact heapLookup_byteHeap_here pre post be flag after _

/-- A reference other than the updated array retains its reference invariant.
The finite map's injectivity is needed to exclude aliasing the replaced cell. -/
theorem bcRefInv_byteUpdate_other {width : Nat} [NeZero width] (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (f tf : HolFiniteMapExact Nat Nat)
    (pre post : ValueHeap width) (be flag : Bool) (before after : List (BitVec 8))
    (words : List (BitVec width)) (ptr n : Nat)
    (found : sptLookup ptr refs = some (.byteArray flag before))
    (ptrMap : f.lookup ptr = some (heapLength pre))
    (injective : mapInjInto f
      (fun index => isSomeDataElement (heapLookup index (pre ++ [bytesRep be flag before words] ++ post))))
    (different : n ≠ ptr)
    (valid : bcRefInv conf n refs (f, tf, pre ++ [bytesRep be flag before words] ++ post, be)) :
    bcRefInv conf n (sptInsert ptr (.byteArray flag after) refs)
      (f, tf, pre ++ [bytesRep be flag after words] ++ post, be) := by
  have lookupRefs : sptLookup n (sptInsert ptr (.byteArray flag after) refs) = sptLookup n refs :=
    sptLookup_sptInsert_ne ptr n _ refs different
  cases fLookup : f.lookup n with
  | none => simp [bcRefInv, fLookup] at valid
  | some mapped =>
    have addressNe := byteUpdate_mappedAddress_ne f pre _ ptr n mapped ptrMap fLookup injective different
    have unchanged : heapLookup mapped (pre ++ [bytesRep be flag before words] ++ post) =
        heapLookup mapped (pre ++ [bytesRep be flag after words] ++ post) :=
      heapLookup_replace_ne pre post _ _ (bytesRep_shape be flag before after words).length mapped addressNe
    cases refLookup : sptLookup n refs with
    | none => simp [bcRefInv, fLookup, refLookup] at valid
    | some cell =>
      cases cell with
      | valueArray values =>
        simp only [bcRefInv, fLookup, refLookup] at valid
        simp only [bcRefInv, fLookup, lookupRefs, refLookup]
        obtain ⟨addresses, cell, valuesInv⟩ := valid
        refine ⟨addresses, unchanged ▸ cell, ?_⟩
        apply valuesInv.imp
        intro address value h
        exact valueInv_byteUpdate conf value refs address f tf pre post be flag before after words ptr flag before found h
      | byteArray compare bytes =>
        simp only [bcRefInv, fLookup, refLookup] at valid
        simp only [bcRefInv, fLookup, lookupRefs, refLookup]
        exact unchanged ▸ valid
      | thunk mode value =>
        simp only [bcRefInv, fLookup, refLookup] at valid
        simp only [bcRefInv, fLookup, lookupRefs, refLookup]
        obtain ⟨address, cell, safe, valueInv⟩ := valid
        refine ⟨address, unchanged ▸ cell, ?_, ?_⟩
        · intro evaluated
          exact destThunk_notThunk_insertByteArray value refs ptr flag after (safe evaluated)
        · exact valueInv_byteUpdate conf value refs address f tf pre post be flag before after words ptr flag before found valueInv
      | mutBlock tag finalised left value right =>
        simp only [bcRefInv, fLookup, refLookup] at valid
        simp only [bcRefInv, fLookup, lookupRefs, refLookup]
        obtain ⟨gen, fresh, addresses, cell, valuesInv⟩ := valid
        refine ⟨gen, fresh, addresses, unchanged ▸ cell, ?_⟩
        apply valuesInv.imp
        intro address item h
        exact valueInv_byteUpdate conf item refs address f tf pre post be flag before after words ptr flag before found h

/-- Every reference-cell invariant survives updating the array and its heap
representation. The updated cell and all other references are handled together. -/
theorem bcRefInv_byteUpdate {width : Nat} [NeZero width] (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (f tf : HolFiniteMapExact Nat Nat)
    (pre post : ValueHeap width) (be flag : Bool) (before after : List (BitVec 8))
    (ptr n : Nat) (sameLength : before.length = after.length)
    (found : sptLookup ptr refs = some (.byteArray flag before))
    (ptrMap : f.lookup ptr = some (heapLength pre))
    (injective : mapInjInto f (fun index => isSomeDataElement
      (heapLookup index (pre ++ [bytesRep be flag before
        (List.replicate (before.length / (width / 8) + 1) 0)] ++ post))))
    (valid : bcRefInv conf n refs (f, tf, pre ++ [bytesRep be flag before
      (List.replicate (before.length / (width / 8) + 1) 0)] ++ post, be)) :
    bcRefInv conf n (sptInsert ptr (.byteArray flag after) refs)
      (f, tf, pre ++ [bytesRep be flag after
        (List.replicate (before.length / (width / 8) + 1) 0)] ++ post, be) := by
  by_cases same : n = ptr
  · subst n
    exact bcRefInv_byteUpdate_here conf refs f tf pre post be flag before after ptr sameLength ptrMap
  · exact bcRefInv_byteUpdate_other conf refs f tf pre post be flag before after _ ptr n
      found ptrMap injective same valid

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
