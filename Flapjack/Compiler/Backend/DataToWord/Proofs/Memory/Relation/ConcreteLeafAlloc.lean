module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ConsMemory
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Store an already-represented leaf cell into unused heap space and retain
the full concrete heap-store invariant. This helper shares the concrete
allocation bookkeeping of the Word64 and bignum HOL proofs. -/
theorem heapInMemoryStore_allocateLeaf {width : Nat} [NeZero width]
    (c : DataToWord.Config) (heap heap2 : ValueHeap width) (a sp0 sp1 : Nat) (gens : GenState)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) (limit : Nat)
    (tag : HeapTag) (payload : List (WordLocW width)) (hd : BitVec width)
    (unused : unusedSpaceInv a (sp0 + sp1) heap) (fits : payload.length + 1 ≤ sp0)
    (stored : heapStoreUnusedAlt a (sp0 + sp1) (.dataElement [] payload.length (tag, payload)) heap = (heap2, true))
    (cell : ∀ (addr : BitVec width), wordEl addr (.dataElement [] payload.length (tag, payload)) c = Misc.wordList addr (.word hd :: payload))
    (heapMem : heapInMemoryStore heap a sp0 sp1 gens c st m dm limit) :
    ∃ free curr m1, st.lookup .nextFree = some (.word free) ∧ st.lookup .currHeap = some (.word curr) ∧
      free = curr + StackRemove.bytesInWord width * BitVec.ofNat width a ∧
      storeList free (.word hd :: payload) m dm = some m1 ∧
      heapInMemoryStore heap2 (a + (payload.length + 1)) (sp0 - (payload.length + 1)) sp1 gens c
        (st.update (.nextFree, .word (free + wordSemBytesInWord * BitVec.ofNat width (payload.length + 1)))) m1 dm limit := by
  have positive : sp0 + sp1 ≠ 0 := by omega
  have found := unused.1 positive
  obtain ⟨pre, post, heapShape, aEq⟩ := heapLookup_split heap a _ found
  have expand : (heapExpand (sp0 + sp1) : ValueHeap width) = [.unused (sp0 + sp1 - 1)] := by
    unfold heapExpand
    rw [if_neg positive]
  have heapOld : heap = pre ++ heapExpand (sp0 + sp1) ++ post := by
    simpa [expand, List.append_assoc] using heapShape
  have heap2Shape : heap2 = pre ++ [.dataElement [] payload.length (tag, payload)] ++ heapExpand (sp0 + sp1 - (payload.length + 1)) ++ post := by
    have store := stored
    classical
    simp only [heapStoreUnusedAlt, found, show elLength (.dataElement [] payload.length (tag, payload) : HeapElement (WordLocW width) (HeapTag × List (WordLocW width))) ≤ sp0 + sp1 by simp [elLength]; omega,
      and_self, ↓reduceIte] at store
    rw [heapShape, aEq, heapStore_atPrefix] at store
    have h := congrArg Prod.fst store
    simpa [elLength, List.append_assoc] using h.symm
  obtain ⟨heapBound, byteBound, shiftBound, lenPos, lenBound, shiftWidth, globals, curr, other,
    currAligned, otherAligned, currLookup, otherLookup, freeLookup, triggerLookup, endLookup,
    heapLenLookup, globInv, genInv, heapSep⟩ := heapMem
  have heapSepOld : SetSep.star (wordHeap curr (pre ++ heapExpand (sp0 + sp1) ++ post) c)
      (wordHeap other (heapExpand limit) c) (SetSep.fun2Set (m, fun x => dm x = true)) := by
    simpa [heapOld] using heapSep
  obtain ⟨m1, run, heapSepNew⟩ := wordHeapAlloc c curr pre post (sp0 + sp1)
    (.dataElement [] payload.length (tag, payload)) payload hd (wordHeap other (heapExpand limit) c) m dm
    (by omega) (by simp [elLength]) (cell _) heapSepOld
  have nLen : heapLength heap2 = heapLength heap :=
    heapStoreUnusedAlt_imp_length a (sp0 + sp1) (.dataElement [] payload.length (tag, payload)) heap heap2 stored
  let free := curr + StackRemove.bytesInWord width * BitVec.ofNat width a
  let newFree := free + wordSemBytesInWord * BitVec.ofNat width (payload.length + 1)
  let st1 := st.update (.nextFree, .word newFree)
  have nstore : st1.lookup .nextFree = some (.word newFree) := by
    simp [st1, HolFiniteMapExact.update, FUPDATE]
  have shapeSep : SetSep.star (wordHeap curr heap2 c) (wordHeap other (heapExpand limit) c)
      (SetSep.fun2Set (m1, fun x => dm x = true)) := by simpa [heap2Shape] using heapSepNew
  have addSub : a + (payload.length + 1) + (sp0 - (payload.length + 1)) = a + sp0 := by omega
  have addSub1 : a + (payload.length + 1) + (sp0 - (payload.length + 1)) + sp1 = a + sp0 + sp1 := by omega
  have nfreeEq : newFree = curr + StackRemove.bytesInWord width * BitVec.ofNat width (a + (payload.length + 1)) := by
    simp only [newFree, free, wordSemBytesInWord, StackRemove.bytesInWord, BitVec.ofNat_add, BitVec.mul_add]
    rw [BitVec.add_assoc]
  have heapMem1 : heapInMemoryStore heap2 (a + (payload.length + 1)) (sp0 - (payload.length + 1)) sp1 gens c st1 m1 dm limit := by
    refine ⟨by simpa [nLen] using heapBound, by simpa [nLen] using byteBound, shiftBound, lenPos, lenBound, shiftWidth, ?_, curr, other,
      currAligned, otherAligned, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, shapeSep⟩
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using globals
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using currLookup
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using otherLookup
    · simpa [nfreeEq] using nstore
    · simpa [st1, HolFiniteMapExact.update, FUPDATE, addSub] using triggerLookup
    · simpa [st1, HolFiniteMapExact.update, FUPDATE, addSub1] using endLookup
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using heapLenLookup
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using globInv
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using genInv
  refine ⟨free, curr, m1, ?_, currLookup, rfl, ?_, ?_⟩
  · simpa [free] using freeLookup
  · simpa [free, aEq] using run
  · exact heapMem1
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
