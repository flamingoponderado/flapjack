import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.FullStore

/-! No-collection case of the combined GC simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Flapjack-specific store-level form of the no-collection case: the
concrete collector resets the allocation boundaries without changing memory. -/
theorem noneGc_store_correct {width : Nat} [NeZero width] (conf : Config)
    (roots : List (WordLocW width))
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit : Nat) (gens : GcCombined.GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (kind : conf.gcKind = .none) (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ outStore : HolFiniteMapExact WordStoreHOL (WordLocW width),
      wordGcFun conf (roots, memory, domain, store) = some (roots, memory, outStore) ∧
      heapInMemoryStore heap 0 0 0 gens conf outStore memory domain limit ∧
      outStore.lookup .globals = store.lookup .globals := by
  have assum := heapInMemoryStore_gcAssum conf heap a sp sp1 limit gens store memory domain good heapMem
  rcases heapMem with ⟨heapBound, byteBound, shift, nonzero, lenBound, shiftBound, global,
    curr, other, currAligned, otherAligned, currLookup, otherLookup, next, trigger, endHeap, heapSize,
    globReal, generations, separated⟩
  have currValue : holFapply store .currHeap = .word curr := holFapply_of_lookup currLookup
  let outStore := store.updateListEq [(.nextFree, .word curr), (.triggerGC, .word curr), (.endOfHeap, .word curr)]
  refine ⟨outStore, ?_, ?_, ?_⟩
  · simp [wordGcFun, kind, assum, currValue, wordSemTheWord, outStore]
  · refine ⟨heapBound, byteBound, shift, nonzero, lenBound, shiftBound, ?_, curr, other,
      currAligned, otherAligned, ?_⟩
    · simpa [outStore, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL] using global
    · simp [outStore, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL,
        StackRemove.bytesInWord, currLookup, otherLookup, heapSize,
        globReal, generations, separated]
  · simp [outStore, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
