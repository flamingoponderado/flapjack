module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Full
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Store
public import Flapjack.FiniteMap.MapKeys
public import Flapjack.Compiler.Backend.WordGcFunctions.Roots

@[expose] public section

/-! Full copying collection under the heap/store invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.CopyingGc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- The heap/store invariant discharges the concrete collector's store
preconditions. This is Flapjack-specific composition of the original
invariant and collector assumptions. -/
theorem heapInMemoryStore_gcAssum {width : Nat} [NeZero width] (conf : Config)
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit : Nat) (gens : GcCombined.GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    wordGcFunAssum conf store := by
  rcases heapMem with ⟨heapBound, byteBound, shift, nonzero, lenBound, shiftBound, global,
    curr, other, currAligned, otherAligned, currLookup, otherLookup, next, trigger, endHeap, heapSize,
    ⟨globalWord, globalLookup, realLookup⟩, generations, separated⟩
  obtain ⟨genWord, genLookup⟩ := genStartsInStoreImp conf gens _ generations
  have getCurr := holFapply_of_lookup currLookup
  have getOther := holFapply_of_lookup otherLookup
  have getTrigger := holFapply_of_lookup trigger
  have getEnd := holFapply_of_lookup endHeap
  have getSize := holFapply_of_lookup heapSize
  have getGen := holFapply_of_lookup genLookup
  have getGlobal := holFapply_of_lookup globalLookup
  have lenBound1 : conf.lenSize + 2 < width := by omega
  refine ⟨?_, ?_⟩
  · intro name member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [globalLookup, currLookup, otherLookup, heapSize, trigger, genLookup, endHeap]
  · simp [getCurr, getOther, getTrigger, getEnd, getSize, getGen, getGlobal,
      wordSemIsWordLoc, good, nonzero, lenBound1, shiftBound]

/-- Flapjack-specific composition: the source heap/store invariant supplies
all memory and bound premises of full collection. This is an intermediate
step toward the store-level collector theorem, not a separate HOL declaration. -/
theorem fullGc_store_simulation {width : Nat} [NeZero width] (conf : Config)
    (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit a1 : Nat) (gens : GcCombined.GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (run : fullGc (roots, heap, limit) = (roots1, heap1, a1, true))
    (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ curr other : BitVec width, ∃ outMemory : BitVec width → WordLocW width,
      store.lookup .currHeap = some (.word curr) ∧ store.lookup .otherHeap = some (.word other) ∧
      wordFullGc conf (roots.map (wordAddr conf), other, curr, memory, domain) =
        (roots1.map (wordAddr conf), BitVec.ofNat width a1,
          other + wordSemBytesInWord * BitVec.ofNat width a1, outMemory, true) ∧
      SetSep.star (wordHeap other (heap1 ++ heapExpand (limit - a1)) conf)
        (wordHeap curr (heapExpand limit) conf)
        (SetSep.fun2Set (outMemory, fun address => domain address = true)) := by
  rcases heapMem with ⟨heapBound, byteBound, shift, nonzero, lenBound, shiftBound, global,
    curr, other, currAligned, otherAligned, currLookup, otherLookup, next, trigger, endHeap, heapSize,
    globReal, generations, separated⟩
  have byteBound1 : heapLength heap * (width / 8) < 2 ^ width :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) byteBound
  have lenBound1 : conf.lenSize + 2 < width := by omega
  have limitEq := (fullGc_imp roots roots1 heap heap1 limit a1 run).2
  generalize wordRun : wordFullGc conf (roots.map (wordAddr conf), other, curr, memory, domain) = output
  rcases output with ⟨outRoots, outA, outPa, outMemory, outOk⟩
  have sepFrame : SetSep.star (SetSep.star (wordHeap curr heap conf)
      (wordHeap other (heapExpand limit) conf)) SetSep.emp
      (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    simpa [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft] using separated
  obtain ⟨sepResult, okEq, aEq, rootsEq, paEq⟩ := wordFullGc_thm conf roots roots1 heap heap1 limit a1
    curr other memory outMemory domain SetSep.emp outRoots outA outPa outOk run heapBound byteBound1
    lenBound1 sepFrame limitEq good wordRun
  refine ⟨curr, other, outMemory, currLookup, otherLookup, ?_, ?_⟩
  · simpa [rootsEq, aEq, paEq, okEq] using wordRun
  · simpa [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft] using sepResult

/-- The Simple store-level collector executes the successful full collection
when its global root and output head are known. This Flapjack-specific lemma
connects the heap simulation to the actual collector and its store updates. -/
theorem simpleGc_store_execution {width : Nat} [NeZero width] (conf : Config)
    (root root1 : HeapAddress (WordLocW width)) (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit a1 : Nat) (gens : GcCombined.GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (run : fullGc (root :: roots, heap, limit) = (root1 :: roots1, heap1, a1, true))
    (kind : conf.gcKind = .simple)
    (global : store.lookup .globals = some (wordAddr conf root))
    (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ curr other : BitVec width, ∃ outMemory : BitVec width → WordLocW width,
      let pa := other + wordSemBytesInWord * BitVec.ofNat width a1
      let len := wordSemTheWord (holFapply store .heapLength)
      let g := wordAddr conf root1
      store.lookup .currHeap = some (.word curr) ∧ store.lookup .otherHeap = some (.word other) ∧
      wordGcFun conf (roots.map (wordAddr conf), memory, domain, store) =
        some (roots1.map (wordAddr conf), outMemory,
          store.updateListEq [(.currHeap, .word other), (.otherHeap, .word curr),
            (.nextFree, .word pa), (.triggerGC, .word (other + len)),
            (.endOfHeap, .word (other + len)), (.globals, g), (.globReal, globReal conf other g)]) ∧
      SetSep.star (wordHeap other (heap1 ++ heapExpand (limit - a1)) conf)
        (wordHeap curr (heapExpand limit) conf)
        (SetSep.fun2Set (outMemory, fun address => domain address = true)) := by
  obtain ⟨curr, other, outMemory, currLookup, otherLookup, concrete, separated⟩ :=
    fullGc_store_simulation conf (root :: roots) (root1 :: roots1) heap heap1 a sp sp1 limit a1 gens
      store memory domain run good heapMem
  refine ⟨curr, other, outMemory, currLookup, otherLookup, ?_, separated⟩
  have globalValue : holFapply store .globals = wordAddr conf root := holFapply_of_lookup global
  have currValue : holFapply store .currHeap = .word curr := holFapply_of_lookup currLookup
  have otherValue : holFapply store .otherHeap = .word other := holFapply_of_lookup otherLookup
  have assum := heapInMemoryStore_gcAssum conf heap a sp sp1 limit gens store memory domain good heapMem
  simp only [List.map_cons] at concrete
  simp [wordGcFun, kind, globalValue, currValue, otherValue, wordSemTheWord, concrete, holHd, assum]

/-- Reconstruct the heap/store invariant after the Simple collector swaps heap
spaces. This Flapjack-specific lemma factors the store update proof. -/
theorem simpleGc_store_reconstruct {width : Nat} [NeZero width] (conf : Config)
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit : Nat) (gens : GcCombined.GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory outMemory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (curr other g : BitVec width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit)
    (limitEq : limit = heapLength heap) (bound : heapLength heap1 ≤ limit)
    (currLookup : store.lookup .currHeap = some (.word curr))
    (otherLookup : store.lookup .otherHeap = some (.word other))
    (separated : SetSep.star (wordHeap other (heap1 ++ heapExpand (limit - heapLength heap1)) conf)
      (wordHeap curr (heapExpand limit) conf)
      (SetSep.fun2Set (outMemory, fun address => domain address = true))) :
    heapInMemoryStore (heap1 ++ heapExpand (limit - heapLength heap1)) (heapLength heap1)
      (limit - heapLength heap1) 0 gens conf
      (store.updateListEq [(.currHeap, .word other), (.otherHeap, .word curr),
        (.nextFree, .word (other + wordSemBytesInWord * BitVec.ofNat width (heapLength heap1))),
        (.triggerGC, .word (other + wordSemTheWord (holFapply store .heapLength))),
        (.endOfHeap, .word (other + wordSemTheWord (holFapply store .heapLength))),
        (.globals, .word g), (.globReal, globReal conf other (.word g))]) outMemory domain limit := by
  rcases heapMem with ⟨heapBound, byteBound, shift, nonzero, lenBound, shiftBound, global,
    oldCurr, oldOther, currAligned, otherAligned, oldCurrLookup, oldOtherLookup, next, trigger, endHeap, heapSize,
    globRealOld, generations, oldSeparated⟩
  have currEq : oldCurr = curr := by simpa [oldCurrLookup] using currLookup
  have otherEq : oldOther = other := by simpa [oldOtherLookup] using otherLookup
  subst oldCurr
  subst oldOther
  have sizeValue : holFapply store .heapLength = .word (StackRemove.bytesInWord width * BitVec.ofNat width limit) :=
    holFapply_of_lookup heapSize
  have expandedLength : heapLength (heap1 ++ heapExpand (limit - heapLength heap1)) = limit := by
    rw [heapLength_append]
    have expandLen (n : Nat) : heapLength (heapExpand n : List (HeapElement (WordLocW width)
        (HeapTag × List (WordLocW width)))) = n := by
      cases n <;> simp [heapExpand, heapLength, elLength]
    rw [expandLen]
    omega
  have allocSum : heapLength heap1 + (limit - heapLength heap1) = limit := by omega
  rw [heapInMemoryStore, expandedLength]
  refine ⟨by simpa [limitEq] using heapBound, by simpa [limitEq] using byteBound,
    shift, nonzero, lenBound, shiftBound, ?_, other, curr, otherAligned, currAligned, ?_⟩
  · simp [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL,
      sizeValue, wordSemTheWord, wordSemBytesInWord, StackRemove.bytesInWord, allocSum,
      heapSize, globRealInv, globReal, generations, separated]

/-- Full collection preserves the word shape of the global root. This
Flapjack-specific consequence combines the store invariant and root relation. -/
theorem fullGc_global_word {width : Nat} [NeZero width] (conf : Config)
    (root root1 : HeapAddress (WordLocW width)) (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit a1 : Nat) (gens : GcCombined.GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (run : fullGc (root :: roots, heap, limit) = (root1 :: roots1, heap1, a1, true))
    (global : store.lookup .globals = some (wordAddr conf root)) (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ g, wordAddr conf root1 = .word g := by
  have assum := heapInMemoryStore_gcAssum conf heap a sp sp1 limit gens store memory domain good heapMem
  have inputWord : wordSemIsWordLoc (wordAddr conf root) = true := by
    simpa [holFapply_of_lookup global] using assum.2.2.2.2.2.2.2.1
  obtain ⟨curr, other, outMemory, currLookup, otherLookup, concrete, separated⟩ :=
    fullGc_store_simulation conf (root :: roots) (root1 :: roots1) heap heap1 a sp sp1 limit a1 gens
      store memory domain run good heapMem
  have rel := wordGcMoveRoots_rootRel conf ((root :: roots).map (wordAddr conf)) 0 other curr memory domain
  rw [← wordFullGc_fst, concrete] at rel
  simp only [List.map_cons] at rel
  cases rel with
  | cons head tail =>
    have outputWord : wordSemIsWordLoc (wordAddr conf root1) = true := by simpa [inputWord] using head.1.symm
    cases value : wordAddr conf root1 with
    | word w => exact ⟨w, rfl⟩
    | loc l o => simp [value, wordSemIsWordLoc] at outputWord

/-- Compose the actual Simple collector execution with reconstruction of
the heap/store invariant, including the preserved global root. -/
theorem simpleGc_store_correct_word_global {width : Nat} [NeZero width] (conf : Config)
    (root root1 : HeapAddress (WordLocW width)) (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit : Nat) (gens : GcCombined.GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (run : fullGc (root :: roots, heap, limit) = (root1 :: roots1, heap1, heapLength heap1, true))
    (kind : conf.gcKind = .simple) (global : store.lookup .globals = some (wordAddr conf root))
    (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ outMemory outStore,
      wordGcFun conf (roots.map (wordAddr conf), memory, domain, store) =
        some (roots1.map (wordAddr conf), outMemory, outStore) ∧
      heapInMemoryStore (heap1 ++ heapExpand (limit - heapLength heap1)) (heapLength heap1)
        (limit - heapLength heap1) 0 gens conf outStore outMemory domain limit ∧
      outStore.lookup .globals = some (wordAddr conf root1) := by
  obtain ⟨g, globalEq⟩ := fullGc_global_word conf root root1 roots roots1 heap heap1 a sp sp1 limit
    (heapLength heap1) gens store memory domain run global good heapMem
  obtain ⟨curr, other, outMemory, currLookup, otherLookup, concrete, separated⟩ :=
    simpleGc_store_execution conf root root1 roots roots1 heap heap1 a sp sp1 limit (heapLength heap1)
      gens store memory domain run kind global good heapMem
  have inv := simpleGc_store_reconstruct conf heap heap1 a sp sp1 limit gens store memory outMemory domain
    curr other g heapMem (fullGc_imp _ _ _ _ _ _ run).2 (fullGc_imp _ _ _ _ _ _ run).1
    currLookup otherLookup separated
  refine ⟨outMemory, _, ?_, inv, ?_⟩
  · simpa [globalEq] using concrete
  · simp [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL, globalEq]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
