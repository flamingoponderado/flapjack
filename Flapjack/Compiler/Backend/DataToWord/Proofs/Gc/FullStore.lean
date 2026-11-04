import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Full
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Store

/-! Full copying collection under the heap/store invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.CopyingGc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

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
    (kind : conf.gcKind = .simple) (assum : wordGcFunAssum conf store)
    (global : store.lookup .globals = some (wordAddr conf root))
    (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ curr other : BitVec width, ∃ outMemory : BitVec width → WordLocW width,
      let pa := other + wordSemBytesInWord * BitVec.ofNat width a1
      let len := wordSemTheWord (holFapply store .heapLength)
      let g := wordAddr conf root1
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
  refine ⟨curr, other, outMemory, ?_, separated⟩
  have globalValue : holFapply store .globals = wordAddr conf root := holFapply_of_lookup global
  have currValue : holFapply store .currHeap = .word curr := holFapply_of_lookup currLookup
  have otherValue : holFapply store .otherHeap = .word other := holFapply_of_lookup otherLookup
  simp only [List.map_cons] at concrete
  simp [wordGcFun, kind, globalValue, currValue, otherValue, wordSemTheWord, concrete, holHd, assum]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
