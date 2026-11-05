import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CombinedGenerational
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.FullStore
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.GcConfig
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.DoPartial

/-! Generational collectors under the heap/store invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.Compiler.Backend.GcCombined

/-- A selectable partial collection has a nonempty abstract generation list,
and the stored generation-start word represents its first boundary. -/
theorem partialGenStart_store {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width))) (gens : GenState) (refsStart : Nat)
    (limits : List Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (kind : conf.gcKind = .generational limits) (selected : wordGenGcCanDoPartial limits store)
    (related : genStartsInStore conf gens (store.lookup .genStart)) :
    ∃ start tail count,
      gens = .genState count (start :: tail) ∧
      (makePartialConf genConf gens refsStart).genStart = start ∧
      store.lookup .genStart = some (.word (wordSemBytesInWord * BitVec.ofNat width start)) := by
  obtain ⟨word, lookup⟩ := genStartsInStoreImp conf gens _ related
  cases gens with
  | genState count starts =>
    have shape := related
    simp only [lookup, genStartsInStore] at shape
    have lengths := (shape limits kind).1
    have nonempty : limits ≠ [] := selected.1
    cases starts with
    | nil =>
      cases limits with
      | nil => exact False.elim (nonempty rfl)
      | cons head tail => simp at lengths
    | cons start tail =>
      have wordEq := (shape limits kind).2 start tail rfl
      refine ⟨start, tail, count, rfl, ?_, ?_⟩
      · simp [makePartialConf, holHd]
      · simpa only [wordEq, wordSemBytesInWord, StackRemove.bytesInWord] using lookup

/-- The store invariant supplies the memory and machine-word premises for a
successful combined partial collection. -/
theorem combinedPartial_store_simulation {width : Nat} [NeZero width] (conf : Config)
    (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit a1 n1 : Nat) (gens gens1 : GenState) (limits : List Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (run : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits) (roots, heap, gens, a + sp + sp1, true) =
      (roots1, heap1, a1, n1, gens1, true))
    (kind : conf.gcKind = .generational limits) (selected : wordGenGcCanDoPartial limits store)
    (limitEq : limit = heapLength heap) (ending : endsWithRefs (a + sp + sp1) heap)
    (ordered : (makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).genStart ≤ a + sp + sp1)
    (refBound : a + sp + sp1 ≤ heapLength heap) (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ curr other : BitVec width, ∃ outMemory : BitVec width → WordLocW width,
      ∃ state : GcState (WordLocW width) (HeapTag × List (WordLocW width)),
      ∃ current1 refs1,
      store.lookup .currHeap = some (.word curr) ∧ store.lookup .otherHeap = some (.word other) ∧
      store.lookup .genStart = some (.word (wordSemBytesInWord * BitVec.ofNat width
        (makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).genStart)) ∧
      GenGcPartial.partialGc (makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)) (roots, heap) = (roots1, state) ∧
      heap1 = state.old ++ state.h1 ++ heapExpand state.n ++ state.r1 ∧ a1 = state.a ∧ n1 = state.n ∧
      gens1 = .genState 0 (limits.map fun _ => state.a) ∧
      wordGenGcPartialFull conf (roots.map (wordAddr conf), curr, other,
        wordSemBytesInWord * BitVec.ofNat width limit, memory, domain,
        wordSemBytesInWord * BitVec.ofNat width (makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).genStart,
        wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1)) =
        (roots1.map (wordAddr conf), BitVec.ofNat width a1,
         curr + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.old ++ state.h1)), outMemory, true) ∧
      SetSep.star (wordHeap curr heap1 conf) (wordHeap other (heapExpand limit) conf)
        (SetSep.fun2Set (outMemory, fun address => domain address = true)) ∧
      state.h2 = [] ∧ state.r4 = [] ∧ state.r3 = [] ∧ state.r2 = [] ∧
      heapLength state.heap = heapLength heap ∧
      heapSegment ((makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).genStart, a + sp + sp1) state.heap =
        some (state.old, current1, refs1) ∧ partialLenInv state ∧
      state.r1.all (isRefElement (makeGcConf (α := List (WordLocW width)) limit).isRef) = true := by
  classical
  rcases heapMem with ⟨heapBound, byteBound, shift, nonzero, lenBound, shiftBound, global,
    curr, other, currAligned, otherAligned, currLookup, otherLookup, next, trigger, endHeap, heapSize,
    globReal, generations, separated⟩
  obtain ⟨start, tail, count, gensEq, startEq, startLookup⟩ :=
    partialGenStart_store conf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1) limits store kind selected generations
  have storedStart : store.lookup .genStart = some (.word (wordSemBytesInWord * BitVec.ofNat width
      (makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).genStart)) := by simpa [startEq] using startLookup
  have byteBound1 : heapLength heap * (width / 8) < 2 ^ width :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) byteBound
  have dataBound : conf.lenSize + 2 < width := by omega
  have refClass : ∀ (t : HeapTag) (r : List (WordLocW width)), (makeGcConf (α := List (WordLocW width)) limit).isRef (t, r) = true ↔ isMutTag t := by
    intro t r
    simp [makeGcConf]
  have sepFrame : SetSep.star (SetSep.star (wordHeap curr heap conf)
      (Misc.wordListExists other (heapLength heap))) SetSep.emp
      (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    rw [wordHeap_heapExpand, limitEq] at separated
    simpa [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft] using separated
  generalize wordRun : wordGenGcPartialFull conf (roots.map (wordAddr conf), curr, other,
      wordSemBytesInWord * BitVec.ofNat width (heapLength heap), memory, domain,
      wordSemBytesInWord * BitVec.ofNat width (makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).genStart,
      wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1)) = result
  obtain ⟨wordRoots, wordI, wordPa, outMemory, wordOk⟩ := result
  obtain ⟨state, current1, refs1, abstractRun, heapEq, allocEq, freeEq, gensOut, output,
    h2Empty, r4Empty, r3Empty, r2Empty, rootsEq, heapLen, segment, okEq, indexEq, paEq, inv, refsOk⟩ :=
    combinedPartial_heap_correct conf (makeGcConf (α := List (WordLocW width)) limit) gens gens1 limits (a + sp + sp1) roots roots1 heap heap1 a1 n1
      memory outMemory domain curr other wordPa wordI SetSep.emp wordRoots wordOk run heapBound byteBound1 ending
      limitEq ordered refBound dataBound refClass wordRun sepFrame good
  refine ⟨curr, other, outMemory, state, current1, refs1, currLookup, otherLookup, storedStart, abstractRun,
    heapEq, allocEq, freeEq, gensOut, ?_, ?_, h2Empty, r4Empty, r3Empty, r2Empty, heapLen, segment, inv, refsOk⟩
  · simpa [limitEq, rootsEq, indexEq, paEq, okEq] using wordRun
  · simpa [limitEq, SetSep.starComm, StackRemove.StackHeap.starEmptyLeft] using output

/-- The input store invariant discharges the memory and dimensional
preconditions of the combined major collector's heap simulation. -/
theorem combinedMajor_store_simulation {width : Nat} [NeZero width] (conf : Config)
    (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit a1 n1 : Nat) (gens gens1 : GenState) (limits : List Nat) (refsStart : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (run : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits) (roots, heap, gens, refsStart, false) =
      (roots1, heap1, a1, n1, gens1, true))
    (limitEq : limit = heapLength heap) (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ curr other : BitVec width, ∃ outMemory : BitVec width → WordLocW width,
      ∃ state : GcState (WordLocW width) (HeapTag × List (WordLocW width)),
      store.lookup .currHeap = some (.word curr) ∧ store.lookup .otherHeap = some (.word other) ∧
      GenGc.genGc (makeGcConf (α := List (WordLocW width)) limit) (roots, heap) = (roots1, state) ∧
      heap1 = state.h1 ++ heapExpand state.n ++ state.r1 ∧ a1 = state.a ∧ n1 = state.n ∧
      gens1 = .genState 0 (limits.map fun _ => state.a) ∧
      wordGenGc conf (roots.map (wordAddr conf), curr, other,
        wordSemBytesInWord * BitVec.ofNat width limit, memory, domain) =
        (roots1.map (wordAddr conf), BitVec.ofNat width a1,
         other + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1),
         BitVec.ofNat width (a1 + n1),
         other + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1 + state.n), outMemory, true) ∧
      SetSep.star (wordHeap other heap1 conf) (wordHeap curr (heapExpand limit) conf)
        (SetSep.fun2Set (outMemory, fun address => domain address = true)) ∧
      state.h2 = [] ∧ state.r4 = [] ∧ state.r3 = [] ∧ state.r2 = [] ∧
      heapLength state.heap = heapLength heap ∧ genLenInv state ∧
      state.r1.all (isRefElement (makeGcConf (α := List (WordLocW width)) limit).isRef) = true := by
  classical
  rcases heapMem with ⟨heapBound, byteBound, shift, nonzero, lenBound, shiftBound, global,
    curr, other, currAligned, otherAligned, currLookup, otherLookup, next, trigger, endHeap, heapSize,
    globReal, generations, separated⟩
  have byteBound1 : heapLength heap * (width / 8) < 2 ^ width :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) byteBound
  have dataBound : conf.lenSize + 2 < width := by omega
  have lenBound1 : conf.lenSize + 5 ≤ width := by omega
  have refClass : ∀ (t : HeapTag) (r : List (WordLocW width)), (makeGcConf (α := List (WordLocW width)) limit).isRef (t, r) = true ↔ isMutTag t := by
    intro t r
    simp [makeGcConf]
  have sepFrame : SetSep.star (SetSep.star (wordHeap curr heap conf)
      (Misc.wordListExists other (heapLength heap))) SetSep.emp
      (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    rw [wordHeap_heapExpand, limitEq] at separated
    simpa [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft] using separated
  generalize wordRun : wordGenGc conf (roots.map (wordAddr conf), curr, other,
      wordSemBytesInWord * BitVec.ofNat width (heapLength heap), memory, domain) = result
  obtain ⟨wordRoots, wordI, wordPa, wordIb, wordPb, outMemory, wordOk⟩ := result
  obtain ⟨state, abstractRun, heapEq, allocEq, freeEq, gensEq, output, h2Empty, r4Empty, r3Empty, r2Empty,
    rootsEq, originalLen, okEq, indexEq, ibEq, paEq, pbEq, inv, refsOk⟩ :=
    combinedMajor_heap_correct conf (makeGcConf (α := List (WordLocW width)) limit) gens gens1 limits refsStart roots roots1 heap heap1 a1 n1
      memory outMemory domain curr other wordPb wordPa wordIb wordI SetSep.emp wordRoots wordOk run heapBound byteBound1
      dataBound refClass lenBound1 good wordRun sepFrame
  refine ⟨curr, other, outMemory, state, currLookup, otherLookup, abstractRun, heapEq, allocEq, freeEq, gensEq,
    ?_, ?_, h2Empty, r4Empty, r3Empty, r2Empty, originalLen, inv, refsOk⟩
  · simpa [limitEq, rootsEq, indexEq, ibEq, paEq, pbEq, okEq] using wordRun
  · simpa [limitEq, SetSep.starComm, StackRemove.StackHeap.starEmptyLeft] using output

/-- Execute the major generational branch of the concrete collector using
the combined collector's successful run and the input store invariant. -/
theorem combinedMajor_store_execution {width : Nat} [NeZero width] (conf : Config)
    (root root1 : HeapAddress (WordLocW width)) (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit a1 n1 : Nat) (gens gens1 : GenState) (limits : List Nat) (refsStart : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (run : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits) (root :: roots, heap, gens, refsStart, false) =
      (root1 :: roots1, heap1, a1, n1, gens1, true))
    (kind : conf.gcKind = .generational limits) (full : ¬ wordGenGcCanDoPartial limits store)
    (global : store.lookup .globals = some (wordAddr conf root))
    (limitEq : limit = heapLength heap) (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ curr other : BitVec width, ∃ outMemory : BitVec width → WordLocW width,
      ∃ state : GcState (WordLocW width) (HeapTag × List (WordLocW width)),
      let pa := other + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)
      let pb := other + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1 + state.n)
      let g := wordAddr conf root1
      let alloc := wordSemTheWord (holFapply store .allocSize)
      store.lookup .currHeap = some (.word curr) ∧ store.lookup .otherHeap = some (.word other) ∧
      GenGc.genGc (makeGcConf (α := List (WordLocW width)) limit) (root :: roots, heap) = (root1 :: roots1, state) ∧
      heap1 = state.h1 ++ heapExpand state.n ++ state.r1 ∧ a1 = state.a ∧ n1 = state.n ∧
      gens1 = .genState 0 (limits.map fun _ => state.a) ∧
      wordGcFun conf (roots.map (wordAddr conf), memory, domain, store) =
        some (roots1.map (wordAddr conf), outMemory,
          store.updateListEq [(.currHeap, .word other), (.otherHeap, .word curr),
            (.nextFree, .word pa), (.genStart, .word (pa - other)),
            (.triggerGC, .word (pa + newTrig (pb - pa) alloc limits)), (.endOfHeap, .word pb),
            (.globals, g), (.globReal, globReal conf other g),
            (.temp 0, .word 0), (.temp 1, .word 0), (.temp 2, .word 0), (.temp 3, .word 0),
            (.temp 4, .word 0), (.temp 5, .word 0), (.temp 6, .word 0)]) ∧
      SetSep.star (wordHeap other heap1 conf) (wordHeap curr (heapExpand limit) conf)
        (SetSep.fun2Set (outMemory, fun address => domain address = true)) ∧
      state.h2 = [] ∧ state.r4 = [] ∧ state.r3 = [] ∧ state.r2 = [] ∧
      heapLength state.heap = heapLength heap ∧ genLenInv state ∧
      state.r1.all (isRefElement (makeGcConf (α := List (WordLocW width)) limit).isRef) = true := by
  classical
  obtain ⟨curr, other, outMemory, state, currLookup, otherLookup, abstractRun, heapEq, allocEq, freeEq, gensEq,
    concrete, separated, h2Empty, r4Empty, r3Empty, r2Empty, heapLen, inv, refsOk⟩ :=
    combinedMajor_store_simulation conf (root :: roots) (root1 :: roots1) heap heap1 a sp sp1 limit a1 n1
      gens gens1 limits refsStart store memory domain run limitEq good heapMem
  refine ⟨curr, other, outMemory, state, currLookup, otherLookup, abstractRun, heapEq, allocEq, freeEq, gensEq,
    ?_, separated, h2Empty, r4Empty, r3Empty, r2Empty, heapLen, inv, refsOk⟩
  have globalValue : holFapply store .globals = wordAddr conf root := holFapply_of_lookup global
  have currValue : holFapply store .currHeap = .word curr := holFapply_of_lookup currLookup
  have otherValue : holFapply store .otherHeap = .word other := holFapply_of_lookup otherLookup
  have assum := heapInMemoryStore_gcAssum conf heap a sp sp1 limit gens store memory domain good heapMem
  have sizeValue : holFapply store .heapLength = .word (wordSemBytesInWord * BitVec.ofNat width limit) := by
    rcases heapMem with ⟨_, _, _, _, _, _, _, oldCurr, oldOther, _, _, oldCurrLookup, oldOtherLookup,
      _, _, _, heapSize, _⟩
    exact holFapply_of_lookup heapSize
  simp only [List.map_cons] at concrete
  simp [wordGcFun, kind, full, globalValue, currValue, otherValue, sizeValue, wordSemTheWord, concrete, holHd, assum]

/-- Execute the concrete partial branch once its allocation-space check is
known to hold. Deriving that check from the source invariant remains part of
the enclosing store-correctness proof. -/
theorem combinedPartial_store_execution {width : Nat} [NeZero width] (conf : Config)
    (root root1 : HeapAddress (WordLocW width)) (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit a1 n1 : Nat) (gens gens1 : GenState) (limits : List Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (run : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits)
      (root :: roots, heap, gens, a + sp + sp1, true) = (root1 :: roots1, heap1, a1, n1, gens1, true))
    (kind : conf.gcKind = .generational limits) (selected : wordGenGcCanDoPartial limits store)
    (global : store.lookup .globals = some (wordAddr conf root))
    (limitEq : limit = heapLength heap) (ending : endsWithRefs (a + sp + sp1) heap)
    (ordered : (makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).genStart ≤ a + sp + sp1)
    (refBound : a + sp + sp1 ≤ heapLength heap) (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit)
    (enough : ∀ (curr : BitVec width) (state : GcState (WordLocW width) (HeapTag × List (WordLocW width))),
      store.lookup .currHeap = some (.word curr) →
      GenGcPartial.partialGc (makePartialConf (makeGcConf limit) gens (a + sp + sp1)) (root :: roots, heap) = (root1 :: roots1, state) →
      let endh := curr + wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1)
      let pa := curr + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.old ++ state.h1))
      let alloc := wordSemTheWord (holFapply store .allocSize)
      alloc ≤ endh - pa ∧ alloc ≤ newTrig (endh - pa) alloc limits) :
    ∃ curr other : BitVec width, ∃ outMemory : BitVec width → WordLocW width,
      ∃ state : GcState (WordLocW width) (HeapTag × List (WordLocW width)),
      let pa := curr + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.old ++ state.h1))
      let endh := curr + wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1)
      let alloc := wordSemTheWord (holFapply store .allocSize)
      let g := wordAddr conf root1
      store.lookup .currHeap = some (.word curr) ∧ store.lookup .otherHeap = some (.word other) ∧
      GenGcPartial.partialGc (makePartialConf (makeGcConf limit) gens (a + sp + sp1)) (root :: roots, heap) =
        (root1 :: roots1, state) ∧
      heap1 = state.old ++ state.h1 ++ heapExpand state.n ++ state.r1 ∧ a1 = state.a ∧ n1 = state.n ∧
      gens1 = .genState 0 (limits.map fun _ => state.a) ∧
      wordGcFun conf (roots.map (wordAddr conf), memory, domain, store) =
        some (roots1.map (wordAddr conf), outMemory,
          store.updateListEq [(.currHeap, .word curr), (.otherHeap, .word other),
            (.nextFree, .word pa), (.genStart, .word (pa - curr)),
            (.triggerGC, .word (pa + newTrig (endh - pa) alloc limits)),
            (.globals, g), (.globReal, globReal conf curr g), (.temp 0, .word 0), (.temp 1, .word 0)]) ∧
      SetSep.star (wordHeap curr heap1 conf) (wordHeap other (heapExpand limit) conf)
        (SetSep.fun2Set (outMemory, fun address => domain address = true)) ∧
      state.h2 = [] ∧ state.r4 = [] ∧ state.r3 = [] ∧ state.r2 = [] ∧ partialLenInv state := by
  classical
  obtain ⟨curr, other, outMemory, state, current1, refs1, currLookup, otherLookup, startLookup,
    abstractRun, heapEq, allocEq, freeEq, gensEq, concrete, separated, h2Empty, r4Empty, r3Empty, r2Empty,
    heapLen, segment, inv, refsOk⟩ :=
    combinedPartial_store_simulation conf (root :: roots) (root1 :: roots1) heap heap1 a sp sp1 limit a1 n1
      gens gens1 limits store memory domain run kind selected limitEq ending ordered refBound good heapMem
  refine ⟨curr, other, outMemory, state, currLookup, otherLookup, abstractRun, heapEq, allocEq, freeEq, gensEq,
    ?_, separated, h2Empty, r4Empty, r3Empty, r2Empty, inv⟩
  have globalValue : holFapply store .globals = wordAddr conf root := holFapply_of_lookup global
  have currValue : holFapply store .currHeap = .word curr := holFapply_of_lookup currLookup
  have otherValue : holFapply store .otherHeap = .word other := holFapply_of_lookup otherLookup
  have startValue := holFapply_of_lookup startLookup
  have assum := heapInMemoryStore_gcAssum conf heap a sp sp1 limit gens store memory domain good heapMem
  have sizeValue : holFapply store .heapLength = .word (wordSemBytesInWord * BitVec.ofNat width limit) := by
    rcases heapMem with ⟨_, _, _, _, _, _, _, oldCurr, oldOther, _, _, oldCurrLookup, oldOtherLookup,
      _, _, _, heapSize, _⟩
    exact holFapply_of_lookup heapSize
  have endValue : holFapply store .endOfHeap = .word (curr + wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1)) := by
    rcases heapMem with ⟨_, _, _, _, _, _, _, oldCurr, oldOther, _, _, oldCurrLookup, _, _, _, oldEnd, _⟩
    have same : oldCurr = curr := by simpa [oldCurrLookup] using currLookup
    subst oldCurr
    exact holFapply_of_lookup oldEnd
  have enough' := enough curr state currLookup abstractRun
  have endOffset : (curr + wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1)) - curr =
      wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1) := by
    simp only [BitVec.add_comm curr, BitVec.add_sub_cancel]
  have cancelCommon (x y z : BitVec width) : (x + y) - (x + z) = y - z := by
    apply BitVec.sub_eq_iff_eq_add.mpr
    calc
      x + y = x + ((y - z) + z) := by rw [BitVec.sub_add_cancel]
      _ = (y - z) + (x + z) := by ac_rfl
  have enoughNorm :
      wordSemTheWord (holFapply store .allocSize) ≤
        wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1) -
          wordSemBytesInWord * BitVec.ofNat width (heapLength (state.old ++ state.h1)) ∧
      wordSemTheWord (holFapply store .allocSize) ≤ newTrig
        (wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1) -
          wordSemBytesInWord * BitVec.ofNat width (heapLength (state.old ++ state.h1)))
        (wordSemTheWord (holFapply store .allocSize)) limits := by
    simpa only [cancelCommon] using enough'
  simp only [List.map_cons] at concrete
  simp [wordGcFun, kind, selected, globalValue, currValue, otherValue, startValue, sizeValue, endValue,
    wordSemTheWord, endOffset, concrete, holHd, assum]
  simpa only [wordSemTheWord] using enoughNorm

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
