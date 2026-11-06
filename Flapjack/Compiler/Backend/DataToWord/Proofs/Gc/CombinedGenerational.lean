import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialFull
import Flapjack.Compiler.Backend.GcCombined.Collector

/-! Combined collector's partial-generational heap simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.Compiler.Backend.GcCombined

private instance {α : Type} : Std.Associative (SetSep.star (α := α)) :=
  ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩
private instance {α : Type} : Std.Commutative (SetSep.star (α := α)) := ⟨SetSep.starComm⟩

/-- Pack the major collector's separated output into the two heap regions
returned by the combined generational branch. -/
theorem combinedMajor_pack {width : Nat} [NeZero width] (conf : Config)
    (state : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (curr new : BitVec width) (xs : List (WordLocW width)) (limit : Nat)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (h2Empty : state.h2 = []) (r4Empty : state.r4 = []) (r3Empty : state.r3 = []) (r2Empty : state.r2 = [])
    (heapLen : heapLength state.heap = limit) (xsLen : state.n = xs.length)
    (separated : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (wordHeapParts conf new state xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true))) :
    SetSep.star (SetSep.star (wordHeap new (state.h1 ++ heapExpand state.n ++ state.r1) conf)
      (wordHeap curr (heapExpand limit) conf)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)) := by
  let freeAddr := new + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)
  let refsAddr := new + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1 + state.n)
  let target := SetSep.star (SetSep.star (wordHeap new state.h1 conf) (Misc.wordList freeAddr xs))
    (wordHeap refsAddr state.r1 conf)
  have arranged : SetSep.star (SetSep.star target frame) (wordHeap curr state.heap conf)
      (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    simp only [wordHeapParts, h2Empty, r4Empty, r3Empty, r2Empty, List.nil_append, List.append_nil, ← xsLen] at separated
    change SetSep.star (SetSep.star (wordHeap curr state.heap conf) target) frame _ at separated
    have reorder : SetSep.star (SetSep.star (wordHeap curr state.heap conf) target) frame =
        SetSep.star (SetSep.star target frame) (wordHeap curr state.heap conf) := by ac_rfl
    rwa [reorder] at separated
  have erased := wordHeap_imp_wordListExists state.heap (SetSep.star target frame) curr conf _ arranged
  rw [heapLen, ← wordHeap_heapExpand] at erased
  let others := SetSep.star (wordHeap refsAddr state.r1 conf) (SetSep.star (wordHeap curr (heapExpand limit) conf) frame)
  have freeSeparated : SetSep.star (SetSep.star (wordHeap new state.h1 conf) (Misc.wordList freeAddr xs)) others
      (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    have reorder : SetSep.star (SetSep.star target frame) (wordHeap curr (heapExpand limit) conf) =
        SetSep.star (SetSep.star (wordHeap new state.h1 conf) (Misc.wordList freeAddr xs)) others := by
      dsimp [target, others]
      ac_rfl
    rwa [reorder] at erased
  rcases freeSeparated with ⟨left, right, split, ⟨heapCells, freeCells, split', heapPart, freeWords⟩, rest⟩
  have freeExists : Misc.wordListExists freeAddr state.n freeCells :=
    ⟨xs, (StackRemove.WordListExists.starCond _ _ _).mpr ⟨freeWords, xsLen.symm⟩⟩
  have packedFree : SetSep.star (SetSep.star (wordHeap new state.h1 conf) (Misc.wordListExists freeAddr state.n)) others
      (SetSep.fun2Set (memory, fun address => domain address = true)) :=
    ⟨left, right, split, ⟨heapCells, freeCells, split', heapPart, freeExists⟩, rest⟩
  rw [← wordHeap_heapExpand] at packedFree
  have expandLen : heapLength (heapExpand state.n : List (HeapElement (WordLocW width)
      (HeapTag × List (WordLocW width)))) = state.n := by cases state.n <;> simp [heapExpand, heapLength, elLength]
  rw [wordHeapAppend (state.h1 ++ heapExpand state.n) state.r1 new conf,
    wordHeapAppend state.h1 (heapExpand state.n) new conf]
  simp only [heapLength_append, expandLen]
  have reorder' : SetSep.star (SetSep.star (wordHeap new state.h1 conf)
      (wordHeap freeAddr (heapExpand state.n) conf)) others =
    SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap new state.h1 conf)
      (wordHeap freeAddr (heapExpand state.n) conf)) (wordHeap refsAddr state.r1 conf))
      (wordHeap curr (heapExpand limit) conf)) frame := by dsimp [others]; ac_rfl
  rw [reorder'] at packedFree
  simpa only [freeAddr, refsAddr, wordSemBytesInWord, StackRemove.bytesInWord, SetSep.starAssoc] using packedFree

/-- Flapjack-specific composition of the partial collector's full simulation
with the partial branch of the combined collector. -/
theorem combinedPartial_heap_correct {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width))) (gens gens1 : GenState)
    (limits : List Nat) (refsStart : Nat)
    (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a1 n1 : Nat) (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (curr new pa1 i1 : BitVec width) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (roots1' : List (WordLocW width)) (c1 : Bool)
    (run : gcCombined genConf (.generational limits) (roots, heap, gens, refsStart, true) =
      (roots1, heap1, a1, n1, gens1, true))
    (heapBound : heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (byteBound : heapLength heap * (width / 8) < 2 ^ width)
    (ending : endsWithRefs refsStart heap) (limitEq : genConf.limit = heapLength heap)
    (ordered : (makePartialConf genConf gens refsStart).genStart ≤ refsStart) (refBound : refsStart ≤ heapLength heap)
    (dataBound : conf.lenSize + 2 < width) (refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (wordRun : wordGenGcPartialFull conf (roots.map (wordAddr conf), curr, new,
      wordSemBytesInWord * BitVec.ofNat width (heapLength heap), memory, domain,
      wordSemBytesInWord * BitVec.ofNat width (makePartialConf genConf gens refsStart).genStart,
      wordSemBytesInWord * BitVec.ofNat width refsStart) = (roots1', i1, pa1, memory1, c1))
    (separated : SetSep.star (SetSep.star (wordHeap curr heap conf)
      (Misc.wordListExists new (heapLength heap))) frame
      (SetSep.fun2Set (memory, fun address => domain address = true))) (good : goodDimindex width) :
    ∃ state current1 refs1,
      GenGcPartial.partialGc (makePartialConf genConf gens refsStart) (roots, heap) = (roots1, state) ∧
      heap1 = state.old ++ state.h1 ++ heapExpand state.n ++ state.r1 ∧
      a1 = state.a ∧ n1 = state.n ∧ gens1 = .genState 0 (limits.map fun _ => state.a) ∧
      SetSep.star (SetSep.star (wordHeap curr heap1 conf) (wordHeap new (heapExpand (heapLength heap)) conf)) frame
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      state.h2 = [] ∧ state.r4 = [] ∧ state.r3 = [] ∧ state.r2 = [] ∧
      roots1' = roots1.map (wordAddr conf) ∧ heapLength state.heap = heapLength heap ∧
      heapSegment ((makePartialConf genConf gens refsStart).genStart, refsStart) state.heap = some (state.old, current1, refs1) ∧
      c1 = true ∧ i1 = BitVec.ofNat width a1 ∧
      pa1 = curr + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.old ++ state.h1)) ∧
      partialLenInv state ∧ state.r1.all (isRefElement genConf.isRef) = true := by
  classical
  let partConf := makePartialConf genConf gens refsStart
  have partLimit : partConf.limit = genConf.limit := by cases gens; rfl
  have partRefs : partConf.refsStart = refsStart := by cases gens; rfl
  have partClass : partConf.isRef = genConf.isRef := by cases gens; rfl
  simp only [gcCombined, ↓reduceIte] at run
  generalize partialRun : GenGcPartial.partialGc partConf (roots, heap) = result at run
  obtain ⟨moved, state⟩ := result
  simp only [Prod.mk.injEq] at run
  obtain ⟨rfl, rfl, rfl, rfl, rfl, stateOk⟩ := run
  obtain ⟨current1, refs1, resultMemory, h2Empty, r4Empty, r3Empty, r2Empty, rootsEq, heapEq,
    segment, success, indexEq, paEq, inv, refsOk⟩ :=
    wordGenGcPartialFull_thm conf partConf roots moved heap state memory memory1 domain curr new pa1 i1 frame roots1' c1
      partialRun stateOk heapBound byteBound (by simpa [partRefs] using ending) (by simpa [partLimit] using limitEq)
      (by simpa [partRefs] using ordered) (by simpa [partRefs] using refBound) byteBound dataBound
      (by simpa [partClass] using refClass) (by simpa [partRefs] using wordRun) separated good
  have packed := (congrFun (partialFull_packResult conf state.old state.h1 state.r1 curr new pa1 state.n
    (heapLength heap) frame paEq) _).mp resultMemory
  refine ⟨state, current1, refs1, rfl, rfl, rfl, rfl, rfl, packed, h2Empty, r4Empty, r3Empty, r2Empty,
    rootsEq, heapEq, ?_, success, indexEq, paEq, inv, ?_⟩
  · simpa [partRefs] using segment
  · simpa [partClass] using refsOk

/-- Flapjack-specific composition of the major collector simulation with the
full-collection branch of the combined collector. -/
theorem combinedMajor_heap_correct {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width))) (gens gens1 : GenState)
    (limits : List Nat) (refsStart : Nat)
    (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a1 n1 : Nat) (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (curr new pb1 pa1 ib1 i1 : BitVec width) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (roots1' : List (WordLocW width)) (c1 : Bool)
    (run : gcCombined genConf (.generational limits) (roots, heap, gens, refsStart, false) =
      (roots1, heap1, a1, n1, gens1, true))
    (heapBound : heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (byteBound : heapLength heap * (width / 8) < 2 ^ width)
    (dataBound : conf.lenSize + 2 < width) (refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (lenBound : conf.lenSize + 5 ≤ width) (good : goodDimindex width)
    (wordRun : wordGenGc conf (roots.map (wordAddr conf), curr, new,
      wordSemBytesInWord * BitVec.ofNat width (heapLength heap), memory, domain) =
      (roots1', i1, pa1, ib1, pb1, memory1, c1))
    (separated : SetSep.star (SetSep.star (wordHeap curr heap conf)
      (Misc.wordListExists new (heapLength heap))) frame
      (SetSep.fun2Set (memory, fun address => domain address = true))) :
    ∃ state,
      GenGc.genGc genConf (roots, heap) = (roots1, state) ∧
      heap1 = state.h1 ++ heapExpand state.n ++ state.r1 ∧ a1 = state.a ∧ n1 = state.n ∧
      gens1 = .genState 0 (limits.map fun _ => state.a) ∧
      SetSep.star (SetSep.star (wordHeap new heap1 conf) (wordHeap curr (heapExpand (heapLength heap)) conf)) frame
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      state.h2 = [] ∧ state.r4 = [] ∧ state.r3 = [] ∧ state.r2 = [] ∧
      roots1' = roots1.map (wordAddr conf) ∧ heapLength state.heap = heapLength heap ∧ c1 = true ∧
      i1 = BitVec.ofNat width a1 ∧ ib1 = BitVec.ofNat width (a1 + n1) ∧
      pa1 = new + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1) ∧
      pb1 = new + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1 + state.n) ∧
      genLenInv state ∧ state.r1.all (isRefElement genConf.isRef) = true := by
  classical
  simp only [gcCombined, Bool.false_eq_true, ↓reduceIte] at run
  generalize majorRun : GenGc.genGc genConf (roots, heap) = result at run
  obtain ⟨moved, state⟩ := result
  simp only [Prod.mk.injEq] at run
  obtain ⟨rfl, rfl, rfl, rfl, rfl, stateOk⟩ := run
  obtain ⟨xs, resultMemory, h2Empty, r4Empty, r3Empty, r2Empty, rootsEq, heapEq, success, indexEq,
    limitEq, paEq, pbEq, _, xsLen, inv, refsOk⟩ :=
    wordGenGc_thm conf genConf roots moved heap state memory memory1 domain curr new pb1 pa1 ib1 i1 frame roots1' c1
      majorRun stateOk wordRun heapBound byteBound dataBound refClass lenBound good separated good
  have packed := combinedMajor_pack conf state curr new xs (heapLength heap) memory1 domain frame
    h2Empty r4Empty r3Empty r2Empty heapEq xsLen resultMemory
  exact ⟨state, rfl, rfl, rfl, rfl, rfl, packed, h2Empty, r4Empty, r3Empty, r2Empty, rootsEq, heapEq, success,
    indexEq, limitEq, paEq, pbEq, inv, refsOk⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
