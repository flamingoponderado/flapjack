import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialFull
import Flapjack.Compiler.Backend.GcCombined.Collector

/-! Combined collector's partial-generational heap simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.Compiler.Backend.GcCombined

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

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
