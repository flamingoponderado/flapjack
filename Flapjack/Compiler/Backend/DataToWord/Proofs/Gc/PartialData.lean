import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialInvariant
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialList
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.LoopArithmetic

/-! Copied-data scan simulation for partial collection. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

open Classical in
/-- Unfold a successful nonempty abstract scan into its root move and
recursive call. This is local factoring of the original scan equation. -/
theorem partialDataScan_abstractStep {α β : Type} (conf : GenGcPartial.Config β)
    (state middle final : GcState α β) (roots moved : List (HeapAddress α))
    (len : Nat) (payload : β) (tail : List (HeapElement α β))
    (pending : state.h2 = .dataElement roots len payload :: tail)
    (move : GenGcPartial.gcMoveList conf state roots = (moved, middle))
    (run : GenGcPartial.gcMoveData conf state = final) (success : final.ok = true) :
    let head := HeapElement.dataElement roots len payload
    let flag := middle.ok && decide (middle.h2 ≠ []) && decide (middle.h2.head? = some head)
    let next := { middle with h1 := middle.h1 ++ [HeapElement.dataElement moved len payload], h2 := middle.h2.drop 1, ok := flag }
    GenGcPartial.gcMoveData conf next = final ∧ middle.ok = true ∧
      middle.h2 ≠ [] ∧ middle.h2.head? = some head := by
  classical
  by_cases over : conf.limit < heapLength (state.h1 ++ .dataElement roots len payload :: tail)
  · rw [GenGcPartial.gcMoveData] at run
    simp [pending, over] at run
    subst final
    simp at success
  · have recursive : GenGcPartial.gcMoveData conf
        { middle with h1 := middle.h1 ++ [HeapElement.dataElement moved len payload], h2 := middle.h2.drop 1, ok := middle.ok && decide (middle.h2 ≠ []) && decide (middle.h2.head? = some (.dataElement roots len payload)) } = final := by
      cases state with
      | mk old h1 h2 r4 r3 r2 r1 a n status heap heap0 =>
        simp only at pending
        subst h2
        rw [GenGcPartial.gcMoveData] at run
        simpa only [over, ↓reduceIte, move] using run
    have flags := partialMoveData_okBefore conf _ final recursive success
    simp only [Bool.and_eq_true, decide_eq_true_eq] at flags
    exact ⟨recursive, flags.1.1, flags.1.2, flags.2⟩

/-- A nonempty copied-data region has distinct start and end addresses under
the original partial-heap invariant and byte bound. -/
theorem partialDataScan_addresses_ne {width : Nat} [NeZero width] {α β : Type}
    (state : GcState α β) (head : HeapElement α β) (tail : List (HeapElement α β))
    (p : BitVec width) (pending : state.h2 = head :: tail) (invariant : partialLenInv state)
    (bytesBound : heapLength state.heap * (width / 8) < 2 ^ width) (good : goodDimindex width) :
    p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1) ≠
      p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)) := by
  have positive : 0 < heapLength state.h2 := by
    rw [pending]
    have pos : 0 < elLength head := by cases head <;> simp [elLength]
    simp only [heapLength, List.map_cons, List.sum_cons]
    omega
  have le : heapLength state.h1 + heapLength state.h2 ≤ heapLength state.heap := by
    simp only [partialLenInv, heapLength_append] at invariant
    omega
  have bound : (heapLength state.h1 + heapLength state.h2) * (width / 8) < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ le) bytesBound
  have wordBytes : 0 < width / 8 := by rcases good with rfl | rfl <;> decide
  simpa only [heapLength_append, BitVec.mul_comm] using
    scanOffsets_ne p (heapLength state.h1) (heapLength state.h2) positive wordBytes bound

/-- Scanning a nonempty data element consumes at least one word of the
original pending-plus-free budget. -/
theorem partialDataScan_nextFuel {α β : Type} (k : Nat) (state middle : GcState α β)
    (head : HeapElement α β) (tail : List (HeapElement α β))
    (pending : middle.h2 = head :: tail)
    (accounting : state.n + heapLength state.h2 = middle.n + heapLength middle.h2)
    (fuel : heapLength state.h2 + state.n ≤ k) :
    heapLength (middle.h2.drop 1) + middle.n ≤ k - 1 := by
  have pos : 0 < elLength head := by cases head <;> simp [elLength]
  simp only [pending, List.drop_succ_cons, List.drop_zero, heapLength, List.map_cons, List.sum_cons] at accounting ⊢
  simp only [heapLength] at fuel
  omega

/-- Moving an object's roots and advancing the scan preserves the original
heap partition and its combined data/free/reference length. -/
theorem partialDataScan_nextInvariant {α β : Type} (conf : GenGcPartial.Config β)
    (state middle : GcState α β) (roots moved : List (HeapAddress α)) (len : Nat) (payload : β)
    (tail : List (HeapElement α β)) (flag : Bool)
    (move : GenGcPartial.gcMoveList conf state roots = (moved, middle)) (middleOk : middle.ok = true)
    (pending : middle.h2 = .dataElement roots len payload :: tail) (invariant : partialLenInv state) :
    let next := { middle with h1 := middle.h1 ++ [.dataElement moved len payload], h2 := middle.h2.drop 1, ok := flag }
    partialLenInv next ∧
      heapLength (next.h1 ++ next.h2 ++ next.r4) + next.n =
        heapLength (state.h1 ++ state.h2 ++ state.r4) + state.n := by
  obtain ⟨h1Eq, r4Eq, r3Eq, r2Eq, r1Eq, oldEq⟩ :=
    partialMoveList_fixedFields conf roots moved state middle move
  have heapEq := GenGcPartial.gcMoveList_heapLength roots moved conf state middle move
  have account := partialMoveList_heapLengths roots conf state moved middle move middleOk
  simp only [partialLenInv, heapLength_append] at invariant
  simp only [pending, List.drop_succ_cons, List.drop_zero, partialLenInv, heapLength_append,
    h1Eq, r4Eq, r3Eq, r2Eq, r1Eq, oldEq, ← heapEq]
  simp only [pending, heapLength, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, elLength] at account ⊢
  simp only [heapLength] at invariant
  omega

/-- The empty pending-data case of the partial collector data-scan theorem. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_partial_move_data_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMoveData_empty {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width))) (k : Nat)
    (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (curr p : BitVec width) (xs : List (WordLocW width))
    (pa1 i1 : BitVec width) (old current refs : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (c1 : Bool)
    (abstractRun : GenGcPartial.gcMoveData genConf state = state1) (_stateOk : state1.ok = true)
    (_limitEq : genConf.limit = heapLength state.heap)
    (_heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (_heapBytesBound : heapLength state.heap * (width / 8) < 2 ^ width)
    (_ordered : genConf.genStart ≤ genConf.refsStart) (_refBound : genConf.refsStart ≤ heapLength state.heap)
    (segment : heapSegment (genConf.genStart, genConf.refsStart) state.heap = some (old, current, refs))
    (_dataBound : conf.lenSize + 2 < width)
    (_refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (wordRun : wordGenGcPartialMoveData conf k
      (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1),
       BitVec.ofNat width state.a,
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)),
       curr, memory, domain, wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
       wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) = (i1, pa1, memory1, c1))
    (_countBound : heapLength state.h2 + state.n ≤ k) (invariant : partialLenInv state)
    (separated : SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (wordHeap p (state.h1 ++ state.h2) conf))
      (Misc.wordList (p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))) xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (allRefs : (state.r4 ++ state.r3 ++ state.r2 ++ state.r1).all (isRefElement genConf.isRef) = true)
    (length : xs.length = state.n) (_good : goodDimindex width) (empty : state.h2 = []) :
    ∃ xs1 current1,
      SetSep.star (SetSep.star (SetSep.star
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current1 conf)
        (wordHeap p (state1.h1 ++ state1.h2) conf))
        (Misc.wordList (p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state1.h1 ++ state1.h2))) xs1)) frame
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      state1.h2 = [] ∧ heapLength state1.heap = heapLength state.heap ∧
      heapSegment (genConf.genStart, genConf.refsStart) state1.heap = some (old, current1, refs) ∧
      c1 = true ∧ i1 = BitVec.ofNat width state1.a ∧ state1.n = xs1.length ∧ partialLenInv state1 ∧
      heapLength (state1.h1 ++ state1.h2 ++ state1.r4) + state1.n =
        heapLength (state.h1 ++ state.h2 ++ state.r4) + state.n ∧
      pa1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state1.h1 ++ state1.h2)) ∧
      (state1.r4 ++ state1.r3 ++ state1.r2 ++ state1.r1).all (isRefElement genConf.isRef) = true := by
  have abstractEq : GenGcPartial.gcMoveData genConf state = state := by
    rw [GenGcPartial.gcMoveData]
    simp [empty]
  rw [abstractEq] at abstractRun
  subst state1
  simp only [empty, List.append_nil] at wordRun
  rw [wordGenGcPartialMoveData] at wordRun
  simp only [↓reduceIte, Prod.mk.injEq] at wordRun
  obtain ⟨rfl, rfl, rfl, rfl⟩ := wordRun
  exact ⟨xs, current, separated, empty, rfl, segment, rfl, rfl, length.symm, invariant, rfl, by simp [empty], allRefs⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
