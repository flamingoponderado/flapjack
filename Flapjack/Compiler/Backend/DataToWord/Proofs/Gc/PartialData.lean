import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialInvariant
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialList
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.LoopArithmetic
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.LoopCell
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalData

/-! Copied-data scan simulation for partial collection. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private instance {α : Type} : Std.Associative (SetSep.star (α := α)) :=
  ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩
private instance {α : Type} : Std.Commutative (SetSep.star (α := α)) := ⟨SetSep.starComm⟩

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

/-- The concrete nonempty scan reads the represented header and follows its
raw-word or pointer-list branch. -/
theorem partialDataScan_wordStep {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width))) (k : Nat)
    (state : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (roots : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag) (payload : List (WordLocW width))
    (tail old current : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr p i : BitVec width) (xs : List (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (pending : state.h2 = .dataElement roots len (tag, payload) :: tail)
    (separated : SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (wordHeap p (state.h1 ++ state.h2) conf))
      (Misc.wordList (p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))) xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (fuel : heapLength state.h2 + state.n ≤ k) (invariant : partialLenInv state)
    (bytesBound : heapLength state.heap * (width / 8) < 2 ^ width)
    (good : goodDimindex width) (lenBound : conf.lenSize + 2 < width) :
    ∃ (header : BitVec width) (words : List (WordLocW width)),
      wordPayload roots len tag payload conf = (header, words, true) ∧ words.length = len ∧
      words.length < 2 ^ (width - 4) ∧
      (if header.getLsbD 2 then roots = [] else words = roots.map (wordAddr conf)) ∧
      let addr := p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)
      let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
      let gs := wordSemBytesInWord * BitVec.ofNat width genConf.genStart
      let rs := wordSemBytesInWord * BitVec.ofNat width genConf.refsStart
      wordGenGcPartialMoveData conf k (addr, i, free, curr, memory, domain, gs, rs) =
        if header.getLsbD 2 then
          wordGenGcPartialMoveData conf (k - 1)
            (addr + (BitVec.ofNat width words.length + 1) * wordSemBytesInWord,
             i, free, curr, memory, domain, gs, rs)
        else
          let (next, i1, pa1, memory1, c1) := wordGenGcPartialMoveList conf
            (addr + wordSemBytesInWord, BitVec.ofNat width words.length, i, free, curr, memory, domain, gs, rs)
          let (i2, pa2, memory2, c2) := wordGenGcPartialMoveData conf (k - 1)
            (next, i1, pa1, curr, memory1, domain, gs, rs)
          (i2, pa2, memory2, c1 && c2) := by
  obtain ⟨header, words, encoded, wordLen, bound, decoded, info, read, present, _⟩ :=
    scanDataCell conf state.h1 tail roots len tag payload
      (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) p
      (p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))) xs current
      memory domain frame good lenBound (by simpa only [pending] using separated)
  have different := partialDataScan_addresses_ne state _ tail p pending invariant bytesBound good
  have positive : 0 < k := by
    have h : 0 < heapLength state.h2 := by rw [pending]; simp [heapLength, elLength]
    omega
  have read' : memory (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)) = .word header := by
    simpa [wordSemBytesInWord, StackRemove.bytesInWord] using read
  have present' : domain (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)) = true := by
    simpa [wordSemBytesInWord, StackRemove.bytesInWord] using present
  refine ⟨header, words, encoded, wordLen, bound, info, ?_⟩
  dsimp only
  rw [wordGenGcPartialMoveData, if_neg different, if_neg (Nat.ne_of_gt positive)]
  simp only [present', read', wordSemIsWordLoc, wordSemTheWord,
    Bool.true_and, decoded]

/-- A raw data object has no roots to move, so a successful scan continues
after transferring it into the scanned prefix. -/
theorem partialDataScan_rawAbstract {α β : Type} (conf : GenGcPartial.Config β) (k : Nat)
    (state final : GcState α β) (len : Nat) (payload : β) (tail : List (HeapElement α β))
    (pending : state.h2 = .dataElement [] len payload :: tail)
    (run : GenGcPartial.gcMoveData conf state = final) (success : final.ok = true)
    (fuel : heapLength state.h2 + state.n ≤ k) :
    let next := { state with h1 := state.h1 ++ [HeapElement.dataElement [] len payload], h2 := tail }
    GenGcPartial.gcMoveData conf next = final ∧ state.ok = true ∧
      heapLength next.h2 + next.n ≤ k - 1 := by
  have step := partialDataScan_abstractStep conf state state final [] [] len payload tail pending rfl run success
  have stateOk : state.ok = true := step.2.1
  have recursive : GenGcPartial.gcMoveData conf
      { state with h1 := state.h1 ++ [HeapElement.dataElement [] len payload], h2 := tail } = final := by
    simpa [pending, stateOk] using step.1
  have remaining : heapLength tail + state.n ≤ k - 1 := by
    simp [pending, heapLength, elLength] at fuel ⊢
    omega
  exact ⟨recursive, stateOk, remaining⟩

/-- Advancing past a raw data object preserves the partial invariant and the
same separated memory assertion. -/
theorem partialDataScan_rawState {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width)))
    (state : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (len : Nat) (tag : HeapTag) (payload : List (WordLocW width))
    (tail old current : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr p : BitVec width) (xs : List (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (pending : state.h2 = .dataElement [] len (tag, payload) :: tail) (invariant : partialLenInv state)
    (refs : (state.r4 ++ state.r3 ++ state.r2 ++ state.r1).all (isRefElement genConf.isRef) = true)
    (separated : SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (wordHeap p (state.h1 ++ state.h2) conf))
      (Misc.wordList (p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))) xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true))) :
    let next := { state with h1 := state.h1 ++ [HeapElement.dataElement [] len (tag, payload)], h2 := tail }
    partialLenInv next ∧
      (next.r4 ++ next.r3 ++ next.r2 ++ next.r1).all (isRefElement genConf.isRef) = true ∧
      SetSep.star (SetSep.star (SetSep.star
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
        (wordHeap p (next.h1 ++ next.h2) conf))
        (Misc.wordList (p + wordSemBytesInWord * BitVec.ofNat width (heapLength (next.h1 ++ next.h2))) xs)) frame
        (SetSep.fun2Set (memory, fun address => domain address = true)) ∧
      heapLength (next.h1 ++ next.h2 ++ next.r4) + next.n =
        heapLength (state.h1 ++ state.h2 ++ state.r4) + state.n := by
  have layout : (state.h1 ++ [HeapElement.dataElement [] len (tag, payload)]) ++ tail = state.h1 ++ state.h2 := by
    simp [pending, List.append_assoc]
  refine ⟨?_, refs, ?_, ?_⟩
  · simpa only [partialLenInv, layout] using invariant
  · simpa only [layout] using separated
  · simp only [layout]

/-- Expose the pointer payload and retain the header and unscanned objects
in the frame for the partial collector's root-list simulation. -/
theorem partialDataScan_pointerLists {width : Nat} [NeZero width] (conf : Config)
    (state : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (roots : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width))
    (tail old current : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr p : BitVec width) (xs : List (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (pending : state.h2 = .dataElement roots len (tag, payload) :: tail)
    (good : goodDimindex width) (lenBound : conf.lenSize + 2 < width)
    (separated : SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (wordHeap p (state.h1 ++ state.h2) conf))
      (Misc.wordList (p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))) xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (pointer : (wordSemTheWord (memory (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)))).getLsbD 2 = false) :
    ∃ (header : BitVec width),
      wordPayload roots len tag payload conf = (header, roots.map (wordAddr conf), true) ∧
      roots.length = len ∧ roots.length < 2 ^ (width - 4) ∧
      decodeLength conf header = BitVec.ofNat width roots.length ∧ header.getLsbD 2 = false ∧
      let addr := p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)
      let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
      let rootFrame := SetSep.star (SetSep.one (addr, .word header))
        (SetSep.star (SetSep.star frame (wordHeap p state.h1 conf))
          (wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf))
      SetSep.star (SetSep.star (SetSep.star
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
        (Misc.wordList free xs)) (Misc.wordList (addr + wordSemBytesInWord) (roots.map (wordAddr conf)))) rootFrame
        (SetSep.fun2Set (memory, fun address => domain address = true)) := by
  obtain ⟨header, words, encoded, wordLen, bound, decoded, info, read, _, cell⟩ :=
    scanDataCell conf state.h1 tail roots len tag payload
      (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) p
      (p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))) xs current
      memory domain frame good lenBound (by simpa only [pending] using separated)
  have read' : memory (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)) = .word header := by
    simpa [wordSemBytesInWord, StackRemove.bytesInWord] using read
  have headerBit : header.getLsbD 2 = false := by simpa [read', wordSemTheWord] using pointer
  have mapped : words = roots.map (wordAddr conf) := by simpa [headerBit] using info
  subst words
  simp only [List.length_map] at wordLen bound decoded
  refine ⟨header, encoded, wordLen, bound, decoded, headerBit, ?_⟩
  let addr := p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)
  let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
  let source := wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf
  let prefixHeap := wordHeap p state.h1 conf
  let suffixHeap := wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf
  have reordered : SetSep.star (SetSep.star (SetSep.star source (Misc.wordList free xs))
      (Misc.wordList (addr + wordSemBytesInWord) (roots.map (wordAddr conf))))
      (SetSep.star (SetSep.one (addr, .word header))
        (SetSep.star (SetSep.star frame prefixHeap) suffixHeap))
      (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    change SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star source frame)
      prefixHeap) suffixHeap) (Misc.wordList addr (.word header :: roots.map (wordAddr conf))))
      (Misc.wordList free xs) _ at cell
    simp only [Misc.wordList] at cell
    have reorder : SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star source frame)
        prefixHeap) suffixHeap) (SetSep.star (SetSep.one (addr, .word header))
          (Misc.wordList (addr + wordSemBytesInWord) (roots.map (wordAddr conf))))) (Misc.wordList free xs) =
      SetSep.star (SetSep.star (SetSep.star source (Misc.wordList free xs))
        (Misc.wordList (addr + wordSemBytesInWord) (roots.map (wordAddr conf))))
        (SetSep.star (SetSep.one (addr, .word header)) (SetSep.star (SetSep.star frame prefixHeap) suffixHeap)) := by
      ac_rfl
    apply (congrFun reorder (SetSep.fun2Set (memory, fun address => domain address = true))).mp
    simpa only [wordSemBytesInWord, StackRemove.bytesInWord] using cell
  simpa only [addr, free, source, prefixHeap, suffixHeap, SetSep.starAssoc] using reordered

/-- Apply the partial root-list simulation to a pointer-valued pending object,
keeping the rest of the scanned and unscanned data in its frame. -/
theorem partialDataScan_moveRoots {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width)))
    (state middle : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (roots moved : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width))
    (tail old current refs : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr p k1 i1 pa1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (c1 : Bool)
    (pending : state.h2 = .dataElement roots len (tag, payload) :: tail)
    (abstractRun : GenGcPartial.gcMoveList genConf state roots = (moved, middle)) (middleOk : middle.ok = true)
    (limitEq : genConf.limit = heapLength state.heap)
    (heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (ordered : genConf.genStart ≤ genConf.refsStart) (refBound : genConf.refsStart ≤ heapLength state.heap)
    (segment : heapSegment (genConf.genStart, genConf.refsStart) state.heap = some (old, current, refs))
    (refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (byteBound : heapLength state.heap * (width / 8) < 2 ^ width)
    (dataBound : conf.lenSize + 2 < width)
    (separated : SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (wordHeap p (state.h1 ++ state.h2) conf))
      (Misc.wordList (p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))) xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (length : xs.length = state.n) (good : goodDimindex width)
    (pointer : (wordSemTheWord (memory (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)))).getLsbD 2 = false)
    (wordRun : wordGenGcPartialMoveList conf
      (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1) + wordSemBytesInWord,
       BitVec.ofNat width roots.length, BitVec.ofNat width state.a,
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)),
       curr, memory, domain, wordSemBytesInWord * BitVec.ofNat width genConf.genStart,
       wordSemBytesInWord * BitVec.ofNat width genConf.refsStart) = (k1, i1, pa1, memory1, c1)) :
    ∃ (header : BitVec width)
      (left right : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
      (xs1 : List (WordLocW width)) (current1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))),
      wordPayload roots len tag payload conf = (header, roots.map (wordAddr conf), true) ∧
      roots.length = len ∧ roots.length < 2 ^ (width - 4) ∧
      decodeLength conf header = BitVec.ofNat width roots.length ∧
      middle.h2 = state.h2 ++ left ∧ middle.r4 = right ++ state.r4 ∧
      (let addr := p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)
       let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
       let rootFrame := SetSep.star (SetSep.one (addr, .word header))
         (SetSep.star (SetSep.star frame (wordHeap p state.h1 conf))
           (wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf))
       SetSep.star (SetSep.star (SetSep.star (SetSep.star
         (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current1 conf)
         (wordHeap free left conf)) (Misc.wordList pa1 xs1))
         (Misc.wordList (addr + wordSemBytesInWord) (moved.map (wordAddr conf)))) rootFrame
         (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
       heapLength middle.heap = heapLength state.heap ∧
       heapSegment (genConf.genStart, genConf.refsStart) middle.heap = some (old, current1, refs) ∧
       c1 = true ∧ i1 = BitVec.ofNat width middle.a ∧ middle.n = xs1.length ∧
       state.n = heapLength left + middle.n + heapLength right ∧
       k1 = (addr + wordSemBytesInWord) + BitVec.ofNat width roots.length * wordSemBytesInWord ∧
       pa1 = free + wordSemBytesInWord * BitVec.ofNat width (heapLength left)) := by
  obtain ⟨header, encoded, rootsLen, rootsBound, decoded, _, lists⟩ :=
    partialDataScan_pointerLists conf state roots len tag payload tail old current curr p xs memory domain frame
      pending good dataBound separated pointer
  obtain ⟨left, right, leftEq, rightEq, clearRun⟩ :=
    partialMoveList_withNilLemma genConf roots state moved middle abstractRun middleOk
  have rootBound : roots.length < 2 ^ width := by
    have widthPos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
    have exponent : width - 4 < width := by omega
    have boundPow : 2 ^ (width - 4) < 2 ^ width := Nat.pow_lt_pow_right (by decide : 1 < 2) exponent
    omega
  let addr := p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)
  let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
  let rootFrame := SetSep.star (SetSep.one (addr, WordLocW.word header))
    (SetSep.star (SetSep.star frame (wordHeap p state.h1 conf))
      (wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf))
  obtain ⟨xs1, current1, memoryResult, heapLen, segment1, success, indexEq, xsLen, accounting, lastEq, paEq⟩ :=
    wordGenGcPartialMoveList_thm conf genConf roots { state with h2 := [], r4 := [] }
      { middle with h2 := left, r4 := right } moved old current refs curr free
      (addr + wordSemBytesInWord) k1 i1 pa1 xs memory memory1 domain rootFrame c1
      clearRun middleOk rfl rfl limitEq heapBound ordered refBound segment refClass byteBound lists wordRun length good rootBound
  exact ⟨header, left, right, xs1, current1, encoded, rootsLen, rootsBound, decoded, leftEq, rightEq,
    memoryResult, heapLen, segment1, success, indexEq, xsLen, accounting, lastEq, paEq⟩

/-- A partial root traversal preserves the number of roots even on failure. -/
theorem partialDataScan_moveListLength {α β : Type} (conf : GenGcPartial.Config β)
    (roots moved : List (HeapAddress α)) (state middle : GcState α β)
    (run : GenGcPartial.gcMoveList conf state roots = (moved, middle)) : moved.length = roots.length := by
  induction roots generalizing moved state middle with
  | nil => simp [GenGcPartial.gcMoveList, Prod.mk.injEq] at run; obtain ⟨rfl, _⟩ := run; rfl
  | cons root roots ih =>
    simp only [GenGcPartial.gcMoveList] at run
    generalize headRun : GenGcPartial.gcMove conf state root = headResult at run
    rcases headResult with ⟨root1, next⟩
    generalize tailRun : GenGcPartial.gcMoveList conf next roots = tailResult at run
    rcases tailResult with ⟨tail, final⟩
    simp only [Prod.mk.injEq] at run
    obtain ⟨rfl, _⟩ := run
    simp only [List.length_cons]
    rw [ih tail next final tailRun]

/-- A moved pointer payload retains its header and has exactly the updated
root words. This is local factoring of the partial data-scan proof. -/
theorem partialDataScan_movedElement {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width)))
    (state middle : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (roots moved : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width)) (header addr : BitVec width)
    (run : GenGcPartial.gcMoveList genConf state roots = (moved, middle))
    (encoded : wordPayload roots len tag payload conf = (header, roots.map (wordAddr conf), true))
    (rootsLen : roots.length = len) (bound : roots.length < 2 ^ (width - 4))
    (decoded : decodeLength conf header = BitVec.ofNat width roots.length) :
    wordEl addr (.dataElement moved len (tag, payload)) conf =
      SetSep.star (SetSep.one (addr, WordLocW.word header))
        (Misc.wordList (addr + wordSemBytesInWord) (moved.map (wordAddr conf))) := by
  have movedLen := partialDataScan_moveListLength genConf roots moved state middle run
  have encodedMoved : wordPayload moved len tag payload conf = (header, moved.map (wordAddr conf), true) := by
    have original : wordPayload roots roots.length tag payload conf =
        (header, roots.map (wordAddr conf), true) := by simpa only [rootsLen] using encoded
    simpa only [rootsLen] using wordPayload_swap roots moved tag payload conf header original movedLen
  funext cells
  apply propext
  simp only [wordEl, encodedMoved, StackRemove.WordListExists.starCond, Misc.wordList,
    List.length_map, movedLen, bound, decoded, and_self, and_true]
  rfl

/-- Reassemble the copied object and appended data into one heap assertion. -/
theorem partialDataScan_reassemble {width : Nat} [NeZero width] (conf : Config)
    (heap before tail left : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (moved : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width)) (header : BitVec width)
    (curr p free pa1 addr : BitVec width) (xs1 : List (WordLocW width))
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (addrEq : addr = p + wordSemBytesInWord * BitVec.ofNat width (heapLength before))
    (freeEq : free = addr + wordSemBytesInWord * BitVec.ofNat width (len + 1) +
      wordSemBytesInWord * BitVec.ofNat width (heapLength tail))
    (elementEq : wordEl addr (.dataElement moved len (tag, payload)) conf =
      SetSep.star (SetSep.one (addr, .word header))
        (Misc.wordList (addr + wordSemBytesInWord) (moved.map (wordAddr conf)))) :
    SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap conf)
      (wordHeap free left conf)) (Misc.wordList pa1 xs1))
      (Misc.wordList (addr + wordSemBytesInWord) (moved.map (wordAddr conf))))
      (SetSep.star (SetSep.one (addr, .word header))
        (SetSep.star (SetSep.star frame (wordHeap p before conf))
          (wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf))) =
    SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap conf)
      (wordHeap p (before ++ (.dataElement moved len (tag, payload) :: (tail ++ left))) conf))
      (Misc.wordList pa1 xs1)) frame := by
  change addr = p + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength before) at addrEq
  change free = addr + StackRemove.bytesInWord width * BitVec.ofNat width (len + 1) +
    StackRemove.bytesInWord width * BitVec.ofNat width (heapLength tail) at freeEq
  rw [wordHeapAppend before (.dataElement moved len (tag, payload) :: (tail ++ left)) p conf, ← addrEq]
  simp only [wordHeap, elLength, elementEq]
  rw [wordHeapAppend tail left (addr + StackRemove.bytesInWord width * BitVec.ofNat width (len + 1)) conf,
    ← freeEq]
  simp only [wordSemBytesInWord, StackRemove.bytesInWord]
  ac_rfl

/-- Reconstruct the recursive partial scan's separated memory after moving a
pointer payload. -/
theorem partialDataScan_nextMemory {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width)))
    (state middle : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (roots moved : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width))
    (tail left old current1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (header curr p pa1 : BitVec width) (xs1 : List (WordLocW width)) (flag : Bool)
    (memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (pending : state.h2 = .dataElement roots len (tag, payload) :: tail)
    (run : GenGcPartial.gcMoveList genConf state roots = (moved, middle))
    (encoded : wordPayload roots len tag payload conf = (header, roots.map (wordAddr conf), true))
    (rootsLen : roots.length = len) (bound : roots.length < 2 ^ (width - 4))
    (decoded : decodeLength conf header = BitVec.ofNat width roots.length)
    (leftEq : middle.h2 = state.h2 ++ left)
    (freeEq : pa1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)) +
      wordSemBytesInWord * BitVec.ofNat width (heapLength left))
    (separated :
      let addr := p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)
      let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
      SetSep.star (SetSep.star (SetSep.star (SetSep.star
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current1 conf)
        (wordHeap free left conf)) (Misc.wordList pa1 xs1))
        (Misc.wordList (addr + wordSemBytesInWord) (moved.map (wordAddr conf))))
        (SetSep.star (SetSep.one (addr, .word header))
          (SetSep.star (SetSep.star frame (wordHeap p state.h1 conf))
            (wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf)))
        (SetSep.fun2Set (memory1, fun address => domain address = true))) :
    let next := { middle with h1 := middle.h1 ++ [HeapElement.dataElement moved len (tag, payload)], h2 := middle.h2.drop 1, ok := flag }
    SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current1 conf)
      (wordHeap p (next.h1 ++ next.h2) conf))
      (Misc.wordList (p + wordSemBytesInWord * BitVec.ofNat width (heapLength (next.h1 ++ next.h2))) xs1)) frame
      (SetSep.fun2Set (memory1, fun address => domain address = true)) := by
  obtain ⟨h1Eq, _, _, _, _, _⟩ := partialMoveList_fixedFields genConf roots moved state middle run
  let addr := p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)
  let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
  have freeStart : free = addr + wordSemBytesInWord * BitVec.ofNat width (len + 1) +
      wordSemBytesInWord * BitVec.ofNat width (heapLength tail) := by
    simp [free, addr, pending, heapLength, List.map_append, List.sum_append, elLength,
      BitVec.ofNat_add, BitVec.mul_add]
    ac_rfl
  have elementEq := partialDataScan_movedElement conf genConf state middle roots moved len tag payload header addr
    run encoded rootsLen bound decoded
  have assembly := partialDataScan_reassemble conf current1 state.h1 tail left moved len tag payload header
    (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) p free pa1 addr xs1 frame
    rfl freeStart elementEq
  have reconstructed := (congrFun assembly (SetSep.fun2Set (memory1, fun address => domain address = true))).mp separated
  have nextPrefix : state.h1 ++ [HeapElement.dataElement moved len (tag, payload)] ++
      (state.h2 ++ left).drop 1 = state.h1 ++ (.dataElement moved len (tag, payload) :: (tail ++ left)) := by
    simp [pending, List.append_assoc]
  have heapEq : heapLength (state.h1 ++ (.dataElement moved len (tag, payload) :: (tail ++ left))) =
      heapLength (state.h1 ++ state.h2 ++ left) := by
    simp [pending, heapLength, List.map_append, List.sum_append, elLength]
  have paEq : pa1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2 ++ left)) := by
    rw [freeEq]
    simp only [heapLength_append, BitVec.ofNat_add, BitVec.mul_add]
    ac_rfl
  simp only [h1Eq, leftEq]
  rw [nextPrefix, heapEq, ← paEq]
  exact reconstructed

/-- The concrete scan cursor and free pointer match the recursive partial
state after a pointer payload is moved. -/
theorem partialDataScan_nextPointers {width : Nat} [NeZero width] {α β : Type}
    (state middle : GcState α β) (roots moved : List (HeapAddress α)) (len : Nat) (payload : β)
    (tail left : List (HeapElement α β)) (p k1 pa1 : BitVec width) (flag : Bool)
    (pending : state.h2 = .dataElement roots len payload :: tail)
    (h1Eq : middle.h1 = state.h1) (h2Eq : middle.h2 = state.h2 ++ left)
    (rootsLen : roots.length = len)
    (cursor : k1 = (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1) + wordSemBytesInWord) +
      BitVec.ofNat width roots.length * wordSemBytesInWord)
    (freeEq : pa1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)) +
      wordSemBytesInWord * BitVec.ofNat width (heapLength left)) :
    let next := { middle with h1 := middle.h1 ++ [HeapElement.dataElement moved len payload], h2 := middle.h2.drop 1, ok := flag }
    k1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength next.h1) ∧
    pa1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (next.h1 ++ next.h2)) := by
  have sameLen : heapLength ((middle.h1 ++ [HeapElement.dataElement moved len payload]) ++ middle.h2.drop 1) =
      heapLength (state.h1 ++ state.h2 ++ left) := by
    simp [heapLength, List.map_append, List.sum_append, elLength, h1Eq, h2Eq, pending]
  constructor
  · rw [cursor, rootsLen, h1Eq]
    calc
      _ = p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1) +
          (BitVec.ofNat width len + 1) * wordSemBytesInWord := by
        simp only [BitVec.add_mul]
        ac_rfl
      _ = _ := dataScan_nextCursor state moved len payload p
  · rw [sameLen, freeEq]
    simp only [heapLength_append, BitVec.ofNat_add, BitVec.mul_add]
    ac_rfl

/-- A successful pointer move advances the abstract scan and leaves enough
fuel for the recursive call. -/
theorem partialDataScan_pointerAbstract {α β : Type} (conf : GenGcPartial.Config β) (k : Nat)
    (state middle final : GcState α β) (roots moved : List (HeapAddress α))
    (len : Nat) (payload : β) (tail left : List (HeapElement α β))
    (pending : state.h2 = .dataElement roots len payload :: tail)
    (move : GenGcPartial.gcMoveList conf state roots = (moved, middle))
    (leftEq : middle.h2 = state.h2 ++ left)
    (run : GenGcPartial.gcMoveData conf state = final) (success : final.ok = true)
    (fuel : heapLength state.h2 + state.n ≤ k) :
    let next := { middle with h1 := middle.h1 ++ [HeapElement.dataElement moved len payload], h2 := tail ++ left, ok := true }
    GenGcPartial.gcMoveData conf next = final ∧ middle.ok = true ∧
      heapLength next.h2 + next.n ≤ k - 1 := by
  have step := partialDataScan_abstractStep conf state middle final roots moved len payload tail pending move run success
  have middleOk : middle.ok = true := step.2.1
  have recursive : GenGcPartial.gcMoveData conf
      { middle with h1 := middle.h1 ++ [HeapElement.dataElement moved len payload], h2 := tail ++ left, ok := true } = final := by
    simpa [leftEq, pending, middleOk] using step.1
  have account := partialMoveList_heapLengths roots conf state moved middle move middleOk
  have remaining : heapLength (tail ++ left) + middle.n ≤ k - 1 := by
    simp [leftEq, pending, heapLength, List.map_append, List.sum_append, elLength] at account fuel ⊢
    omega
  exact ⟨recursive, middleOk, remaining⟩

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
