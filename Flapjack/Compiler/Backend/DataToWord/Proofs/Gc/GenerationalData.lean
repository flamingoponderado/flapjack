module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalRefs
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.LoopCell

@[expose] public section

/-! Major collector data-scan simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

instance generationalDataInst1 {α : Type} : Std.Associative (SetSep.star (α := α)) :=
  ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩
instance generationalDataInst2 {α : Type} : Std.Commutative (SetSep.star (α := α)) := ⟨SetSep.starComm⟩

/-- Expose the concrete header and payload of the first pending data object,
while retaining the whole reference region in the separated frame. This is
local factoring for the major data-scan proof. -/
theorem dataScan_headCell {width : Nat} [NeZero width] (conf : Config)
    (state : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (roots : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width))
    (tail : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr p : BitVec width) (xs : List (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (pending : state.h2 = .dataElement roots len (tag, payload) :: tail)
    (good : goodDimindex width) (lenBound : conf.lenSize + 2 < width)
    (separated : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (wordHeapParts conf p state xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true))) :
    ∃ (header : BitVec width) (words : List (WordLocW width)),
      wordPayload roots len tag payload conf = (header, words, true) ∧
      words.length = len ∧ words.length < 2 ^ (width - 4) ∧
      decodeLength conf header = BitVec.ofNat width words.length ∧
      (if header.getLsbD 2 then roots = [] else words = roots.map (wordAddr conf)) ∧
      memory (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)) = .word header ∧
      domain (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)) = true ∧
      let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
      let base := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + xs.length)
      let extra := SetSep.star (wordHeap base (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) conf) frame
      SetSep.star (SetSep.star
        (SetSep.star (SetSep.star (SetSep.star (wordHeap curr state.heap conf) extra) (wordHeap p state.h1 conf))
          (wordHeap (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1) +
            wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf))
        (Misc.wordList (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)) (.word header :: words)))
        (Misc.wordList free xs) (SetSep.fun2Set (memory, fun address => domain address = true)) := by
  let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
  let base := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + xs.length)
  let extra := SetSep.star (wordHeap base (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) conf) frame
  have arranged : SetSep.star (SetSep.star (SetSep.star (wordHeap curr state.heap conf)
      (wordHeap p (state.h1 ++ .dataElement roots len (tag, payload) :: tail) conf))
      (Misc.wordList free xs)) extra (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    simp only [wordHeapParts, pending] at separated
    have reorder : SetSep.star (SetSep.star (wordHeap curr state.heap conf)
      (SetSep.star (SetSep.star (wordHeap p (state.h1 ++ .dataElement roots len (tag, payload) :: tail) conf)
        (Misc.wordList free xs)) (wordHeap base (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) conf))) frame =
      SetSep.star (SetSep.star (SetSep.star (wordHeap curr state.heap conf)
        (wordHeap p (state.h1 ++ .dataElement roots len (tag, payload) :: tail) conf))
        (Misc.wordList free xs)) extra := by dsimp [extra]; ac_rfl
    simp only [free, base, pending] at reorder ⊢
    rwa [reorder] at separated
  obtain ⟨header, words, encoded, wordLen, wordBound, decoded, info, read, present, cell⟩ :=
    scanDataCell conf state.h1 tail roots len tag payload curr p free xs state.heap memory domain extra good lenBound arranged
  refine ⟨header, words, encoded, wordLen, wordBound, decoded, info, ?_, ?_, ?_⟩
  · exact read
  · exact present
  · exact cell

open Classical in
/-- Unfold a successful nonempty abstract data scan into its root move and
recursive call. This local factoring has no separate HOL original. -/
theorem dataScan_abstractStep {α β : Type} (conf : GenGc.Config β)
    (state middle final : GcState α β) (roots moved : List (HeapAddress α))
    (len : Nat) (payload : β) (tail : List (HeapElement α β))
    (pending : state.h2 = .dataElement roots len payload :: tail)
    (move : GenGc.gcMoveList conf state roots = (moved, middle))
    (run : GenGc.gcMoveData conf state = final) (success : final.ok = true) :
    let head := HeapElement.dataElement roots len payload
    let flag := middle.ok && decide (middle.h2 ≠ []) && decide (middle.h2.head? = some head)
    let next := { middle with h1 := middle.h1 ++ [HeapElement.dataElement moved len payload], h2 := middle.h2.drop 1, ok := flag }
    GenGc.gcMoveData conf next = final ∧ middle.ok = true ∧
      middle.h2 ≠ [] ∧ middle.h2.head? = some head := by
  classical
  by_cases over : conf.limit < heapLength (state.h1 ++ .dataElement roots len payload :: tail)
  · rw [GenGc.gcMoveData] at run
    simp [pending, over] at run
    subst final
    simp at success
  · have recursive : GenGc.gcMoveData conf
        { middle with h1 := middle.h1 ++ [HeapElement.dataElement moved len payload], h2 := middle.h2.drop 1, ok := middle.ok && decide (middle.h2 ≠ []) && decide (middle.h2.head? = some (.dataElement roots len payload)) } = final := by
      cases state with
      | mk old h1 h2 r4 r3 r2 r1 a n ok heap heap0 =>
        simp only at pending
        subst h2
        rw [GenGc.gcMoveData] at run
        simpa only [over, ↓reduceIte, move] using run
    have nextOk : (GenGc.gcMoveData conf
        { middle with h1 := middle.h1 ++ [HeapElement.dataElement moved len payload], h2 := middle.h2.drop 1, ok := middle.ok && decide (middle.h2 ≠ []) && decide (middle.h2.head? = some (.dataElement roots len payload)) }).ok = true := by
      rw [recursive]
      exact success
    have flags := GenGc.gcMoveData_ok conf _ nextOk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at flags
    exact ⟨recursive, flags.1.1, flags.1.2, flags.2⟩

/-- Successful data scanning preserves the allocation-index/work-list
relationship while transferring each scanned object between lists. -/
theorem genMoveData_dataIndex {α β : Type} (conf : GenGc.Config β) (state : GcState α β) :
    (GenGc.gcMoveData conf state).ok = true →
    (GenGc.gcMoveData conf state).a + heapLength state.h1 + heapLength state.h2 =
      state.a + heapLength (GenGc.gcMoveData conf state).h1 + heapLength (GenGc.gcMoveData conf state).h2 := by
  classical
  induction state using GenGc.gcMoveData.induct conf with
  | case1 state empty => rw [GenGc.gcMoveData]; simp [empty]
  | case2 state head tail heap over => rw [GenGc.gcMoveData]; simp [heap, over]
  | case3 state tail roots len payload roots1 middle move heap bounded flag ih =>
    intro success
    obtain ⟨recursive, _, nonempty, headEq⟩ :=
      dataScan_abstractStep conf state middle (GenGc.gcMoveData conf state)
        roots roots1 len payload tail heap move rfl success
    have pending : ∃ rest, middle.h2 = .dataElement roots len payload :: rest := by
      cases h : middle.h2 with
      | nil => exact False.elim (nonempty h)
      | cons head rest =>
        simp only [h, List.head?_cons, Option.some.injEq] at headEq
        exact ⟨rest, by simp [headEq] at h ⊢⟩
    obtain ⟨rest, pending⟩ := pending
    have index := genMoveList_dataIndex conf roots roots1 state middle move
    dsimp only [flag] at ih
    have scan := ih (by rw [recursive]; exact success)
    rw [recursive] at scan
    simp only [pending, List.drop_succ_cons, List.drop_zero, heapLength, List.map_append,
      List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, elLength] at scan index ⊢
    omega
  | case4 state head tail heap bounded notData =>
    cases head with
    | unused len => rw [GenGc.gcMoveData]; simp [heap, bounded]
    | forwardPointer ptr value len => rw [GenGc.gcMoveData]; simp [heap, bounded]
    | dataElement roots len payload => exact False.elim (notData roots len payload rfl)

/-- The nonempty scan consumes at least one heap word, so the original
combined pending/free/reference budget decreases. This local arithmetic
factoring has no separate HOL original. -/
theorem dataScan_nextFuel {α β : Type} (k : Nat) (state middle : GcState α β)
    (roots : List (HeapAddress α)) (len : Nat) (payload : β)
    (tail left right : List (HeapElement α β))
    (pending : state.h2 = .dataElement roots len payload :: tail)
    (leftEq : middle.h2 = state.h2 ++ left) (rightEq : middle.r4 = right ++ state.r4)
    (accounting : state.n = heapLength left + middle.n + heapLength right)
    (fuel : heapLength state.h2 + state.n + heapLength state.r4 ≤ k) :
    heapLength (middle.h2.drop 1) + middle.n + heapLength middle.r4 ≤ k - 1 := by
  simp [leftEq, rightEq, pending, heapLength, List.map_append, List.sum_append, elLength] at fuel accounting ⊢
  omega

/-- A nonempty pending data segment cannot have the same start and end
addresses under the original heap byte bound. This local arithmetic lemma
rules out the word scan's empty branch. -/
theorem dataScan_addresses_ne {width : Nat} [NeZero width] {α β : Type}
    (state : GcState α β) (head : HeapElement α β) (tail : List (HeapElement α β))
    (p : BitVec width) (pending : state.h2 = head :: tail) (invariant : genLenInv state)
    (bytesBound : heapLength state.heap * (width / 8) < 2 ^ width) (good : goodDimindex width) :
    p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1) ≠
      p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)) := by
  have positive : 0 < heapLength state.h2 := by
    rw [pending]
    have pos : 0 < elLength head := by cases head <;> simp [elLength]
    simp only [heapLength, List.map_cons, List.sum_cons]
    omega
  have leHeap : heapLength state.h2 ≤ heapLength state.heap := by
    simp [genLenInv, heapLength, List.map_append, List.sum_append] at invariant ⊢
    omega
  have stepBound : (width / 8) * heapLength state.h2 < 2 ^ width := by
    have h := lt_of_le_of_lt (Nat.mul_le_mul_right (width / 8) leHeap) bytesBound
    simpa only [Nat.mul_comm] using h
  have bytesPositive : 0 < width / 8 := by rcases good with rfl | rfl <;> decide
  have nonzero : wordSemBytesInWord * BitVec.ofNat width (heapLength state.h2) ≠ 0 := by
    intro eq
    have natEq := congrArg BitVec.toNat eq
    simp [wordSemBytesInWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt stepBound] at natEq
    rcases natEq with tooSmall | empty
    · omega
    · omega
  intro equal
  apply nonzero
  apply add_left_cancel (a := p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1))
  calc
    _ = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)) := by
      simp only [heapLength_append, BitVec.ofNat_add, BitVec.mul_add]
      ac_rfl
    _ = _ := by rw [← equal]; simp

/-- The concrete nonempty data scan reads the represented header and takes
the source raw-word or pointer-list branch. This local transition lemma has
no separate HOL original. -/
theorem dataScan_wordStep {width : Nat} [NeZero width] (conf : Config) (k : Nat)
    (state : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (roots : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width))
    (tail : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr p i ib pb : BitVec width) (xs : List (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (pending : state.h2 = .dataElement roots len (tag, payload) :: tail)
    (separated : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (wordHeapParts conf p state xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (fuel : heapLength state.h2 + state.n + heapLength state.r4 ≤ k) (invariant : genLenInv state)
    (bytesBound : heapLength state.heap * (width / 8) < 2 ^ width)
    (good : goodDimindex width) (lenBound : conf.lenSize + 2 < width) :
    ∃ (header : BitVec width) (words : List (WordLocW width)),
      wordPayload roots len tag payload conf = (header, words, true) ∧
      words.length = len ∧ words.length < 2 ^ (width - 4) ∧
      (if header.getLsbD 2 then roots = [] else words = roots.map (wordAddr conf)) ∧
      let addr := p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)
      let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
      wordGenGcMoveData conf k (addr, i, free, ib, pb, curr, memory, domain) =
        if header.getLsbD 2 then
          wordGenGcMoveData conf (k - 1)
            (addr + (BitVec.ofNat width words.length + 1) * wordSemBytesInWord,
             i, free, ib, pb, curr, memory, domain)
        else
          let (next, i1, pa1, ib1, pb1, memory1, c1) := wordGenGcMoveList conf
            (addr + wordSemBytesInWord, BitVec.ofNat width words.length, i, free, ib, pb, curr, memory, domain)
          let (i2, pa2, ib2, pb2, memory2, c2) := wordGenGcMoveData conf (k - 1)
            (next, i1, pa1, ib1, pb1, curr, memory1, domain)
          (i2, pa2, ib2, pb2, memory2, c1 && c2) := by
  obtain ⟨header, words, encoded, wordLen, bound, decoded, info, read, present, _⟩ :=
    dataScan_headCell conf state roots len tag payload tail curr p xs memory domain frame pending good lenBound separated
  have different := dataScan_addresses_ne state _ tail p pending invariant bytesBound good
  have positive : 0 < k := by
    have h : 0 < heapLength state.h2 := by
      rw [pending]
      simp [heapLength, elLength]
    omega
  refine ⟨header, words, encoded, wordLen, bound, info, ?_⟩
  dsimp only
  rw [wordGenGcMoveData, if_neg different, if_neg (Nat.ne_of_gt positive)]
  simp only [present, read, wordSemIsWordLoc, wordSemTheWord, Bool.true_and, decoded]

/-- A raw data object has no roots to move, so a successful abstract scan
recurses after transferring that object from h2 to h1. This is local
factoring for the source data-scan proof. -/
theorem dataScan_rawAbstract {α β : Type} (conf : GenGc.Config β) (k : Nat)
    (state final : GcState α β) (len : Nat) (payload : β) (tail : List (HeapElement α β))
    (pending : state.h2 = .dataElement [] len payload :: tail)
    (run : GenGc.gcMoveData conf state = final) (success : final.ok = true)
    (fuel : heapLength state.h2 + state.n + heapLength state.r4 ≤ k) :
    let next := { state with h1 := state.h1 ++ [HeapElement.dataElement [] len payload], h2 := tail }
    GenGc.gcMoveData conf next = final ∧ state.ok = true ∧
      heapLength next.h2 + next.n + heapLength next.r4 ≤ k - 1 := by
  have step := dataScan_abstractStep conf state state final [] [] len payload tail pending rfl run success
  have stateOk : state.ok = true := step.2.1
  have recursive : GenGc.gcMoveData conf
      { state with h1 := state.h1 ++ [HeapElement.dataElement [] len payload], h2 := tail } = final := by
    simpa [pending, stateOk] using step.1
  have remaining : heapLength tail + state.n + heapLength state.r4 ≤ k - 1 := by
    simp [pending, heapLength, elLength] at fuel ⊢
    omega
  exact ⟨recursive, stateOk, remaining⟩

/-- Moving a raw data object into the scanned prefix preserves the abstract
heap invariant and its complete separated memory assertion. This is local
factoring for the source data-scan proof. -/
theorem dataScan_rawState {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width)))
    (state : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (len : Nat) (tag : HeapTag) (payload : List (WordLocW width))
    (tail : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr p : BitVec width) (xs : List (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (pending : state.h2 = .dataElement [] len (tag, payload) :: tail)
    (invariant : genLenInv state)
    (refs : (state.r4 ++ state.r3 ++ state.r2 ++ state.r1).all (isRefElement genConf.isRef) = true)
    (separated : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (wordHeapParts conf p state xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true))) :
    let next := { state with h1 := state.h1 ++ [HeapElement.dataElement [] len (tag, payload)], h2 := tail }
    genLenInv next ∧
      (next.r4 ++ next.r3 ++ next.r2 ++ next.r1).all (isRefElement genConf.isRef) = true ∧
      SetSep.star (SetSep.star (wordHeap curr next.heap conf) (wordHeapParts conf p next xs)) frame
        (SetSep.fun2Set (memory, fun address => domain address = true)) ∧
      heapLength (next.h1 ++ next.h2 ++ next.r4) + next.n =
        heapLength (state.h1 ++ state.h2 ++ state.r4) + state.n := by
  have layout : (state.h1 ++ [HeapElement.dataElement [] len (tag, payload)]) ++ tail = state.h1 ++ state.h2 := by
    simp [pending, List.append_assoc]
  refine ⟨?_, refs, ?_, ?_⟩
  · simpa only [genLenInv, layout] using invariant
  · simpa only [wordHeapParts, layout] using separated
  · simp only [layout]

/-- Scanning one object advances to the next abstract scanned-prefix
boundary. This local address identity has no separate HOL original. -/
theorem dataScan_nextCursor {width : Nat} [NeZero width] {α β : Type}
    (state : GcState α β) (roots : List (HeapAddress α)) (len : Nat) (payload : β) (p : BitVec width) :
    p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1) +
      (BitVec.ofNat width len + 1) * wordSemBytesInWord =
    p + wordSemBytesInWord * BitVec.ofNat width
      (heapLength (state.h1 ++ [HeapElement.dataElement roots len payload])) := by
  rw [heapLength_append]
  have oneLen : heapLength [HeapElement.dataElement roots len payload] = len + 1 := by
    simp [heapLength, elLength]
  rw [oneLen]
  simp only [BitVec.ofNat_add, BitVec.mul_add, BitVec.add_mul, BitVec.mul_one]
  ac_rfl

/-- A pointer-valued data object exposes its roots in the exact separated
layout required by the major root-list simulation. This local factoring has
no separate HOL original. -/
theorem dataScan_pointerLists {width : Nat} [NeZero width] (conf : Config)
    (state : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (roots : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width))
    (tail : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr p : BitVec width) (xs : List (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (pending : state.h2 = .dataElement roots len (tag, payload) :: tail)
    (good : goodDimindex width) (lenBound : conf.lenSize + 2 < width)
    (separated : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (wordHeapParts conf p state xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (pointer : (wordSemTheWord (memory (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)))).getLsbD 2 = false) :
    ∃ (header : BitVec width),
      wordPayload roots len tag payload conf = (header, roots.map (wordAddr conf), true) ∧
      roots.length = len ∧ roots.length < 2 ^ (width - 4) ∧
      decodeLength conf header = BitVec.ofNat width roots.length ∧ header.getLsbD 2 = false ∧
      let addr := p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)
      let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
      let base := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + xs.length)
      let rootFrame := SetSep.star (SetSep.one (addr, .word header))
        (SetSep.star (SetSep.star (SetSep.star (wordHeap base (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) conf) frame)
          (wordHeap p state.h1 conf))
          (wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf))
      SetSep.star (SetSep.star (SetSep.star (wordHeap curr state.heap conf) (Misc.wordList free xs))
        (Misc.wordList (addr + wordSemBytesInWord) (roots.map (wordAddr conf)))) rootFrame
        (SetSep.fun2Set (memory, fun address => domain address = true)) := by
  obtain ⟨header, words, encoded, wordLen, bound, decoded, info, read, _, cell⟩ :=
    dataScan_headCell conf state roots len tag payload tail curr p xs memory domain frame pending good lenBound separated
  have headerBit : header.getLsbD 2 = false := by simpa [read, wordSemTheWord] using pointer
  have mapped : words = roots.map (wordAddr conf) := by simpa [headerBit] using info
  subst words
  simp only [List.length_map] at wordLen bound decoded
  refine ⟨header, encoded, wordLen, bound, decoded, headerBit, ?_⟩
  let addr := p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)
  let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
  let base := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + xs.length)
  let extra := SetSep.star (wordHeap base (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) conf) frame
  let prefixHeap := wordHeap p state.h1 conf
  let suffixHeap := wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf
  have reordered : SetSep.star (SetSep.star (SetSep.star (wordHeap curr state.heap conf) (Misc.wordList free xs))
      (Misc.wordList (addr + wordSemBytesInWord) (roots.map (wordAddr conf))))
      (SetSep.star (SetSep.one (addr, .word header))
        (SetSep.star (SetSep.star extra prefixHeap) suffixHeap))
      (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    change SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap curr state.heap conf) extra)
      prefixHeap) suffixHeap) (Misc.wordList addr (.word header :: roots.map (wordAddr conf))))
      (Misc.wordList free xs) _ at cell
    simp only [Misc.wordList] at cell
    have reorder : SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap curr state.heap conf) extra)
        prefixHeap) suffixHeap) (SetSep.star (SetSep.one (addr, .word header))
          (Misc.wordList (addr + wordSemBytesInWord) (roots.map (wordAddr conf))))) (Misc.wordList free xs) =
      SetSep.star (SetSep.star (SetSep.star (wordHeap curr state.heap conf) (Misc.wordList free xs))
        (Misc.wordList (addr + wordSemBytesInWord) (roots.map (wordAddr conf))))
        (SetSep.star (SetSep.one (addr, .word header)) (SetSep.star (SetSep.star extra prefixHeap) suffixHeap)) := by
      ac_rfl
    apply (congrFun reorder (SetSep.fun2Set (memory, fun address => domain address = true))).mp
    simpa only [wordSemBytesInWord, StackRemove.bytesInWord] using cell
  simpa only [addr, free, base, extra, prefixHeap, suffixHeap, SetSep.starAssoc] using reordered

/-- The state after scanning a pointer-valued object preserves the length and
reference invariants and transfers that object to the scanned prefix. This
is local factoring of the major data-scan proof. -/
theorem dataScan_advanceInvariant {α β : Type} (conf : GenGc.Config β)
    (state middle : GcState α β) (roots moved : List (HeapAddress α))
    (len : Nat) (payload : β) (tail left right : List (HeapElement α β)) (flag : Bool)
    (pending : state.h2 = .dataElement roots len payload :: tail)
    (move : GenGc.gcMoveList conf state roots = (moved, middle)) (middleOk : middle.ok = true)
    (leftEq : middle.h2 = state.h2 ++ left) (rightEq : middle.r4 = right ++ state.r4)
    (accounting : state.n = heapLength left + middle.n + heapLength right)
    (invariant : genLenInv state)
    (refs : (state.r4 ++ state.r3 ++ state.r2 ++ state.r1).all (isRefElement conf.isRef) = true)
    (newRefs : (right ++ middle.r3 ++ middle.r2 ++ middle.r1).all (isRefElement conf.isRef) = true) :
    let next := { middle with h1 := middle.h1 ++ [HeapElement.dataElement moved len payload], h2 := middle.h2.drop 1, ok := flag }
    genLenInv next ∧ next.h1 = state.h1 ++ [.dataElement moved len payload] ∧ next.h2 = tail ++ left ∧
      (next.r4 ++ next.r3 ++ next.r2 ++ next.r1).all (isRefElement conf.isRef) = true ∧
      heapLength (next.h1 ++ next.h2 ++ next.r4) + next.n =
        heapLength (state.h1 ++ state.h2 ++ state.r4) + state.n := by
  obtain ⟨h1Eq, _, _, _⟩ := genMoveList_const conf roots moved state middle move
  have midInv := genMoveList_lenInv conf roots moved state middle move middleOk invariant
  have tailEq : middle.h2.drop 1 = tail ++ left := by simp [leftEq, pending]
  have oldRefs : state.r4.all (isRefElement conf.isRef) = true := by
    apply List.all_eq_true.mpr
    intro element member
    exact (List.all_eq_true.mp refs) element (by simp [member])
  constructor
  · simp only [genLenInv] at midInv ⊢
    simp [heapLength, List.map_append, List.sum_append, elLength, h1Eq, leftEq, pending] at midInv ⊢
    omega
  constructor
  · simp [h1Eq]
  constructor
  · exact tailEq
  constructor
  · simp only [rightEq, List.all_append, Bool.and_eq_true] at newRefs oldRefs ⊢
    aesop
  · simp [heapLength, List.map_append, List.sum_append, elLength, h1Eq, pending, tailEq, rightEq] at accounting ⊢
    omega

/-- Run the verified major root-list simulation on a pointer-valued pending
data object, retaining its header and the other heap regions in the frame.
This is local factoring of the nonempty data-scan proof. -/
theorem dataScan_moveRoots {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width)))
    (state middle : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (roots moved : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width))
    (tail : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr p k1 i1 pa1 ib1 pb1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (c1 : Bool)
    (pending : state.h2 = .dataElement roots len (tag, payload) :: tail)
    (abstractRun : GenGc.gcMoveList genConf state roots = (moved, middle)) (middleOk : middle.ok = true)
    (heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t) (lenBound : conf.lenSize + 5 ≤ width)
    (dataBound : conf.lenSize + 2 < width)
    (refs : (state.r4 ++ state.r3 ++ state.r2 ++ state.r1).all (isRefElement genConf.isRef) = true)
    (separated : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (wordHeapParts conf p state xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (length : xs.length = state.n) (good : goodDimindex width)
    (pointer : (wordSemTheWord (memory (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)))).getLsbD 2 = false)
    (wordRun : wordGenGcMoveList conf
      (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1) + wordSemBytesInWord,
       BitVec.ofNat width roots.length, BitVec.ofNat width state.a,
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)),
       BitVec.ofNat width (state.a + state.n),
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + state.n),
       curr, memory, domain) = (k1, i1, pa1, ib1, pb1, memory1, c1)) :
    ∃ (header : BitVec width)
      (left right : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
      (xs1 : List (WordLocW width)),
      wordPayload roots len tag payload conf = (header, roots.map (wordAddr conf), true) ∧
      roots.length = len ∧ roots.length < 2 ^ (width - 4) ∧
      decodeLength conf header = BitVec.ofNat width roots.length ∧
      middle.h2 = state.h2 ++ left ∧ middle.r4 = right ++ state.r4 ∧
      (let addr := p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)
       let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
       let base := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + xs.length)
       let rootFrame := SetSep.star (SetSep.one (addr, .word header))
         (SetSep.star (SetSep.star (SetSep.star (wordHeap base (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) conf) frame)
           (wordHeap p state.h1 conf))
           (wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf))
       SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap curr middle.heap conf)
         (wordHeap free left conf)) (wordHeap pb1 right conf)) (Misc.wordList pa1 xs1))
         (Misc.wordList (addr + wordSemBytesInWord) (moved.map (wordAddr conf)))) rootFrame
         (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
       heapLength middle.heap = heapLength state.heap ∧ c1 = true ∧ i1 = BitVec.ofNat width middle.a ∧
       ib1 = BitVec.ofNat width (middle.a + middle.n) ∧ middle.n = xs1.length ∧
       state.n = heapLength left + middle.n + heapLength right ∧
       k1 = (addr + wordSemBytesInWord) + BitVec.ofNat width roots.length * wordSemBytesInWord ∧
       pa1 = free + wordSemBytesInWord * BitVec.ofNat width (heapLength left) ∧
       pb1 = pa1 + wordSemBytesInWord * BitVec.ofNat width middle.n ∧
       (right ++ middle.r3 ++ middle.r2 ++ middle.r1).all (isRefElement genConf.isRef) = true) := by
  obtain ⟨header, encoded, rootsLen, rootsBound, decoded, _, lists⟩ :=
    dataScan_pointerLists conf state roots len tag payload tail curr p xs memory domain frame
      pending good dataBound separated pointer
  obtain ⟨left, right, leftEq, rightEq, clearRun⟩ :=
    gcMoveList_withNilLemma genConf roots moved state middle abstractRun middleOk
  have clearRefs : (({ state with h2 := [], r4 := [] }).r4 ++
      ({ state with h2 := [], r4 := [] }).r3 ++ ({ state with h2 := [], r4 := [] }).r2 ++
      ({ state with h2 := [], r4 := [] }).r1).all (isRefElement genConf.isRef) = true := by
    simp only at refs ⊢
    simp only [List.nil_append, List.all_append, Bool.and_eq_true] at refs ⊢
    exact ⟨⟨refs.1.1.2, refs.1.2⟩, refs.2⟩
  have rootBound : roots.length < 2 ^ width := by
    have widthPos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
    have exponent : width - 4 < width := by omega
    have boundPow : 2 ^ (width - 4) < 2 ^ width := Nat.pow_lt_pow_right (by decide : 1 < 2) exponent
    omega
  let addr := p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)
  let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
  let base := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + xs.length)
  let rootFrame := SetSep.star (SetSep.one (addr, WordLocW.word header))
    (SetSep.star (SetSep.star (SetSep.star (wordHeap base (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) conf) frame)
      (wordHeap p state.h1 conf)) (wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf))
  have freeEnd : free + wordSemBytesInWord * BitVec.ofNat width state.n =
      p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + state.n) := by
    simp only [free, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
  have wordRun' : wordGenGcMoveList conf
      (addr + wordSemBytesInWord, BitVec.ofNat width roots.length, BitVec.ofNat width state.a, free,
       BitVec.ofNat width (state.a + state.n), free + wordSemBytesInWord * BitVec.ofNat width state.n,
       curr, memory, domain) = (k1, i1, pa1, ib1, pb1, memory1, c1) := by
    rw [freeEnd]
    exact wordRun
  obtain ⟨xs1, memoryResult, heapLen, success, indexEq, limitEq, xsLen, accounting, lastEq, paEq, pbEq, refsOut⟩ :=
    wordGenGcMoveList_thm conf genConf roots { state with h2 := [], r4 := [] }
      { middle with h2 := left, r4 := right } moved curr free (addr + wordSemBytesInWord) k1 i1 pa1 ib1 pb1
      xs memory memory1 domain rootFrame c1 clearRun middleOk rfl rfl heapBound refClass lenBound lists wordRun'
      clearRefs length good rootBound
  exact ⟨header, left, right, xs1, encoded, rootsLen, rootsBound, decoded, leftEq, rightEq,
    memoryResult, heapLen, success, indexEq, limitEq, xsLen, accounting, lastEq, paEq, pbEq, refsOut⟩

/-- Reassemble the updated data prefix, free space, and reference region from
the exact separated resources returned by the root-list simulation. This is
local separation factoring for the data-scan proof. -/
theorem dataScan_reassembleRegions {width : Nat} [NeZero width] (conf : Config)
    (heap before tail left right references : List
      (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (moved : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width)) (header : BitVec width)
    (curr p free pa1 pb1 base addr : BitVec width) (xs1 : List (WordLocW width))
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (addrEq : addr = p + wordSemBytesInWord * BitVec.ofNat width (heapLength before))
    (freeEq : free = addr + wordSemBytesInWord * BitVec.ofNat width (len + 1) +
      wordSemBytesInWord * BitVec.ofNat width (heapLength tail))
    (baseEq : base = pb1 + wordSemBytesInWord * BitVec.ofNat width (heapLength right))
    (elementEq : wordEl addr (.dataElement moved len (tag, payload)) conf =
      SetSep.star (SetSep.one (addr, .word header))
        (Misc.wordList (addr + wordSemBytesInWord) (moved.map (wordAddr conf)))) :
    SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap conf)
      (wordHeap free left conf)) (wordHeap pb1 right conf)) (Misc.wordList pa1 xs1))
      (Misc.wordList (addr + wordSemBytesInWord) (moved.map (wordAddr conf))))
      (SetSep.star (SetSep.one (addr, .word header))
        (SetSep.star (SetSep.star (SetSep.star (wordHeap base references conf) frame)
          (wordHeap p before conf))
          (wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf))) =
    SetSep.star (SetSep.star (wordHeap curr heap conf)
      (SetSep.star (SetSep.star (wordHeap p (before ++ (.dataElement moved len (tag, payload) :: (tail ++ left))) conf)
        (Misc.wordList pa1 xs1)) (wordHeap pb1 (right ++ references) conf))) frame := by
  change addr = p + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength before) at addrEq
  change free = addr + StackRemove.bytesInWord width * BitVec.ofNat width (len + 1) +
    StackRemove.bytesInWord width * BitVec.ofNat width (heapLength tail) at freeEq
  change base = pb1 + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength right) at baseEq
  rw [wordHeapAppend before (.dataElement moved len (tag, payload) :: (tail ++ left)) p conf,
    wordHeapAppend right references pb1 conf, ← addrEq, ← baseEq]
  simp only [wordHeap, elLength, elementEq]
  rw [wordHeapAppend tail left (addr + StackRemove.bytesInWord width * BitVec.ofNat width (len + 1)) conf,
    ← freeEq]
  simp only [wordSemBytesInWord, StackRemove.bytesInWord]
  ac_rfl

/-- Reconstruct the exact separated memory assertion for the recursive
pointer-data scan after the root-list move. This is local factoring of the
source nonempty scan proof. -/
theorem dataScan_nextMemory {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width)))
    (state middle : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (roots moved : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width))
    (tail left right : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (header curr p pa1 pb1 : BitVec width) (xs xs1 : List (WordLocW width)) (flag : Bool)
    (memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (pending : state.h2 = .dataElement roots len (tag, payload) :: tail)
    (abstractRun : GenGc.gcMoveList genConf state roots = (moved, middle))
    (encoded : wordPayload roots len tag payload conf = (header, roots.map (wordAddr conf), true))
    (rootsLen : roots.length = len) (bound : roots.length < 2 ^ (width - 4))
    (decoded : decodeLength conf header = BitVec.ofNat width roots.length)
    (leftEq : middle.h2 = state.h2 ++ left) (rightEq : middle.r4 = right ++ state.r4)
    (freeEq : pa1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)) +
      wordSemBytesInWord * BitVec.ofNat width (heapLength left))
    (refsEq : pb1 = pa1 + wordSemBytesInWord * BitVec.ofNat width middle.n)
    (accounting : state.n = heapLength left + middle.n + heapLength right)
    (length : xs.length = state.n) (length1 : middle.n = xs1.length)
    (separated :
      let addr := p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)
      let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
      let base := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + xs.length)
      SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap curr middle.heap conf)
        (wordHeap free left conf)) (wordHeap pb1 right conf)) (Misc.wordList pa1 xs1))
        (Misc.wordList (addr + wordSemBytesInWord) (moved.map (wordAddr conf))))
        (SetSep.star (SetSep.one (addr, .word header))
          (SetSep.star (SetSep.star (SetSep.star (wordHeap base (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) conf) frame)
            (wordHeap p state.h1 conf))
            (wordHeap (addr + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf)))
        (SetSep.fun2Set (memory1, fun address => domain address = true))) :
    let next := { middle with h1 := middle.h1 ++ [HeapElement.dataElement moved len (tag, payload)], h2 := middle.h2.drop 1, ok := flag }
    SetSep.star (SetSep.star (wordHeap curr next.heap conf) (wordHeapParts conf p next xs1)) frame
      (SetSep.fun2Set (memory1, fun address => domain address = true)) := by
  obtain ⟨h1Eq, r1Eq, r2Eq, r3Eq⟩ := genMoveList_const genConf roots moved state middle abstractRun
  obtain ⟨paEq, pbEq, baseEq⟩ := refScan_regionAddresses state middle left right p pa1 pb1 xs.length
    freeEq refsEq accounting length
  let addr := p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)
  let free := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2))
  let base := p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + xs.length)
  have freeStart : free = addr + wordSemBytesInWord * BitVec.ofNat width (len + 1) +
      wordSemBytesInWord * BitVec.ofNat width (heapLength tail) := by
    simp [free, addr, pending, heapLength, List.map_append, List.sum_append, elLength,
      BitVec.ofNat_add, BitVec.mul_add]
    ac_rfl
  have elementEq := refScan_movedElement conf genConf state middle roots moved len tag payload header addr
    abstractRun encoded rootsLen bound decoded
  have assembly := dataScan_reassembleRegions conf middle.heap state.h1 tail left right
    (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) moved len tag payload header curr p free pa1 pb1 base addr xs1 frame
    rfl freeStart baseEq.symm elementEq
  have reconstructed := (congrFun assembly (SetSep.fun2Set (memory1, fun address => domain address = true))).mp separated
  have nextPrefix : state.h1 ++ [HeapElement.dataElement moved len (tag, payload)] ++
      (state.h2 ++ left).drop 1 = state.h1 ++ (.dataElement moved len (tag, payload) :: (tail ++ left)) := by
    simp [pending, List.append_assoc]
  have heapEq : heapLength (state.h1 ++ (.dataElement moved len (tag, payload) :: (tail ++ left))) =
      heapLength (state.h1 ++ state.h2 ++ left) := by
    simp [pending, heapLength, List.map_append, List.sum_append, elLength]
  simp only [wordHeapParts]
  simp only [h1Eq, leftEq, rightEq, r1Eq, r2Eq, r3Eq, ← length1]
  rw [nextPrefix, heapEq]
  rw [← paEq, ← pbEq]
  simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using reconstructed

/-- The pointer-data branch's concrete scan and allocation pointers equal the
addresses computed from the recursive state. This is local arithmetic
factoring for the data-scan proof. -/
theorem dataScan_nextPointers {width : Nat} [NeZero width] {α β : Type}
    (state middle : GcState α β) (roots moved : List (HeapAddress α)) (len : Nat) (payload : β)
    (tail left right : List (HeapElement α β)) (p k1 pa1 pb1 : BitVec width) (xsLength : Nat) (flag : Bool)
    (pending : state.h2 = .dataElement roots len payload :: tail)
    (h1Eq : middle.h1 = state.h1) (h2Eq : middle.h2 = state.h2 ++ left)
    (rootsLen : roots.length = len) (accounting : state.n = heapLength left + middle.n + heapLength right)
    (length : xsLength = state.n)
    (cursor : k1 = (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1) + wordSemBytesInWord) +
      BitVec.ofNat width roots.length * wordSemBytesInWord)
    (freeEq : pa1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)) +
      wordSemBytesInWord * BitVec.ofNat width (heapLength left))
    (refsEq : pb1 = pa1 + wordSemBytesInWord * BitVec.ofNat width middle.n) :
    let next := { middle with h1 := middle.h1 ++ [HeapElement.dataElement moved len payload], h2 := middle.h2.drop 1, ok := flag }
    k1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength next.h1) ∧
    pa1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (next.h1 ++ next.h2)) ∧
    pb1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (next.h1 ++ next.h2) + next.n) := by
  obtain ⟨paEq, pbEq, _⟩ := refScan_regionAddresses state middle left right p pa1 pb1 xsLength
    freeEq refsEq accounting length
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
  constructor
  · simpa only [sameLen] using paEq
  · simpa only [sameLen] using pbEq

/-- Empty pending-data case of the original major data-scan simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_move_data_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMoveData_empty {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width))) (k : Nat)
    (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (curr p : BitVec width) (xs : List (WordLocW width))
    (pb1 pa1 ib1 i1 : BitVec width)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (c1 : Bool)
    (abstractRun : GenGc.gcMoveData genConf state = state1) (stateOk : state1.ok = true)
    (_heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (_heapBytesBound : heapLength state.heap * (width / 8) < 2 ^ width)
    (_dataBound : conf.lenSize + 2 < width)
    (_refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (_lenBound : conf.lenSize + 5 ≤ width)
    (wordRun : wordGenGcMoveData conf k
      (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1),
       BitVec.ofNat width state.a,
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)),
       BitVec.ofNat width (state.a + state.n),
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + state.n),
       curr, memory, domain) = (i1, pa1, ib1, pb1, memory1, c1))
    (_countBound : heapLength state.h2 + state.n + heapLength state.r4 ≤ k) (invariant : genLenInv state)
    (separated : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (wordHeapParts conf p state xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (refs : (state.r4 ++ state.r3 ++ state.r2 ++ state.r1).all (isRefElement genConf.isRef) = true)
    (length : xs.length = state.n) (_good : goodDimindex width) (empty : state.h2 = []) :
    ∃ xs1,
      SetSep.star (SetSep.star (wordHeap curr state1.heap conf) (wordHeapParts conf p state1 xs1)) frame
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      state1.h2 = [] ∧ heapLength state1.heap = heapLength state.heap ∧
      c1 = true ∧ i1 = BitVec.ofNat width state1.a ∧ ib1 = BitVec.ofNat width (state1.a + state1.n) ∧
      state1.n = xs1.length ∧ genLenInv state1 ∧
      heapLength (state1.h1 ++ state1.h2 ++ state1.r4) + state1.n =
        heapLength (state.h1 ++ state.h2 ++ state.r4) + state.n ∧
      pa1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state1.h1 ++ state1.h2)) ∧
      pb1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state1.h1 ++ state1.h2) + state1.n) ∧
      (state1.r4 ++ state1.r3 ++ state1.r2 ++ state1.r1).all (isRefElement genConf.isRef) = true := by
  have abstractEq : GenGc.gcMoveData genConf state = state := by
    rw [GenGc.gcMoveData]
    simp [empty]
  rw [abstractEq] at abstractRun
  subst state1
  simp only [empty, List.append_nil] at wordRun
  rw [wordGenGcMoveData] at wordRun
  simp only [↓reduceIte, Prod.mk.injEq] at wordRun
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := wordRun
  exact ⟨xs, separated, empty, rfl, rfl, rfl, rfl, length.symm, invariant, rfl, by simp [empty],
    by simp [empty], refs⟩

/-- Original major collector data-scan simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_move_data_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMoveData_thm {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width))) (k : Nat)
    (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (curr p : BitVec width) (xs : List (WordLocW width))
    (pb1 pa1 ib1 i1 : BitVec width)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (c1 : Bool)
    (abstractRun : GenGc.gcMoveData genConf state = state1) (stateOk : state1.ok = true)
    (heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (heapBytesBound : heapLength state.heap * (width / 8) < 2 ^ width)
    (dataBound : conf.lenSize + 2 < width)
    (refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (lenBound : conf.lenSize + 5 ≤ width)
    (wordRun : wordGenGcMoveData conf k
      (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1),
       BitVec.ofNat width state.a,
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)),
       BitVec.ofNat width (state.a + state.n),
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + state.n),
       curr, memory, domain) = (i1, pa1, ib1, pb1, memory1, c1))
    (countBound : heapLength state.h2 + state.n + heapLength state.r4 ≤ k) (invariant : genLenInv state)
    (separated : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (wordHeapParts conf p state xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (refs : (state.r4 ++ state.r3 ++ state.r2 ++ state.r1).all (isRefElement genConf.isRef) = true)
    (length : xs.length = state.n) (good : goodDimindex width) :
    ∃ xs1,
      SetSep.star (SetSep.star (wordHeap curr state1.heap conf) (wordHeapParts conf p state1 xs1)) frame
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      state1.h2 = [] ∧ heapLength state1.heap = heapLength state.heap ∧
      c1 = true ∧ i1 = BitVec.ofNat width state1.a ∧ ib1 = BitVec.ofNat width (state1.a + state1.n) ∧
      state1.n = xs1.length ∧ genLenInv state1 ∧
      heapLength (state1.h1 ++ state1.h2 ++ state1.r4) + state1.n =
        heapLength (state.h1 ++ state.h2 ++ state.r4) + state.n ∧
      pa1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state1.h1 ++ state1.h2)) ∧
      pb1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state1.h1 ++ state1.h2) + state1.n) ∧
      (state1.r4 ++ state1.r3 ++ state1.r2 ++ state1.r1).all (isRefElement genConf.isRef) = true := by
  classical
  induction k using Nat.strong_induction_on generalizing state state1 memory memory1 xs pb1 pa1 ib1 i1 c1 with
  | h k ih =>
    cases pending : state.h2 with
    | nil =>
      simpa only [pending] using wordGenGcMoveData_empty conf genConf k state state1 memory memory1 domain curr p xs
        pb1 pa1 ib1 i1 frame c1 abstractRun stateOk heapBound heapBytesBound dataBound refClass lenBound
        wordRun countBound invariant separated refs length good pending
    | cons head tail =>
      cases head with
      | unused len =>
        cases state with
        | mk old h1 h2 r4 r3 r2 r1 a n ok heap heap0 =>
          simp only at pending
          subst h2
          rw [GenGc.gcMoveData] at abstractRun
          simp only [ite_self] at abstractRun
          subst state1
          contradiction
      | forwardPointer addr value len =>
        cases state with
        | mk old h1 h2 r4 r3 r2 r1 a n ok heap heap0 =>
          simp only at pending
          subst h2
          rw [GenGc.gcMoveData] at abstractRun
          simp only [ite_self] at abstractRun
          subst state1
          contradiction
      | dataElement roots len data =>
        rcases data with ⟨tag, payload⟩
        obtain ⟨header, words, encoded, wordLen, wordBound, info, step⟩ :=
          dataScan_wordStep conf k state roots len tag payload tail curr p
            (BitVec.ofNat width state.a) (BitVec.ofNat width (state.a + state.n))
            (p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + state.n))
            xs memory domain frame pending separated countBound invariant heapBytesBound good dataBound
        cases bit : header.getLsbD 2 with
        | true =>
          have rootsEmpty : roots = [] := by simpa [bit] using info
          subst roots
          obtain ⟨recursive, _, nextFuel⟩ := dataScan_rawAbstract genConf k state state1 len (tag, payload) tail
            pending abstractRun stateOk countBound
          obtain ⟨nextInvariant, nextRefs, nextMemory, nextAccounting⟩ :=
            dataScan_rawState conf genConf state len tag payload tail curr p xs memory domain frame
              pending invariant refs separated
          let next := { state with h1 := state.h1 ++ [HeapElement.dataElement [] len (tag, payload)], h2 := tail }
          have nextCursor := dataScan_nextCursor state [] len (tag, payload) p
          simp only [bit, ↓reduceIte] at step
          rw [step] at wordRun
          rw [wordLen, nextCursor] at wordRun
          have sameLayout : next.h1 ++ next.h2 = state.h1 ++ state.h2 := by
            simp [next, pending, List.append_assoc]
          have recursiveWord : wordGenGcMoveData conf (k - 1)
              (p + wordSemBytesInWord * BitVec.ofNat width (heapLength next.h1),
               BitVec.ofNat width next.a,
               p + wordSemBytesInWord * BitVec.ofNat width (heapLength (next.h1 ++ next.h2)),
               BitVec.ofNat width (next.a + next.n),
               p + wordSemBytesInWord * BitVec.ofNat width (heapLength (next.h1 ++ next.h2) + next.n),
               curr, memory, domain) = (i1, pa1, ib1, pb1, memory1, c1) := by
            simpa only [next, sameLayout] using wordRun
          have positive : 0 < k := by
            have h : 0 < heapLength state.h2 := by rw [pending]; simp [heapLength, elLength]
            omega
          obtain ⟨xsFinal, finalMemory, finalH2, finalHeap, finalOk, finalI, finalIb, finalLen,
            finalInvariant, finalAccounting, finalPa, finalPb, finalRefs⟩ :=
            ih (k - 1) (by omega) next state1 memory memory1 xs pb1 pa1 ib1 i1 c1 recursive stateOk
              heapBound heapBytesBound recursiveWord nextFuel nextInvariant nextMemory nextRefs length
          refine ⟨xsFinal, finalMemory, finalH2, finalHeap, finalOk, finalI, finalIb, finalLen,
            finalInvariant, ?_, finalPa, finalPb, finalRefs⟩
          simpa only [pending] using finalAccounting.trans nextAccounting
        | false =>
          have mapped : words = roots.map (wordAddr conf) := by simpa [bit] using info
          obtain ⟨header2, words2, encoded2, _, _, _, _, read, _, _⟩ :=
            dataScan_headCell conf state roots len tag payload tail curr p xs memory domain frame
              pending good dataBound separated
          have headerEq : header2 = header := by
            have h := congrArg Prod.fst (encoded2.symm.trans encoded)
            simpa using h
          subst header2
          have pointer : (wordSemTheWord (memory (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)))).getLsbD 2 = false := by
            simpa [read, wordSemTheWord] using bit
          generalize move : GenGc.gcMoveList genConf state roots = moveResult
          rcases moveResult with ⟨moved, middle⟩
          obtain ⟨recursive, middleOk, notEmpty, firstEq⟩ :=
            dataScan_abstractStep genConf state middle state1 roots moved len (tag, payload) tail
              pending move abstractRun stateOk
          simp only [bit, Bool.false_eq_true, ↓reduceIte, mapped, List.length_map] at step
          rw [step] at wordRun
          let addr := p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)
          generalize wordMove : wordGenGcMoveList conf
            (addr + wordSemBytesInWord, BitVec.ofNat width roots.length, BitVec.ofNat width state.a,
             p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)),
             BitVec.ofNat width (state.a + state.n),
             p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + state.n),
             curr, memory, domain) = wordMoveResult at wordRun
          rcases wordMoveResult with ⟨nextAddr, midI, midPa, midIb, midPb, midMemory, moveOk⟩
          dsimp only at wordRun
          generalize wordTail : wordGenGcMoveData conf (k - 1)
            (nextAddr, midI, midPa, midIb, midPb, curr, midMemory, domain) = wordTailResult at wordRun
          rcases wordTailResult with ⟨lastI, lastPa, lastIb, lastPb, lastMemory, tailOk⟩
          simp only [Prod.mk.injEq] at wordRun
          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := wordRun
          obtain ⟨header3, left, right, xsMid, encoded3, rootsLen, rootsBound, decoded3, leftEq, rightEq,
            memoryResult, heapLen, moveSuccess, indexEq, limitEq, xsLen, accounting,
            cursorEq, paEq, pbEq, refsOut⟩ :=
            dataScan_moveRoots conf genConf state middle roots moved len tag payload tail curr p
              nextAddr midI midPa midIb midPb xs memory midMemory domain frame moveOk
              pending move middleOk heapBound refClass lenBound dataBound refs separated length good pointer wordMove
          subst moveOk
          simp only [Bool.true_and]
          let next := { middle with h1 := middle.h1 ++ [HeapElement.dataElement moved len (tag, payload)], h2 := middle.h2.drop 1, ok := true }
          have nextMemory := dataScan_nextMemory conf genConf state middle roots moved len tag payload tail left right
            header3 curr p midPa midPb xs xsMid true midMemory domain frame pending move encoded3 rootsLen rootsBound
            decoded3 leftEq rightEq paEq pbEq accounting length xsLen memoryResult
          obtain ⟨nextInvariant, h1Eq, _, nextRefs, nextAccounting⟩ :=
            dataScan_advanceInvariant genConf state middle roots moved len (tag, payload) tail left right true
              pending move middleOk leftEq rightEq accounting invariant refs refsOut
          have tailFuel := dataScan_nextFuel k state middle roots len (tag, payload) tail left right
            pending leftEq rightEq accounting countBound
          obtain ⟨middleH1, _, _, _⟩ := genMoveList_const genConf roots moved state middle move
          obtain ⟨nextCursor, nextPa, nextPb⟩ := dataScan_nextPointers state middle roots moved len (tag, payload)
            tail left right p nextAddr midPa midPb xs.length true pending middleH1 leftEq rootsLen accounting length
            cursorEq paEq pbEq
          have nextRun : GenGc.gcMoveData genConf next = state1 := by
            simpa [next, middleOk, notEmpty, firstEq] using recursive
          rw [nextCursor, indexEq, limitEq, nextPa, nextPb] at wordTail
          have recursiveWord : wordGenGcMoveData conf (k - 1)
              (p + wordSemBytesInWord * BitVec.ofNat width (heapLength next.h1),
               BitVec.ofNat width next.a,
               p + wordSemBytesInWord * BitVec.ofNat width (heapLength (next.h1 ++ next.h2)),
               BitVec.ofNat width (next.a + next.n),
               p + wordSemBytesInWord * BitVec.ofNat width (heapLength (next.h1 ++ next.h2) + next.n),
               curr, midMemory, domain) = (lastI, lastPa, lastIb, lastPb, lastMemory, tailOk) := by
            simpa only [next] using wordTail
          have positive : 0 < k := by
            have h : 0 < heapLength state.h2 := by rw [pending]; simp [heapLength, elLength]
            omega
          obtain ⟨xsFinal, finalMemory, finalH2, finalHeap, finalOk, finalI, finalIb, finalLen,
            finalInvariant, finalAccounting, finalPa, finalPb, finalRefs⟩ :=
            ih (k - 1) (by omega) next state1 midMemory lastMemory xsMid lastPb lastPa lastIb lastI tailOk
              nextRun stateOk (by simpa [next, heapLen] using heapBound)
              (by simpa [next, heapLen] using heapBytesBound) recursiveWord tailFuel nextInvariant
              nextMemory nextRefs xsLen.symm
          refine ⟨xsFinal, finalMemory, finalH2, ?_, finalOk, finalI, finalIb, finalLen,
            finalInvariant, ?_, finalPa, finalPb, finalRefs⟩
          · simpa [next, heapLen] using finalHeap
          · simpa only [pending] using finalAccounting.trans nextAccounting

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
