import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalRefs
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.LoopCell

/-! Major collector data-scan simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private instance {α : Type} : Std.Associative (SetSep.star (α := α)) :=
  ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩
private instance {α : Type} : Std.Commutative (SetSep.star (α := α)) := ⟨SetSep.starComm⟩

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

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
