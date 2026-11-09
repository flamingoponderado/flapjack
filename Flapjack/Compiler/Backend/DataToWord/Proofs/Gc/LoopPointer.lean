import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.LoopClaim
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PayloadSwap

/-! Pointer-payload branch of the copying-collector scan induction. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.CopyingGc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private instance {α : Type} : Std.Associative (SetSep.star (α := α)) :=
  ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩

private instance {α : Type} : Std.Commutative (SetSep.star (α := α)) :=
  ⟨SetSep.starComm⟩

private theorem exposeFields {α : Type} (old frame scanned pending head fields free : (α → Prop) → Prop) :
    SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star old frame) scanned) pending)
      (SetSep.star head fields)) free =
    SetSep.star (SetSep.star (SetSep.star old free) fields)
      (SetSep.star head (SetSep.star scanned (SetSep.star pending frame))) := by
  simp only [← SetSep.starAssoc]
  rw [SetSep.starComm fields free, star_swap_first head free, star_swap_first pending free,
    star_swap_first scanned free, star_swap_first frame free, SetSep.starComm head fields,
    star_swap_first pending fields, star_swap_first scanned fields, star_swap_first frame fields,
    SetSep.starComm pending head, star_swap_first scanned head, star_swap_first frame head,
    star_swap_first frame scanned, SetSep.starComm frame pending]

/-- The pointer-payload branch of the source scan induction. The recursive
premise is the complete source claim for the result of moving the payload. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gc_move_loop_thm"
  (words_as_type_indexed_bitvec)]
theorem scanClaim_pointer {width : Nat} [NeZero width] (conf : Config)
    (scanned pending : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (addresses : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width)) (a n : Nat)
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (limit : Nat)
    (ih : ∀ (moved : List (HeapAddress (WordLocW width)))
      (added : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
      (a' n' : Nat) (heap' : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))),
      gcMoveList (addresses, [], a, n, heap, true, limit) = (moved, added, a', n', heap', true) →
      ScanClaim conf (scanned ++ [.dataElement moved len (tag, payload)]) (pending ++ added)
        a' n' heap' true limit)
    (h11 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (a1 n1 : Nat)
    (heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (i1 pa1 : BitVec width) (m1 : BitVec width → WordLocW width) (c1 : Bool)
    (xs : List (WordLocW width)) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (m : BitVec width → WordLocW width) (k : Nat) (curr new : BitVec width) (dm : BitVec width → Bool)
    (run : gcMoveLoop (scanned, .dataElement addresses len (tag, payload) :: pending,
      a, n, heap, true, limit) = (h11, a1, n1, heap1, true))
    (heapBound : heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (bytesBound : heapLength heap * (width / 8) < 2 ^ width) (lenBound : conf.lenSize + 2 < width)
    (separated : SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap conf)
      (wordHeap new (scanned ++ .dataElement addresses len (tag, payload) :: pending) conf))
      (Misc.wordList (new + BitVec.ofNat width (heapLength (scanned ++ .dataElement addresses len (tag, payload) :: pending)) *
        wordSemBytesInWord) xs)) frame (SetSep.fun2Set (m, fun address => dm address = true)))
    (steps : limit - heapLength scanned ≤ k) (limitEq : limit = heapLength heap) (good : goodDimindex width)
    (wordRun : wordGcMoveLoop k conf (new + BitVec.ofNat width (heapLength scanned) * wordSemBytesInWord,
      BitVec.ofNat width a,
      new + BitVec.ofNat width (heapLength (scanned ++ .dataElement addresses len (tag, payload) :: pending)) *
        wordSemBytesInWord, curr, m, dm, true) = (i1, pa1, m1, c1))
    (length : xs.length = n)
    (pointer : (wordSemTheWord (m (new + BitVec.ofNat width (heapLength scanned) * wordSemBytesInWord))).getLsbD 2 = false) :
    ∃ xs1,
      SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap1 conf) (wordHeap new h11 conf))
        (Misc.wordList pa1 xs1)) frame (SetSep.fun2Set (m1, fun address => dm address = true)) ∧
      heapLength heap1 = heapLength heap ∧ c1 = true ∧ i1 = BitVec.ofNat width a1 ∧ n1 = xs1.length ∧
      pa1 = new + wordSemBytesInWord * BitVec.ofNat width (heapLength h11) := by
  obtain ⟨header, words, encoded, wordLen, wordBound, decoded, info, read, valid, step⟩ :=
    scanData_headStep conf scanned pending addresses len tag payload a n limit heap true h11 a1 n1 heap1
      k curr new xs m dm frame run bytesBound lenBound separated steps limitEq good
  have pointerHeader : header.getLsbD 2 = false := by simpa [read, wordSemTheWord] using pointer
  have mapped : words = addresses.map (wordAddr conf) := by simpa [pointerHeader] using info
  have pendingBound : heapLength (scanned ++ .dataElement addresses len (tag, payload) :: pending) ≤ limit := by
    by_contra bad
    have over : limit < heapLength (scanned ++ .dataElement addresses len (tag, payload) :: pending) := by omega
    simp [gcMoveLoop, over] at run
  have positive : 0 < k := scanFuel_pos scanned pending (.dataElement addresses len (tag, payload))
    a n limit heap true h11 a1 n1 heap1 k run steps
  generalize moveEq : gcMoveList (addresses, [], a, n, heap, true, limit) = moveResult
  rcases moveResult with ⟨moved, added, a', n', heap', movedOk⟩
  have prefixMove : gcMoveList (addresses, .dataElement addresses len (tag, payload) :: pending,
      a, n, heap, true, limit) =
      (moved, (.dataElement addresses len (tag, payload) :: pending) ++ added, a', n', heap', movedOk) := by
    rw [gcMoveList_alt addresses (.dataElement addresses len (tag, payload) :: pending)
      a n heap true limit () () () () () (), moveEq]
  have recursiveRun : gcMoveLoop (scanned ++ [.dataElement moved len (tag, payload)], pending ++ added,
      a', n', heap', movedOk, limit) = (h11, a1, n1, heap1, true) := by
    simpa [gcMoveLoop, Nat.not_lt.mpr pendingBound, prefixMove] using run
  have movedOkEq : movedOk = true :=
    gcMoveLoop_ok (scanned ++ [.dataElement moved len (tag, payload)]) (pending ++ added) heap' heap1
      a' n' limit a1 n1 movedOk h11 recursiveRun
  subst movedOk
  simp only [pointerHeader, Bool.false_eq_true, ↓reduceIte, decoded] at step
  rw [step] at wordRun
  let pb := new + BitVec.ofNat width (heapLength scanned) * wordSemBytesInWord
  let pa := new + BitVec.ofNat width (heapLength (scanned ++ .dataElement addresses len (tag, payload) :: pending)) *
    wordSemBytesInWord
  have rootLen : addresses.length = len := by simpa [mapped] using wordLen
  have positiveWidth : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  have rootBound : addresses.length < 2 ^ width := by
    have exponent : width - 4 < width := by omega
    have powLt : 2 ^ (width - 4) < 2 ^ width := Nat.pow_lt_pow_right (by decide : 1 < 2) exponent
    omega
  have separated' : SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap conf)
        (wordHeap new (scanned ++ .dataElement addresses len (tag, payload) :: pending) conf))
        (Misc.wordList pa xs)) frame (SetSep.fun2Set (m, fun address => dm address = true)) := separated
  obtain ⟨header', words', encoded', _, _, _, _, _, _, cell⟩ :=
    scanDataCell conf scanned pending addresses len tag payload curr new pa xs heap m dm frame good lenBound separated'
  rw [encoded] at encoded'
  simp only [Prod.mk.injEq, and_true] at encoded'
  obtain ⟨rfl, rfl⟩ := encoded'
  simp only [Misc.wordList] at cell
  rw [exposeFields] at cell
  have listSep : SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap conf) (Misc.wordList pa xs))
      (Misc.wordList (pb + wordSemBytesInWord) (addresses.map (wordAddr conf))))
      (SetSep.star (SetSep.one (pb, WordLocW.word header))
        (SetSep.star (wordHeap new scanned conf)
          (SetSep.star (wordHeap (new + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength scanned) +
            StackRemove.bytesInWord width * BitVec.ofNat width (len + 1)) pending conf) frame)))
      (SetSep.fun2Set (m, fun address => dm address = true)) := by
    simpa only [pb, wordSemBytesInWord, StackRemove.bytesInWord, BitVec.mul_comm, mapped] using cell
  generalize wordListEq : wordGcMoveList conf (pb + wordSemBytesInWord,
    BitVec.ofNat width addresses.length, BitVec.ofNat width a, pa, curr, m, dm) = wordListResult at wordRun
  rcases wordListResult with ⟨pb', i', pa', m', ok'⟩
  have wordListEq' : wordGcMoveList conf
      (new + BitVec.ofNat width (heapLength scanned) * wordSemBytesInWord + wordSemBytesInWord,
        BitVec.ofNat width addresses.length, BitVec.ofNat width a,
        new + BitVec.ofNat width (heapLength (scanned ++ .dataElement addresses len (tag, payload) :: pending)) *
          wordSemBytesInWord, curr, m, dm) = (pb', i', pa', m', ok') := wordListEq
  simp only [mapped, List.length_map, wordListEq'] at wordRun
  obtain ⟨xs', afterList, heapLen, listOk, indexEq, freeEq, pbEq, paEq⟩ :=
    wordGcMoveList_thm conf addresses a n heap limit pa moved added a' n' heap' pa' m m' xs i' ok'
      _ (pb + wordSemBytesInWord) pb' curr dm moveEq heapBound wordListEq listSep length rootBound
  have movedLen : moved.length = addresses.length :=
    gcMoveList_imp_length addresses moved [] added heap heap' a n limit a' n' true true moveEq
  have encodedOriginal : wordPayload addresses addresses.length tag payload conf =
      (header, addresses.map (wordAddr conf), true) := by
    simpa only [rootLen, ← mapped] using encoded
  have encodedMoved : wordPayload moved len tag payload conf =
      (header, moved.map (wordAddr conf), true) := by
    simpa only [rootLen] using wordPayload_swap addresses moved tag payload conf header encodedOriginal movedLen
  have movedWordLen : (moved.map (wordAddr conf)).length = words.length := by
    simpa only [List.length_map, movedLen] using congrArg List.length mapped.symm
  have elementEq : wordEl pb (.dataElement moved len (tag, payload)) conf =
      SetSep.star (SetSep.one (pb, WordLocW.word header))
        (Misc.wordList (pb + StackRemove.bytesInWord width) (moved.map (wordAddr conf))) := by
    funext cellHeap
    apply propext
    simp only [wordEl, encodedMoved, StackRemove.WordListExists.starCond, Misc.wordList, movedWordLen,
      wordBound, decoded, and_self, and_true]
  have scanLength : heapLength (scanned ++ [.dataElement moved len (tag, payload)]) =
      heapLength scanned + (len + 1) := by
    rw [heapLength_append]
    simp [heapLength, elLength]
  have originalLength : heapLength (scanned ++ .dataElement addresses len (tag, payload) :: pending) =
      heapLength scanned + (len + 1) + heapLength pending := by
    rw [heapLength_append]
    simp [heapLength, elLength, Nat.add_assoc]
  have nextLength : heapLength ((scanned ++ [.dataElement moved len (tag, payload)]) ++ (pending ++ added)) =
      heapLength (scanned ++ .dataElement addresses len (tag, payload) :: pending) + heapLength added := by
    simp [heapLength, List.map_append, List.sum_append, elLength, Nat.add_assoc]
  have nextPb : pb' = new + BitVec.ofNat width
      (heapLength (scanned ++ [.dataElement moved len (tag, payload)])) * wordSemBytesInWord := by
    rw [pbEq, scanLength, rootLen]
    dsimp only [pb]
    simp only [BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]
    ac_rfl
  have nextPa : pa' = new + BitVec.ofNat width
      (heapLength ((scanned ++ [.dataElement moved len (tag, payload)]) ++ (pending ++ added))) *
        wordSemBytesInWord := by
    rw [paEq, nextLength]
    dsimp only [pa]
    simp only [BitVec.ofNat_add, BitVec.add_mul]
    ac_rfl
  have nextSteps : limit - heapLength (scanned ++ [.dataElement moved len (tag, payload)]) ≤ k - 1 := by
    rw [scanLength]
    omega
  have newBound : heapLength heap' ≤ 2 ^ width / 2 ^ shiftLength conf := by simpa [heapLen] using heapBound
  have newBytesBound : heapLength heap' * (width / 8) < 2 ^ width := by simpa [heapLen] using bytesBound
  have recWordRun : wordGcMoveLoop (k - 1) conf
      (new + BitVec.ofNat width (heapLength (scanned ++ [.dataElement moved len (tag, payload)])) * wordSemBytesInWord,
        BitVec.ofNat width a', new + BitVec.ofNat width
          (heapLength ((scanned ++ [.dataElement moved len (tag, payload)]) ++ (pending ++ added))) * wordSemBytesInWord,
        curr, m', dm, true) = (i1, pa1, m1, c1) := by
    simpa only [nextPb, nextPa, indexEq, listOk] using wordRun
  have tailPa : pa = new + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength scanned) +
      StackRemove.bytesInWord width * BitVec.ofNat width (len + 1) +
      StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pending) := by
    dsimp only [pa]
    rw [originalLength]
    simp only [wordSemBytesInWord, StackRemove.bytesInWord, BitVec.ofNat_add, BitVec.mul_add,
      BitVec.add_mul]
    ac_rfl
  have heapDecomp : wordHeap new
      ((scanned ++ [.dataElement moved len (tag, payload)]) ++ (pending ++ added)) conf =
    SetSep.star (wordHeap new scanned conf)
      (SetSep.star (wordEl pb (.dataElement moved len (tag, payload)) conf)
        (SetSep.star (wordHeap
          (new + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength scanned) +
            StackRemove.bytesInWord width * BitVec.ofNat width (len + 1)) pending conf)
          (wordHeap pa added conf))) := by
    simp only [List.append_assoc, List.singleton_append, wordHeapAppend, wordHeap, elLength]
    rw [tailPa]
    simp only [pb, wordSemBytesInWord, StackRemove.bytesInWord, BitVec.mul_comm]
  have reassembled : SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap' conf)
      (SetSep.star (wordHeap new scanned conf)
        (SetSep.star (SetSep.star (SetSep.one (pb, WordLocW.word header))
            (Misc.wordList (pb + wordSemBytesInWord) (moved.map (wordAddr conf))))
          (SetSep.star (wordHeap (new + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength scanned) +
            StackRemove.bytesInWord width * BitVec.ofNat width (len + 1)) pending conf)
            (wordHeap pa added conf))))) (Misc.wordList pa' xs')) frame
      (SetSep.fun2Set (m', fun address => dm address = true)) := by
    have rearrange : SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap' conf)
        (SetSep.star (wordHeap new scanned conf)
          (SetSep.star (SetSep.star (SetSep.one (pb, WordLocW.word header))
              (Misc.wordList (pb + wordSemBytesInWord) (moved.map (wordAddr conf))))
            (SetSep.star (wordHeap (new + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength scanned) +
              StackRemove.bytesInWord width * BitVec.ofNat width (len + 1)) pending conf)
              (wordHeap pa added conf))))) (Misc.wordList pa' xs')) frame =
      SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap' conf) (wordHeap pa added conf))
        (Misc.wordList pa' xs')) (Misc.wordList (pb + wordSemBytesInWord) (moved.map (wordAddr conf))))
        (SetSep.star (SetSep.one (pb, WordLocW.word header))
          (SetSep.star (wordHeap new scanned conf)
            (SetSep.star (wordHeap (new + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength scanned) +
              StackRemove.bytesInWord width * BitVec.ofNat width (len + 1)) pending conf) frame))) := by
      ac_rfl
    rw [rearrange]
    exact afterList
  have recSeparated : SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap' conf)
      (wordHeap new ((scanned ++ [.dataElement moved len (tag, payload)]) ++ (pending ++ added)) conf))
      (Misc.wordList (new + BitVec.ofNat width
        (heapLength ((scanned ++ [.dataElement moved len (tag, payload)]) ++ (pending ++ added))) *
          wordSemBytesInWord) xs')) frame (SetSep.fun2Set (m', fun address => dm address = true)) := by
    rw [← nextPa, heapDecomp, elementEq]
    exact reassembled
  have limitEq' : limit = heapLength heap' := by simpa [heapLen] using limitEq
  obtain ⟨resultXs, resultSep, resultHeap, resultOk, resultIndex, resultLen, resultPa⟩ :=
    ih moved added a' n' heap' moveEq h11 a1 n1 heap1 i1 pa1 m1 c1 xs' frame m' (k - 1) curr new dm
      recursiveRun rfl newBound newBytesBound lenBound recSeparated nextSteps limitEq' good recWordRun freeEq.symm
  exact ⟨resultXs, resultSep, resultHeap.trans heapLen, resultOk, resultIndex, resultLen, resultPa⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
