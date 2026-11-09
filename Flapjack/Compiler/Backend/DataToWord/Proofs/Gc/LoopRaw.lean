module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.LoopClaim

@[expose] public section

/-! Raw-payload branch of the copying-collector scan induction. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.CopyingGc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- The raw-payload branch of the source scan induction, with its induction
hypothesis stated as the complete source-shaped claim for the recursive scan.
The branch selector is the original concrete header bit. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gc_move_loop_thm"
  (words_as_type_indexed_bitvec)]
theorem scanClaim_raw {width : Nat} [NeZero width] (conf : Config)
    (scanned pending : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (addresses : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width)) (a n : Nat)
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (limit : Nat)
    (ih : ScanClaim conf (scanned ++ [.dataElement addresses len (tag, payload)]) pending a n heap true limit)
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
    (raw : (wordSemTheWord (m (new + BitVec.ofNat width (heapLength scanned) * wordSemBytesInWord))).getLsbD 2 = true) :
    ∃ xs1,
      SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap1 conf) (wordHeap new h11 conf))
        (Misc.wordList pa1 xs1)) frame (SetSep.fun2Set (m1, fun address => dm address = true)) ∧
      heapLength heap1 = heapLength heap ∧ c1 = true ∧ i1 = BitVec.ofNat width a1 ∧ n1 = xs1.length ∧
      pa1 = new + wordSemBytesInWord * BitVec.ofNat width (heapLength h11) := by
  obtain ⟨header, words, encoded, wordLen, wordBound, decoded, info, read, valid, step⟩ :=
    scanData_headStep conf scanned pending addresses len tag payload a n limit heap true h11 a1 n1 heap1
      k curr new xs m dm frame run bytesBound lenBound separated steps limitEq good
  have rawHeader : header.getLsbD 2 = true := by simpa [read, wordSemTheWord] using raw
  have emptyAddresses : addresses = [] := by simpa [rawHeader] using info
  subst addresses
  have pendingBound : heapLength (scanned ++ .dataElement [] len (tag, payload) :: pending) ≤ limit := by
    by_contra bad
    have over : limit < heapLength (scanned ++ .dataElement [] len (tag, payload) :: pending) := by omega
    simp [gcMoveLoop, over] at run
  have positive : 0 < k := scanFuel_pos scanned pending (.dataElement [] len (tag, payload))
    a n limit heap true h11 a1 n1 heap1 k run steps
  have recursiveRun : gcMoveLoop (scanned ++ [.dataElement [] len (tag, payload)], pending,
      a, n, heap, true, limit) = (h11, a1, n1, heap1, true) := by
    simpa [gcMoveLoop, Nat.not_lt.mpr pendingBound, gcMoveList] using run
  simp only [rawHeader, ↓reduceIte, decoded, wordLen] at step
  rw [step] at wordRun
  have scanLength : heapLength (scanned ++ [.dataElement [] len (tag, payload)]) =
      heapLength scanned + (len + 1) := by
    rw [heapLength_append]
    simp [heapLength, elLength]
  have scanAddr : new + BitVec.ofNat width (heapLength scanned) * wordSemBytesInWord +
      (BitVec.ofNat width len + 1) * wordSemBytesInWord =
      new + BitVec.ofNat width (heapLength (scanned ++ [.dataElement [] len (tag, payload)])) *
        wordSemBytesInWord := by
    rw [scanLength]
    simp only [BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]
    ac_rfl
  rw [scanAddr] at wordRun
  have nextSteps : limit - heapLength (scanned ++ [.dataElement [] len (tag, payload)]) ≤ k - 1 := by
    rw [scanLength]
    omega
  apply ih h11 a1 n1 heap1 i1 pa1 m1 c1 xs frame m (k - 1) curr new dm recursiveRun rfl
    heapBound bytesBound lenBound
  · simpa [List.append_assoc] using separated
  · exact nextSteps
  · exact limitEq
  · exact good
  · simpa [List.append_assoc] using wordRun
  · exact length

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
