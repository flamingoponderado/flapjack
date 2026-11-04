import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.LoopRaw
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.LoopPointer

/-! Full abstract-to-word copying-collector scan simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.CopyingGc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private theorem scanClaim_all {width : Nat} [NeZero width] (conf : Config) :
    ∀ input : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))) ×
      List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))) × Nat × Nat ×
      List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))) × Bool × Nat,
      ScanClaim conf input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2.1
        input.2.2.2.2.2.1 input.2.2.2.2.2.2 := by
  intro input
  induction input using gcMoveLoop.induct with
  | case1 scanned a n heap ok limit =>
    exact scanClaim_empty conf scanned a n heap ok limit
  | case2 scanned head pending a n heap ok limit over =>
    intro h11 a1 n1 heap1 i1 pa1 m1 c1 xs frame m k curr new dm run
    cases head <;> simp [gcMoveLoop, over] at run
  | case3 scanned pending a n heap ok limit addresses len payload roots copied a' n' heap' ok' bound move ok2 ih =>
    rcases payload with ⟨tag, payload⟩
    intro h11 a1 n1 heap1 i1 pa1 m1 c1 xs frame m k curr new dm run okTrue heapBound bytesBound
      lenBound separated steps limitEq good wordRun length
    dsimp only at run okTrue heapBound bytesBound separated steps limitEq wordRun length ⊢
    subst ok
    generalize emptyMove : gcMoveList (addresses, [], a, n, heap, true, limit) = emptyResult
    rcases emptyResult with ⟨moved, added, aNext, nNext, heapNext, statusNext⟩
    rw [gcMoveList_alt addresses (.dataElement addresses len (tag, payload) :: pending)
      a n heap true limit () () () () () (), emptyMove] at move
    simp only [Prod.mk.injEq] at move
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := move
    simp only [List.cons_append, List.drop, ok2, List.head?, decide_true, Bool.and_true] at ih
    have ihFamily : ∀ (moved1 : List (HeapAddress (WordLocW width)))
        (added1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
        (aNext1 nNext1 : Nat) (heapNext1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))),
        gcMoveList (addresses, [], a, n, heap, true, limit) =
          (moved1, added1, aNext1, nNext1, heapNext1, true) →
        ScanClaim conf (scanned ++ [.dataElement moved1 len (tag, payload)]) (pending ++ added1)
          aNext1 nNext1 heapNext1 true limit := by
      intro moved1 added1 aNext1 nNext1 heapNext1 move1
      rw [emptyMove] at move1
      simp only [Prod.mk.injEq] at move1
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := move1
      exact ih
    cases rawEq : (wordSemTheWord (m (new + BitVec.ofNat width (heapLength scanned) * wordSemBytesInWord))).getLsbD 2 with
    | false =>
      exact scanClaim_pointer conf scanned pending addresses len tag payload a n heap limit ihFamily
        h11 a1 n1 heap1 i1 pa1 m1 c1 xs frame m k curr new dm run heapBound bytesBound lenBound
        separated steps limitEq good wordRun length rawEq
    | true =>
      obtain ⟨header, words, encoded, wordLen, wordBound, decoded, info, read, valid, step⟩ :=
        scanData_headStep conf scanned pending addresses len tag payload a n limit heap true h11 a1 n1 heap1
          k curr new xs m dm frame run bytesBound lenBound separated steps limitEq good
      have rawHeader : header.getLsbD 2 = true := by simpa [read, wordSemTheWord] using rawEq
      have empty : addresses = [] := by simpa [rawHeader] using info
      subst addresses
      have moveNil : gcMoveList ([], [], a, n, heap, true, limit) =
          ([], [], a, n, heap, true) := by simp [gcMoveList]
      have rawIH : ScanClaim conf (scanned ++ [.dataElement [] len (tag, payload)]) pending a n heap true limit := by
        simpa only [List.append_nil] using ihFamily [] [] a n heap moveNil
      simpa only [List.append_nil] using
        scanClaim_raw conf scanned pending [] len tag payload a n heap limit rawIH
          h11 a1 n1 heap1 i1 pa1 m1 c1 xs frame m k curr new dm run heapBound bytesBound lenBound
          separated steps limitEq good wordRun length rawEq
  | case4 scanned head pending a n heap ok limit bound notData =>
    intro h11 a1 n1 heap1 i1 pa1 m1 c1 xs frame m k curr new dm run
    cases head <;> simp_all [gcMoveLoop]

/-- Complete copying-collector scan simulation, assembled by the original loop induction. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gc_move_loop_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGcMoveLoop_thm {width : Nat} [NeZero width] (conf : Config)
    (scanned pending : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a n : Nat) (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (c0 : Bool) (limit : Nat)
    (h11 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (a1 n1 : Nat)
    (heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (i1 pa1 : BitVec width) (m1 : BitVec width → WordLocW width) (c1 : Bool)
    (xs : List (WordLocW width)) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (m : BitVec width → WordLocW width) (k : Nat) (curr new : BitVec width)
    (dm : BitVec width → Bool)
    (abstractRun : gcMoveLoop (scanned, pending, a, n, heap, c0, limit) = (h11, a1, n1, heap1, true))
    (cTrue : c0 = true)
    (heapBound : heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (byteBound : heapLength heap * (width / 8) < 2 ^ width)
    (lenBound : conf.lenSize + 2 < width)
    (separated : SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap conf)
      (wordHeap new (scanned ++ pending) conf))
      (Misc.wordList (new + BitVec.ofNat width (heapLength (scanned ++ pending)) * wordSemBytesInWord) xs)) frame
      (SetSep.fun2Set (m, fun address => dm address = true)))
    (steps : limit - heapLength scanned ≤ k) (limitEq : limit = heapLength heap)
    (good : goodDimindex width)
    (wordRun : wordGcMoveLoop k conf (new + BitVec.ofNat width (heapLength scanned) * wordSemBytesInWord,
      BitVec.ofNat width a, new + BitVec.ofNat width (heapLength (scanned ++ pending)) * wordSemBytesInWord,
      curr, m, dm, true) = (i1, pa1, m1, c1)) (length : xs.length = n) :
    ∃ xs1,
      SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap1 conf) (wordHeap new h11 conf))
        (Misc.wordList pa1 xs1)) frame (SetSep.fun2Set (m1, fun address => dm address = true)) ∧
      heapLength heap1 = heapLength heap ∧ c1 = true ∧ i1 = BitVec.ofNat width a1 ∧ n1 = xs1.length ∧
      pa1 = new + wordSemBytesInWord * BitVec.ofNat width (heapLength h11) := by
  exact scanClaim_all conf (scanned, pending, a, n, heap, c0, limit)
    h11 a1 n1 heap1 i1 pa1 m1 c1 xs frame m k curr new dm abstractRun cTrue
    heapBound byteBound lenBound separated steps limitEq good wordRun length

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
