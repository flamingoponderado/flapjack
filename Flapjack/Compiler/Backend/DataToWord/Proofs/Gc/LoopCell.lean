import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.LoopArithmetic
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MoveBlock

/-! Expose the next copied heap element for the collector scan. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- The original separated scan state determines the next data-element
header, its valid payload and its concrete memory-domain membership. The
complete remaining heap, free list and external frame are retained for the
two branches of the scan. This is Flapjack proof factoring. -/
theorem scanDataCell {width : Nat} [NeZero width] (conf : Config)
    (scanned pending : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (addresses : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width)) (curr new pa : BitVec width) (xs : List (WordLocW width))
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (good : goodDimindex width) (lenBound : conf.lenSize + 2 < width)
    (separated : SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap conf)
        (wordHeap new (scanned ++ .dataElement addresses len (tag, payload) :: pending) conf))
        (Misc.wordList pa xs)) frame (SetSep.fun2Set (memory, fun address => domain address = true))) :
    ∃ (header : BitVec width) (words : List (WordLocW width)),
      wordPayload addresses len tag payload conf = (header, words, true) ∧
      words.length = len ∧ words.length < 2 ^ (width - 4) ∧
      decodeLength conf header = BitVec.ofNat width words.length ∧
      (if header.getLsbD 2 then addresses = [] else words = addresses.map (wordAddr conf)) ∧
      memory (new + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength scanned)) = .word header ∧
      domain (new + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength scanned)) = true ∧
      SetSep.star (SetSep.star
        (SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap conf) frame) (wordHeap new scanned conf))
          (wordHeap (new + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength scanned) +
            StackRemove.bytesInWord width * BitVec.ofNat width (len + 1)) pending conf))
        (Misc.wordList (new + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength scanned))
          (.word header :: words))) (Misc.wordList pa xs)
        (SetSep.fun2Set (memory, fun address => domain address = true)) := by
  have arranged : SetSep.star
      (SetSep.star (wordHeap new (scanned ++ .dataElement addresses len (tag, payload) :: pending) conf)
        (Misc.wordList pa xs)) (SetSep.star (wordHeap curr heap conf) frame)
      (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    simp only [← SetSep.starAssoc] at separated ⊢
    rw [star_swap_first (wordHeap curr heap conf)
      (wordHeap new (scanned ++ .dataElement addresses len (tag, payload) :: pending) conf),
      star_swap_first (wordHeap curr heap conf) (Misc.wordList pa xs)] at separated
    exact separated
  obtain ⟨header, words, encoded, wordLen, wordBound, decoded, cell⟩ :=
    wordHeap_dataCell conf scanned pending addresses len tag payload new pa xs memory domain
      (SetSep.star (wordHeap curr heap conf) frame) arranged
  have info := (wordPayloadTrueImp addresses len tag payload conf header words) ⟨encoded, good, lenBound⟩
  have read : memory (new + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength scanned)) =
        .word header ∧
      domain (new + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength scanned)) = true := by
    rcases cell with ⟨sourceAndFrame, free, outer, sourceAndFrameAssert, _⟩
    rcases sourceAndFrameAssert with ⟨rest, source, inner, _, sourceAssert⟩
    have entry := StackRemove.StackHeap.wordListNth
      (new + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength scanned))
      (.word header :: words) source 0 (by simp) sourceAssert
    have graph : SetSep.fun2Set (memory, fun address => domain address = true)
        (new + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength scanned), .word header) := by
      rw [← outer.1, ← inner.1]
      exact Or.inl (Or.inr (by simpa using entry))
    exact (SetSep.fun2SetThm memory _ _ _).mp graph
  exact ⟨header, words, encoded, wordLen, wordBound, decoded, info.2, read.1, read.2, cell⟩

/-- With a distinct scan address, remaining fuel and a valid concrete header,
unfolding the actual collector loop yields its raw-payload and pointer-payload
branches. This is Flapjack proof factoring of the original loop equation. -/
theorem scanWord_step {width : Nat} [NeZero width] (conf : Config) (k : Nat)
    (pb i pa old : BitVec width) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (header : BitVec width)
    (different : pb ≠ pa) (positive : 0 < k) (read : memory pb = .word header)
    (valid : domain pb = true) :
    wordGcMoveLoop k conf (pb, i, pa, old, memory, domain, true) =
      if header.getLsbD 2 then
        wordGcMoveLoop (k - 1) conf
          (pb + (decodeLength conf header + 1) * wordSemBytesInWord, i, pa, old, memory, domain, true)
      else
        let (pb1, i1, pa1, memory1, c1) := wordGcMoveList conf
          (pb + wordSemBytesInWord, decodeLength conf header, i, pa, old, memory, domain)
        wordGcMoveLoop (k - 1) conf (pb1, i1, pa1, old, memory1, domain, c1) := by
  rw [wordGcMoveLoop]
  simp [different, Nat.ne_of_gt positive, read, valid, wordSemIsWordLoc, wordSemTheWord]

/-- In the nonempty data-element branch of a successful abstract scan, the
original scan hypotheses determine a valid concrete header and force the
actual word loop to take the corresponding header-directed step. No concrete
evaluation or pointer-separation fact is assumed. This is Flapjack proof
factoring used to assemble the scan induction. -/
theorem scanData_headStep {width : Nat} [NeZero width] (conf : Config)
    (scanned pending : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (addresses : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width)) (a n limit : Nat)
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (status : Bool)
    (result : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a1 n1 : Nat) (heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (k : Nat) (curr new : BitVec width) (xs : List (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (run : CopyingGc.gcMoveLoop (scanned, .dataElement addresses len (tag, payload) :: pending,
      a, n, heap, status, limit) = (result, a1, n1, heap1, true))
    (bytesBound : heapLength heap * (width / 8) < 2 ^ width)
    (lenBound : conf.lenSize + 2 < width)
    (separated : SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap conf)
      (wordHeap new (scanned ++ .dataElement addresses len (tag, payload) :: pending) conf))
      (Misc.wordList (new + BitVec.ofNat width (heapLength (scanned ++ .dataElement addresses len (tag, payload) :: pending)) *
        wordSemBytesInWord) xs)) frame (SetSep.fun2Set (memory, fun address => domain address = true)))
    (steps : limit - heapLength scanned ≤ k) (limitEq : limit = heapLength heap) (good : goodDimindex width) :
    ∃ (header : BitVec width) (words : List (WordLocW width)),
      wordPayload addresses len tag payload conf = (header, words, true) ∧
      words.length = len ∧ words.length < 2 ^ (width - 4) ∧
      decodeLength conf header = BitVec.ofNat width words.length ∧
      (if header.getLsbD 2 then addresses = [] else words = addresses.map (wordAddr conf)) ∧
      let pb := new + BitVec.ofNat width (heapLength scanned) * wordSemBytesInWord
      let pa := new + BitVec.ofNat width (heapLength (scanned ++ .dataElement addresses len (tag, payload) :: pending)) *
        wordSemBytesInWord
      memory pb = .word header ∧ domain pb = true ∧
      wordGcMoveLoop k conf (pb, BitVec.ofNat width a, pa, curr, memory, domain, true) =
        if header.getLsbD 2 then
          wordGcMoveLoop (k - 1) conf
            (pb + (decodeLength conf header + 1) * wordSemBytesInWord,
              BitVec.ofNat width a, pa, curr, memory, domain, true)
        else
          let (pb1, i1, pa1, memory1, c1) := wordGcMoveList conf
            (pb + wordSemBytesInWord, decodeLength conf header, BitVec.ofNat width a, pa, curr, memory, domain)
          wordGcMoveLoop (k - 1) conf (pb1, i1, pa1, curr, memory1, domain, c1) := by
  let pa := new + BitVec.ofNat width (heapLength (scanned ++ .dataElement addresses len (tag, payload) :: pending)) *
    wordSemBytesInWord
  let pb := new + BitVec.ofNat width (heapLength scanned) * wordSemBytesInWord
  have different : pb ≠ pa := scanPointer_ne scanned pending (.dataElement addresses len (tag, payload))
    a n limit heap status result a1 n1 heap1 new run limitEq good bytesBound
  have positive : 0 < k := scanFuel_pos scanned pending (.dataElement addresses len (tag, payload))
    a n limit heap status result a1 n1 heap1 k run steps
  obtain ⟨header, words, encoded, wordLen, wordBound, decoded, info, read, valid, _⟩ :=
    scanDataCell conf scanned pending addresses len tag payload curr new pa xs heap memory domain frame
      good lenBound separated
  have read' : memory pb = .word header := by
    simpa [pb, wordSemBytesInWord, StackRemove.bytesInWord, BitVec.mul_comm] using read
  have valid' : domain pb = true := by
    simpa [pb, wordSemBytesInWord, StackRemove.bytesInWord, BitVec.mul_comm] using valid
  exact ⟨header, words, encoded, wordLen, wordBound, decoded, info, read', valid',
    scanWord_step conf k pb (BitVec.ofNat width a) pa curr memory domain header different positive read' valid'⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
