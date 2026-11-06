import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MoveBlock
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MoveForward
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MoveData

/-! Full abstract-to-word copying-collector move simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Every successful abstract move is simulated by the word collector,
preserving the separated frame and the original heap-length and pointer facts. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gc_move_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGcMove_thm {width : Nat} [NeZero width] (conf : Config)
    (x x1 : HeapAddress (WordLocW width)) (a n limit a1 n1 : Nat)
    (heap heap1 h1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr pa pa1 i1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (w : WordLocW width) (c1 : Bool)
    (abstractRun : CopyingGc.gcMove (x, [], a, n, heap, true, limit) = (x1, h1, a1, n1, heap1, true))
    (heapBound : heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (separated : SetSep.star (SetSep.star (wordHeap curr heap conf) (Misc.wordList pa xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (wordRun : wordGcMove conf (wordAddr conf x, BitVec.ofNat width a, pa, curr, memory, domain) =
      (w, i1, pa1, memory1, c1)) (length : xs.length = n) :
    ∃ xs1,
      SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap1 conf) (wordHeap pa h1 conf))
        (Misc.wordList pa1 xs1)) frame (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      w = wordAddr conf x1 ∧ heapLength heap1 = heapLength heap ∧ c1 = true ∧
      i1 = BitVec.ofNat width a1 ∧ n1 = xs1.length ∧
      pa1 = pa + wordSemBytesInWord * BitVec.ofNat width (heapLength h1) := by
  cases x with
  | data value =>
    exact wordGcMove_data conf value a n limit a1 n1 heap heap1 h1 curr pa pa1 i1 xs
      memory memory1 domain frame x1 w c1 abstractRun heapBound separated wordRun length
  | pointer ptr value =>
    cases found : heapLookup ptr heap with
    | none => simp [CopyingGc.gcMove, found] at abstractRun
    | some element =>
      cases element with
      | unused len => simp [CopyingGc.gcMove, found] at abstractRun
      | forwardPointer forwarded oldValue len =>
        exact wordGcMove_forward conf ptr forwarded len value oldValue a n limit a1 n1 heap heap1 h1
          curr pa pa1 i1 xs memory memory1 domain frame x1 w c1 found abstractRun heapBound separated wordRun length
      | dataElement addresses len data =>
        rcases data with ⟨tag, payload⟩
        exact wordGcMove_dataElement conf ptr len value addresses tag payload a n limit a1 n1 heap heap1 h1
          curr pa pa1 i1 xs memory memory1 domain frame x1 w c1 found abstractRun heapBound separated wordRun length

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
