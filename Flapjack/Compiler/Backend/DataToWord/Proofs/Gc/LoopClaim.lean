import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.LoopCell

/-! The source-shaped predicate used for the collector scan induction. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.CopyingGc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- The full HOL scan statement at a fixed abstract input. This factoring is
Flapjack-specific; it introduces no additional simulation premise and has no
standalone HOL declaration. -/
def ScanClaim {width : Nat} [NeZero width] (conf : Config)
    (scanned pending : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a n : Nat) (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (c0 : Bool) (limit : Nat) : Prop :=
  ∀ (h11 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (a1 n1 : Nat)
    (heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (i1 pa1 : BitVec width) (m1 : BitVec width → WordLocW width) (c1 : Bool)
    (xs : List (WordLocW width)) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (m : BitVec width → WordLocW width) (k : Nat) (curr new : BitVec width) (dm : BitVec width → Bool),
    gcMoveLoop (scanned, pending, a, n, heap, c0, limit) = (h11, a1, n1, heap1, true) →
    c0 = true → heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf →
    heapLength heap * (width / 8) < 2 ^ width → conf.lenSize + 2 < width →
    SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap conf) (wordHeap new (scanned ++ pending) conf))
      (Misc.wordList (new + BitVec.ofNat width (heapLength (scanned ++ pending)) * wordSemBytesInWord) xs)) frame
      (SetSep.fun2Set (m, fun address => dm address = true)) →
    limit - heapLength scanned ≤ k → limit = heapLength heap → goodDimindex width →
    wordGcMoveLoop k conf (new + BitVec.ofNat width (heapLength scanned) * wordSemBytesInWord,
      BitVec.ofNat width a, new + BitVec.ofNat width (heapLength (scanned ++ pending)) * wordSemBytesInWord,
      curr, m, dm, true) = (i1, pa1, m1, c1) → xs.length = n →
    ∃ xs1,
      SetSep.star (SetSep.star (SetSep.star (wordHeap curr heap1 conf) (wordHeap new h11 conf))
        (Misc.wordList pa1 xs1)) frame (SetSep.fun2Set (m1, fun address => dm address = true)) ∧
      heapLength heap1 = heapLength heap ∧ c1 = true ∧ i1 = BitVec.ofNat width a1 ∧ n1 = xs1.length ∧
      pa1 = new + wordSemBytesInWord * BitVec.ofNat width (heapLength h11)

/-- The empty scan satisfies the full source-shaped claim. -/
theorem scanClaim_empty {width : Nat} [NeZero width] (conf : Config)
    (scanned : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a n : Nat) (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (c0 : Bool) (limit : Nat) : ScanClaim conf scanned [] a n heap c0 limit := by
  intro h11 a1 n1 heap1 i1 pa1 m1 c1 xs frame m k curr new dm
  exact wordGcMoveLoop_empty conf scanned a n heap c0 limit h11 a1 n1 heap1 i1 pa1 m1 c1 xs frame m k curr new dm

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
