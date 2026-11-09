module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.LoopEmpty

@[expose] public section

/-! Address and fuel facts for the nonempty collector scan. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.CopyingGc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- With positive word size and no offset wrap, advancing by a positive
number of heap words changes the machine address. This is arithmetic
infrastructure for the nonempty scan branch, not a standalone HOL theorem. -/
theorem scanOffsets_ne {width : Nat} [NeZero width] (base : BitVec width)
    (scanned pending : Nat) (positive : 0 < pending) (wordBytes : 0 < width / 8)
    (bounded : (scanned + pending) * (width / 8) < 2 ^ width) :
    base + BitVec.ofNat width scanned * wordSemBytesInWord ≠
      base + BitVec.ofNat width (scanned + pending) * wordSemBytesInWord := by
  intro same
  have offsets : BitVec.ofNat width scanned * wordSemBytesInWord =
      BitVec.ofNat width (scanned + pending) * wordSemBytesInWord := by
    have eq := congrArg (fun x : BitVec width => x - base) same
    simpa only [BitVec.add_comm base, BitVec.add_sub_cancel] using eq
  have beforeBound : scanned * (width / 8) < 2 ^ width := by
    have le : scanned * (width / 8) ≤ (scanned + pending) * (width / 8) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have eq := congrArg BitVec.toNat offsets
  simp only [wordSemBytesInWord, ← BitVec.ofNat_mul, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt beforeBound, Nat.mod_eq_of_lt bounded] at eq
  have lt : scanned * (width / 8) < (scanned + pending) * (width / 8) :=
    Nat.mul_lt_mul_of_pos_right (by omega) wordBytes
  omega

/-- A successful abstract scan with a nonempty pending heap has not already
reached its concrete allocation pointer. The conclusion follows from the
original heap and byte bounds and does not assume address non-overlap. -/
theorem scanPointer_ne {width : Nat} [NeZero width]
    (scanned pending : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (head : HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))
    (a n limit : Nat) (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (c : Bool) (result : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a1 n1 : Nat) (heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (base : BitVec width)
    (run : gcMoveLoop (scanned, head :: pending, a, n, heap, c, limit) = (result, a1, n1, heap1, true))
    (limitEq : limit = heapLength heap) (good : goodDimindex width)
    (bytesBound : heapLength heap * (width / 8) < 2 ^ width) :
    base + BitVec.ofNat width (heapLength scanned) * wordSemBytesInWord ≠
      base + BitVec.ofNat width (heapLength (scanned ++ head :: pending)) * wordSemBytesInWord := by
  have heapBound : heapLength (scanned ++ head :: pending) ≤ limit := by
    by_contra notLe
    have over : limit < heapLength (scanned ++ head :: pending) := by omega
    cases head <;> simp [gcMoveLoop, over] at run
  have wordBytes : 0 < width / 8 := by rcases good with rfl | rfl <;> decide
  have pendingPos : 0 < heapLength (head :: pending) := by
    simp only [heapLength, List.map_cons, List.sum_cons]
    cases head <;> simp [elLength]
  have smaller : heapLength (scanned ++ head :: pending) * (width / 8) < 2 ^ width := by
    have le := Nat.mul_le_mul_right (width / 8) heapBound
    rw [limitEq] at le
    omega
  rw [heapLength_append] at smaller ⊢
  exact scanOffsets_ne base _ _ pendingPos wordBytes smaller

/-- For a successful nonempty scan, the source loop's fuel premise forces a
positive concrete loop counter. This helper has no standalone HOL original. -/
theorem scanFuel_pos {α β : Type} (scanned pending : List (HeapElement α β))
    (head : HeapElement α β) (a n limit : Nat) (heap : List (HeapElement α β))
    (c : Bool) (result : List (HeapElement α β)) (a1 n1 : Nat)
    (heap1 : List (HeapElement α β)) (k : Nat)
    (run : gcMoveLoop (scanned, head :: pending, a, n, heap, c, limit) = (result, a1, n1, heap1, true))
    (steps : limit - heapLength scanned ≤ k) : 0 < k := by
  have heapBound : heapLength (scanned ++ head :: pending) ≤ limit := by
    by_contra notLe
    have over : limit < heapLength (scanned ++ head :: pending) := by omega
    cases head <;> simp [gcMoveLoop, over] at run
  have pendingPos : 0 < heapLength (head :: pending) := by
    simp only [heapLength, List.map_cons, List.sum_cons]
    cases head <;> simp [elLength]
  rw [heapLength_append] at heapBound
  omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
