import Flapjack.Compiler.Backend.Semantics.DataSem.Heap.SizeProperties
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.HeapTraversal
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackRel
import Flapjack.Misc.Multiword.Length
import Flapjack.Misc.GoodDimindex
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv

/-! Source heap sizing facts used by collector soundness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend

/-- Sizing a cons list first processes its tail, then its head. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "size_of_cons"]
theorem sizeOfValues_cons (limits : DataSem.Limits) (x : DataSem.Value) (xs : List DataSem.Value)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit) :
    DataSem.sizeOfValues limits (x :: xs) refs seen =
      let (n1, refs1, seen1) := DataSem.sizeOfValues limits xs refs seen
      let (n2, refs2, seen2) := DataSem.sizeOfValues limits [x] refs1 seen1
      (n1 + n2, refs2, seen2) := by
  cases xs with
  | nil => simp [DataSem.sizeOfValues]
  | cons y ys => simp only [DataSem.sizeOfValues, DataSem.checkRes_sizeOfValues]

/-- The optional global and its default value have identical sizing effects. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "size_of_global_to_vs"]
theorem sizeOfValues_global (limits : DataSem.Limits) (values : List DataSem.Value) (global : Option Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit) :
    DataSem.sizeOfValues limits (values ++ DataSem.globalToValues global) refs seen =
      DataSem.sizeOfValues limits (values ++ [theGlobal global]) refs seen := by
  induction values generalizing refs seen with
  | nil =>
    cases global with
    | none =>
      cases arch : limits.arch64Bit <;>
        simp [DataSem.globalToValues, theGlobal, DataSem.sizeOfValues, DataSem.smallNum, arch]
    | some addr => simp [DataSem.globalToValues, theGlobal]
  | cons head tail ih =>
    simp only [List.cons_append]
    conv_lhs => rw [sizeOfValues_cons, ih]
    conv_rhs => rw [sizeOfValues_cons]

/-- Flapjack infrastructure: on a supported architecture, the word-digit
encoding length is exactly the source sizing function's digit count. -/
theorem n2mw_length_eq_bignumDigits {width : Nat} [NeZero width] (n : Nat)
    (good : goodDimindex width) :
    (Misc.Multiword.n2mw (width := width) n).length = DataSem.bignumDigits (decide (width = 64)) n := by
  have widthEq : (if decide (width = 64) then 64 else 32) = width := by
    rcases good with rfl | rfl <;> decide
  by_cases zero : n = 0
  · subst n
    simp [Misc.Multiword.n2mw, DataSem.bignumDigits]
  · rw [Misc.Multiword.n2mw, DataSem.bignumDigits]
    simp only [zero, ↓reduceIte, List.length_cons, widthEq]
    have smaller : n / 2 ^ width < n := by
      apply Nat.div_lt_self (Nat.pos_of_ne_zero zero)
      rcases good with rfl | rfl <;> decide
    have next := n2mw_length_eq_bignumDigits (width := width) (n / 2 ^ width) good
    omega
termination_by n

/-- The source bignum digit estimate bounds the encoded word-list length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "LENGTH_n2mw_LE_bignum_digits"
  (words_as_type_indexed_bitvec)]
theorem n2mw_length_le_bignumDigits {width : Nat} [NeZero width] (n m : Nat)
    (good : goodDimindex width) (bound : n ≤ m) :
    (Misc.Multiword.n2mw n : List (BitVec width)).length ≤ DataSem.bignumDigits (decide (width = 64)) m := by
  rw [← n2mw_length_eq_bignumDigits m good]
  exact Misc.Multiword.n2mw_length_mono n m bound

/-- Flapjack infrastructure: a represented large integer occupies no more
heap words than the source bignum size calculation charges. -/
theorem lookupLen_bignum_le {width : Nat} [NeZero width] {α : Type}
    (limits : DataSem.Limits) (heap : List (HeapElement α (Memory.HeapTag × List (WordLocW width))))
    (ptr : Nat) (value : Int) (good : goodDimindex width)
    (architecture : limits.arch64Bit = decide (width = 64))
    (found : heapLookup ptr heap = some (Memory.bignumRep value)) :
    Memory.lookupLen heap ptr ≤ DataSem.bignumSize limits.arch64Bit value := by
  have digits := n2mw_length_le_bignumDigits (width := width) value.natAbs value.natAbs good (Nat.le_refl _)
  simp only [Memory.lookupLen, found, Memory.bignumRep, Misc.Multiword.i2mw, elLength,
    DataSem.bignumSize, architecture]
  omega

/-- Flapjack infrastructure: the source's three-word charge for a Word64
value bounds the 32-bit and 64-bit heap representations. -/
theorem lookupLen_word64_le {width : Nat} [NeZero width] {α : Type}
    (heap : List (HeapElement α (Memory.HeapTag × List (WordLocW width))))
    (ptr : Nat) (value : BitVec 64)
    (found : heapLookup ptr heap = some (Memory.word64Rep value)) :
    Memory.lookupLen heap ptr ≤ 3 := by
  simp only [Memory.lookupLen, found, Memory.word64Rep]
  split <;> simp [elLength]

/-- Flapjack infrastructure: a bignum cell can be traversed while charging
at most the source bignum size. -/
theorem traverse_bignum_size {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (heap : List (HeapElement (WordLocW width) (Memory.HeapTag × List (WordLocW width)))) (visited : List Nat)
    (ptr : Nat) (value : Int) (annotation : WordLocW width) (good : goodDimindex width)
    (architecture : limits.arch64Bit = decide (width = 64))
    (found : heapLookup ptr heap = some (Memory.bignumRep value)) :
    traverseHeap heap visited [.pointer ptr annotation] (ptr :: visited) ∧
    (Memory.lookupLen heap ptr :: visited.map (Memory.lookupLen heap)).sum ≤
      DataSem.bignumSize limits.arch64Bit value + (visited.map (Memory.lookupLen heap)).sum := by
  refine ⟨?_, ?_⟩
  · apply traverseHeap.visit (children := [])
    · simpa [Memory.bignumRep, Misc.Multiword.i2mw] using found
    · exact traverseHeap.empty _
  · simp only [List.sum_cons]
    have size := lookupLen_bignum_le limits heap ptr value good architecture found
    omega

/-- Flapjack infrastructure: a represented Word64 can be traversed for no
more than the source's three-word charge. -/
theorem traverse_word64_size {width : Nat} [NeZero width]
    (heap : List (HeapElement (WordLocW width) (Memory.HeapTag × List (WordLocW width)))) (visited : List Nat) (ptr : Nat)
    (value : BitVec 64) (annotation : WordLocW width)
    (found : heapLookup ptr heap = some (Memory.word64Rep value)) :
    traverseHeap heap visited [.pointer ptr annotation] (ptr :: visited) ∧
    (Memory.lookupLen heap ptr :: visited.map (Memory.lookupLen heap)).sum ≤
      3 + (visited.map (Memory.lookupLen heap)).sum := by
  refine ⟨?_, ?_⟩
  · by_cases narrow : width < 64
    · apply traverseHeap.visit (children := [])
      · simpa [Memory.word64Rep, narrow] using found
      · exact traverseHeap.empty _
    · apply traverseHeap.visit (children := [])
      · simpa [Memory.word64Rep, narrow] using found
      · exact traverseHeap.empty _
  · simp only [List.sum_cons]
    have size := lookupLen_word64_le heap ptr value found
    omega

/-- Flapjack infrastructure: supported source and target architectures agree
on the immediate-integer range. -/
theorem smallNum_iff_smallInt {width : Nat} [NeZero width] (limits : DataSem.Limits)
    (i : Int) (good : goodDimindex width) (architecture : limits.arch64Bit = decide (width = 64)) :
    DataSem.smallNum limits.arch64Bit i ↔ smallInt width i := by
  rcases good with rfl | rfl <;>
    simp [DataSem.smallNum, smallInt, architecture]

/-- Flapjack infrastructure: a represented source number admits a heap
traversal whose added cost is bounded by the source singleton size. -/
theorem sizeOf_number_traversal {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (i : Int)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (visited : List Nat)
    (good : goodDimindex width) (architecture : limits.arch64Bit = decide (width = 64))
    (related : Memory.valueInv conf (.number i) refs (address, f, tf, heap)) :
    ∃ after, traverseHeap heap visited [address] after ∧
      (after.map (Memory.lookupLen heap)).sum ≤
        (DataSem.sizeOfValues limits [.number i] refs seen).1 + (visited.map (Memory.lookupLen heap)).sum := by
  have number := (Memory.valueInv_number conf i refs address f tf heap).mp related
  by_cases small : smallInt width i
  · have sourceSmall := (smallNum_iff_smallInt limits i good architecture).mpr small
    simp only [small, ↓reduceIte] at number
    subst address
    refine ⟨visited, traverseHeap.data visited _, ?_⟩
    simp [DataSem.sizeOfValues, sourceSmall]
  · have sourceBig : ¬ DataSem.smallNum limits.arch64Bit i := by
      intro sourceSmall
      exact small ((smallNum_iff_smallInt limits i good architecture).mp sourceSmall)
    simp only [small, ↓reduceIte] at number
    obtain ⟨ptr, rfl, found⟩ := number
    obtain ⟨run, cost⟩ := traverse_bignum_size limits heap visited ptr i (.word 0) good architecture found
    refine ⟨ptr :: visited, run, ?_⟩
    simpa [DataSem.sizeOfValues, sourceBig] using cost

/-- Flapjack infrastructure: a represented Word64 admits a traversal whose
added cost is bounded by its source singleton size. -/
theorem sizeOf_word64_traversal {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (value : BitVec 64)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (visited : List Nat)
    (related : Memory.valueInv conf (.word64 value) refs (address, f, tf, heap)) :
    ∃ after, traverseHeap heap visited [address] after ∧
      (after.map (Memory.lookupLen heap)).sum ≤
        (DataSem.sizeOfValues limits [.word64 value] refs seen).1 + (visited.map (Memory.lookupLen heap)).sum := by
  obtain ⟨ptr, rfl, found⟩ := (Memory.valueInv_word64 conf value refs address f tf heap).mp related
  obtain ⟨run, cost⟩ := traverse_word64_size heap visited ptr value (.word 0) found
  exact ⟨ptr :: visited, run, by simpa [DataSem.sizeOfValues] using cost⟩

/-- Flapjack infrastructure: a code pointer is an immediate value and adds
no heap traversal cost. -/
theorem sizeOf_codePtr_traversal {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (value : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (visited : List Nat)
    (related : Memory.valueInv conf (.codePtr value) refs (address, f, tf, heap)) :
    ∃ after, traverseHeap heap visited [address] after ∧
      (after.map (Memory.lookupLen heap)).sum ≤
        (DataSem.sizeOfValues limits [.codePtr value] refs seen).1 + (visited.map (Memory.lookupLen heap)).sum := by
  have equal := (Memory.valueInv_codePtr conf value refs address f tf heap).mp related
  subst address
  exact ⟨visited, traverseHeap.data visited _, by simp [DataSem.sizeOfValues]⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
