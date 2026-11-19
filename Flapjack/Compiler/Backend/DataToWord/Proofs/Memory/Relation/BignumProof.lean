module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.LeafAllocate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BignumPush
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Allocating a non-small integer preserves the complete abstract machine invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bignum_alt_thm"
  (words_as_type_indexed_bitvec)]
theorem bignumAlt {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (ws stack : List Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (rs roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (be : Bool) (a sp sp1 : Nat) (gens : GenState) (limit ts : Nat)
    (i : Int) (large : ¬ smallInt width i) (len : Nat) (tag : HeapTag) (xs : List (WordLocW width))
    (inv : absMlInv conf (ws ++ stack) refs (rs ++ roots, heap, be, a, sp, sp1, gens) limit ts)
    (lengths : ws.length = rs.length)
    (rep : (bignumRep i : HeapElement (WordLocW width) (HeapTag × List (WordLocW width))) =
      .dataElement [] len (tag, xs)) (room : xs.length < sp) :
    ∃ heap2, heapStoreUnusedAlt a (sp + sp1) (bignumRep i) heap = (heap2, true) ∧
      absMlInv conf (.number i :: stack) refs
        (.pointer a (.word 0) :: roots, heap2, be, a + len + 1, sp - len - 1, sp1, gens) limit ts := by
  have shape : ∃ (sign : Bool) (payload : List (BitVec width)), len = payload.length ∧ tag = .numTag sign ∧ xs = payload.map .word := by
    unfold bignumRep at rep
    cases h : Misc.Multiword.i2mw (width := width) i with
    | mk sign payload =>
      simp only [h] at rep
      cases rep
      exact ⟨sign, payload, rfl, rfl, rfl⟩
  have lenEq : xs.length = len := by
    obtain ⟨sign, payload, rfl, rfl, rfl⟩ := shape
    simp
  have immutable : ¬ isMutTag tag := by
    obtain ⟨sign, payload, _, rfl, _⟩ := shape
    simp [isMutTag]
  have fits : len + 1 ≤ sp := by omega
  obtain ⟨heap2, stored, lookup, _rel, popped⟩ := absMlInv_allocateLeaf conf ws stack refs rs roots heap
    be a sp sp1 gens limit ts len tag xs inv lengths immutable fits
  refine ⟨heap2, ?_, ?_⟩
  · simpa [rep] using stored
  · refine ⟨?_, popped.2.1, popped.2.2.1, popped.2.2.2.1, ?_⟩
    · intro ptr value member
      rcases List.mem_cons.mp member with eq | old
      · cases eq
        rw [lookup]
        simp [isSomeDataElement]
      · exact popped.1 ptr value old
    · apply bcStackRefInv_pushBignum conf ts stack refs roots heap2 be a i large
      · simpa [rep] using lookup
      · exact popped.2.2.2.2
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
