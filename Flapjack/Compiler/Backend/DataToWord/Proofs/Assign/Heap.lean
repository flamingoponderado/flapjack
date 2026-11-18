module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation

@[expose] public section

/-! Heap-store facts for data-to-word assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

namespace reviewedStateRel_lookupHeapMap
/-- Canonical roundtrip for the target state used by this HOL port. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end reviewedStateRel_lookupHeapMap

/-- The full state relation provides the next-free, current-heap and heap-
length words. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "state_rel_FLOOKUP_heap"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_lookupHeap {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (related : stateRel conf l1 l2 source target none locs) :
    ∃ nextFree currHeap heapLength : BitVec width,
      target.store.lookup .nextFree = some (.word nextFree) ∧
      target.store.lookup .currHeap = some (.word currHeap) ∧
      target.store.lookup .heapLength = some (.word heapLength) := by
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmem⟩
  obtain ⟨heap, limit, a, sp, sp1, gens, hstore, _, _, _⟩ := hmem
  obtain ⟨_, _, _, _, _, _, _, curr, other, _, _, currFound, _, nextFound, _, _, lengthFound, _⟩ := hstore
  exact ⟨_, curr, _, nextFound, currFound, lengthFound⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
