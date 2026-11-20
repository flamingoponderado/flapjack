module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.HeapStore
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv.HeapExtend
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Canonical finite-map roundtrip for the reference map parameter. -/
theorem holFmapAsFiniteSupportParamWitness_heapStoreRel_valueInv_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (ReferenceMapBroad.ofBroad (ReferenceMapBroad.toBroad f)).lookup key = f.lookup key ∧
    (ReferenceMapBroad.ofBroad (ReferenceMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    ReferenceMapBroad.ofBroad (ReferenceMapBroad.toBroad f) = f := by
  cases f
  exact ⟨rfl, rfl, rfl⟩

/-- Canonical finite-map roundtrip for the timestamp map parameter. -/
theorem holFmapAsFiniteSupportParamWitness_heapStoreRel_valueInv_tf
    (tf : HolFiniteMapExact Nat Nat) (key : Nat) :
    (ReferenceMapBroad.ofBroad (ReferenceMapBroad.toBroad tf)).lookup key = tf.lookup key ∧
    (ReferenceMapBroad.ofBroad (ReferenceMapBroad.toBroad tf)).finiteSupport = tf.finiteSupport ∧
    ReferenceMapBroad.ofBroad (ReferenceMapBroad.toBroad tf) = tf := by
  cases tf
  exact ⟨rfl, rfl, rfl⟩

/-- Preserving existing data cells preserves every value representation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_store_rel_v_inv"
  (fmap_as_finite_support_parameters := [f, tf]) (words_as_type_indexed_bitvec)]
theorem heapStoreRel_valueInv {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
    (heap heap1 : ValueHeap width) (w : Flapjack.Compiler.Backend.DataSem.Value) (x : HeapAddress (WordLocW width)) :
    heapStoreRel heap heap1 ∧ valueInv conf w refs (x, f, tf, heap) →
      valueInv conf w refs (x, f, tf, heap1) := by
  rintro ⟨rel, inv⟩
  apply valueInv_heapExtend conf refs f tf tf heap heap1 (by intros; assumption) ?_ w x inv
  intro ptr cell data found
  obtain ⟨xs, len, d, rfl⟩ := data
  exact (rel ptr ⟨xs, len, d, found⟩).trans found

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
