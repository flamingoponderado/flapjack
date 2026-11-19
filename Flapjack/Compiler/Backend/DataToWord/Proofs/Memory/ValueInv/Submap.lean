module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv.HeapStoreRel
public import Flapjack.FiniteMap.SubmapExact
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Canonical finite-map roundtrip for `f`. -/
theorem holFmapAsFiniteSupportParamWitness_valueInv_submap_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (ReferenceMapBroad.ofBroad (ReferenceMapBroad.toBroad f)).lookup key = f.lookup key ∧
    (ReferenceMapBroad.ofBroad (ReferenceMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    ReferenceMapBroad.ofBroad (ReferenceMapBroad.toBroad f) = f := by
  cases f
  exact ⟨rfl, rfl, rfl⟩

/-- Canonical finite-map roundtrip for `f1`. -/
theorem holFmapAsFiniteSupportParamWitness_valueInv_submap_f1
    (f1 : HolFiniteMapExact Nat Nat) (key : Nat) :
    (ReferenceMapBroad.ofBroad (ReferenceMapBroad.toBroad f1)).lookup key = f1.lookup key ∧
    (ReferenceMapBroad.ofBroad (ReferenceMapBroad.toBroad f1)).finiteSupport = f1.finiteSupport ∧
    ReferenceMapBroad.ofBroad (ReferenceMapBroad.toBroad f1) = f1 := by
  cases f1
  exact ⟨rfl, rfl, rfl⟩

/-- Canonical finite-map roundtrip for `tf`. -/
theorem holFmapAsFiniteSupportParamWitness_valueInv_submap_tf
    (tf : HolFiniteMapExact Nat Nat) (key : Nat) :
    (ReferenceMapBroad.ofBroad (ReferenceMapBroad.toBroad tf)).lookup key = tf.lookup key ∧
    (ReferenceMapBroad.ofBroad (ReferenceMapBroad.toBroad tf)).finiteSupport = tf.finiteSupport ∧
    ReferenceMapBroad.ofBroad (ReferenceMapBroad.toBroad tf) = tf := by
  cases tf
  exact ⟨rfl, rfl, rfl⟩

/-- Canonical finite-map roundtrip for `tf1`. -/
theorem holFmapAsFiniteSupportParamWitness_valueInv_submap_tf1
    (tf1 : HolFiniteMapExact Nat Nat) (key : Nat) :
    (ReferenceMapBroad.ofBroad (ReferenceMapBroad.toBroad tf1)).lookup key = tf1.lookup key ∧
    (ReferenceMapBroad.ofBroad (ReferenceMapBroad.toBroad tf1)).finiteSupport = tf1.finiteSupport ∧
    ReferenceMapBroad.ofBroad (ReferenceMapBroad.toBroad tf1) = tf1 := by
  cases tf1
  exact ⟨rfl, rfl, rfl⟩

/-- Extending both finite maps while preserving all old data cells preserves
the full value invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_SUBMAP"
  (fmap_as_finite_support_parameters := [f, f1, tf, tf1]) (words_as_type_indexed_bitvec)]
theorem valueInv_submap {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (f : HolFiniteMapExact Nat Nat) (f1 : HolFiniteMapExact Nat Nat)
    (tf : HolFiniteMapExact Nat Nat) (tf1 : HolFiniteMapExact Nat Nat)
    (heap heap1 : ValueHeap width) (value : Flapjack.Compiler.Backend.DataSem.Value) (address : HeapAddress (WordLocW width)) :
    f.submap f1 ∧ tf.submap tf1 ∧ heapStoreRel heap heap1 ∧ valueInv conf value refs (address, f, tf, heap) →
      valueInv conf value refs (address, f1, tf1, heap1) := by
  rintro ⟨references, timestamps, rel, inv⟩ ck
  apply clockValueInv_mapHeapExtend ck conf refs f f1 tf tf1 heap heap1 references timestamps ?_ value address (inv ck)
  intro ptr cell data found
  obtain ⟨xs, len, d, rfl⟩ := data
  exact (rel ptr ⟨xs, len, d, found⟩).trans found
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
