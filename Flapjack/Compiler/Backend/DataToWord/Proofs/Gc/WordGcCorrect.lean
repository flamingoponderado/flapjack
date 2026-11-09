module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.CollectorCombined
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CombinedStore

@[expose] public section

/-! Relating the combined abstract collector to the executed word collector. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.Compiler.Backend.GcCombined

/-- Flapjack infrastructure: selecting partial collection entails an active
abstract generation in a represented heap. -/
theorem doPartial_hasGen {width : Nat} [NeZero width] (conf : Config)
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit : Nat) (gens : GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit)
    (selected : doPartial conf store = true) : hasGen gens := by
  cases kind : conf.gcKind with
  | none | simple => simp [doPartial, kind] at selected
  | generational sizes =>
    have canDo : wordGenGcCanDoPartial sizes store := by simpa [doPartial, kind] using selected
    obtain ⟨_, _, _, _, _, _, _, curr, other, _, _, _, _, _, _, _, _, _, generations, _⟩ := heapMem
    obtain ⟨start, tail, count, shape, _⟩ :=
      partialGenStart_store conf (makeGcConf limit) gens (a + sp + sp1) sizes store kind canDo generations
    simp [shape, hasGen]

/-- Flapjack infrastructure: for all collector kinds, the executed word
collector restores the heap representation and word-level ML invariant,
retaining the abstract collector’s conditional full-collection properties. -/
theorem wordGc_combined_memory {width : Nat} [NeZero width] (conf : Config)
    (value : DataSem.Value) (stack : List (DataSem.Value × WordLocW width))
    (refs : Spt (BvlSem.Ref DataSem.Value))
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (be : Bool) (a sp sp1 limit next : Nat) (gens : GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (source : wordMlInv (heap, be, a, sp, sp1, gens) limit next conf refs
      ((value, holFapply store .globals) :: stack))
    (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ roots1 heap1 gens1 a1 n1 stack1 outMemory outStore k2 k3,
      wordGcFun conf (stack.map Prod.snd, memory, domain, store) = some (stack1, outMemory, outStore) ∧
      heapInMemoryStore heap1 a1 k2 k3 gens1 conf outStore outMemory domain limit ∧
      wordMlInv (heap1, be, a1, k2, k3, gens1) limit next conf refs
        ((value, holFapply outStore .globals) :: ((stack.map Prod.fst).zip stack1)) ∧
      absMlInv conf (value :: stack.map Prod.fst) refs (roots1, heap1, be, a1, k2, k3, gens1) limit next ∧
      k2 + k3 = n1 ∧ stack1.length = stack.length ∧
      (conf.gcKind ≠ .none ∧ (conf.gcKind ≠ .simple → doPartial conf store = false) →
        allReachableFromRoots roots1 heap1 ∧ heapLength heap1 = dataLength heap1 + n1) ∧
      List.Forall₂ (fun v w => wordAddr conf v = w) roots1
        (holFapply outStore .globals :: (((stack.map Prod.fst).zip stack1).map Prod.snd)) ∧
      (∀ limits request, conf.gcKind = .generational limits → wordGenGcCanDoPartial limits store →
        store.lookup .allocSize = some (.word request) →
        ∀ {C F : Type} (state : WordSemStateFiniteExact width C F),
          WordSemStateFiniteExact.hasSpace (.word request) { state with store := outStore } = some true) ∧
      ((conf.gcKind = .none ∨ conf.gcKind = .simple) → k3 = 0) ∧
      (∀ limits requested, conf.gcKind = .generational limits → ¬ wordGenGcCanDoPartial limits store →
        store.lookup .allocSize = some (.word (gcAllocSize requested)) → requested ≤ n1 → requested ≤ k2) := by
  obtain ⟨roots, abstract, related⟩ := source
  simp only [List.map_cons] at abstract related
  have active : doPartial conf store = true → hasGen gens :=
    doPartial_hasGen conf heap a sp sp1 limit gens store memory domain heapMem
  obtain ⟨roots1, heap1, gens1, n1, a1, run, abstractOut, full⟩ :=
    combinedGc_abstractMemory conf (value :: stack.map Prod.fst) refs roots heap be a sp sp1 gens limit next
      (doPartial conf store) abstract active
  obtain ⟨stack1, outMemory, outStore, k2, k3, execution, invariant, sum, space, zero, allocation, rootsOut, length⟩ :=
    combinedGc_correct conf value stack refs roots roots1 heap heap1 be a sp sp1 limit next a1 n1 gens gens1
      store memory domain abstract good heapMem related run
  have abstractSplit : absMlInv conf (value :: stack.map Prod.fst) refs
      (roots1, heap1, be, a1, k2, k3, gens1) limit next := by
    cases kind : conf.gcKind with
    | none =>
      have empty := zero (Or.inl kind)
      have split : k2 = n1 := by omega
      simpa [absMlInv, gcKindInv, kind, empty, split] using abstractOut
    | simple =>
      have empty := zero (Or.inr kind)
      have split : k2 = n1 := by omega
      simpa [absMlInv, gcKindInv, kind, empty, split] using abstractOut
    | generational sizes =>
      simpa [absMlInv, gcKindInv, kind, Nat.add_assoc, sum] using abstractOut
  have output : wordMlInv (heap1, be, a1, k2, k3, gens1) limit next conf refs
      ((value, holFapply outStore .globals) :: ((stack.map Prod.fst).zip stack1)) := by
    refine ⟨roots1, ?_, ?_⟩
    · have zipBound : (stack.map Prod.fst).length ≤ stack1.length := by simp [length]
      simpa only [List.map_cons, List.map_fst_zip zipBound] using abstractSplit
    · simpa using rootsOut
  exact ⟨roots1, heap1, gens1, a1, n1, stack1, outMemory, outStore, k2, k3,
    execution, invariant, output, abstractSplit, sum, length, full, rootsOut, space, zero, allocation⟩

namespace WordGcCorrectWitnesses

/-- Canonical finite-map roundtrip for the word state used by the space check. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordGcCorrectWitnesses

/-- The word collector preserves abstract memory and proves the space and
reachability consequences of a failed allocation after collection. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gc_fun_correct"
  (fmap_as_finite_support_relation := [store, outStore, WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem wordGcFun_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (value : Flapjack.Compiler.Backend.DataSem.Value)
    (stack : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (be : Bool) (a sp sp1 limit next requested : Nat) (gens : GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (state : WordSemStateFiniteExact width C F)
    (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit)
    (source : wordMlInv (heap, be, a, sp, sp1, gens) limit next conf refs
      ((value, holFapply store .globals) :: stack)) :
    ∃ (stack1 : List (WordLocW width)) (outMemory : BitVec width → WordLocW width)
      (outStore : HolFiniteMapExact WordStoreHOL (WordLocW width))
      (heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
      (a1 free1 free2 : Nat) (gens1 : GenState) (root1 : HeapAddress (WordLocW width))
      (roots1 : List (HeapAddress (WordLocW width))),
      wordGcFun conf (stack.map Prod.snd, memory, domain, store) = some (stack1, outMemory, outStore) ∧
      heapInMemoryStore heap1 a1 free1 free2 gens1 conf outStore outMemory domain limit ∧
      absMlInv conf (value :: (((stack.map Prod.fst).zip stack1).map Prod.fst)) refs
        (root1 :: roots1, heap1, be, a1, free1, free2, gens1) limit next ∧
      wordAddr conf root1 = holFapply outStore .globals ∧
      List.Forall₂ (fun v w => wordAddr conf v = w) roots1 (((stack.map Prod.fst).zip stack1).map Prod.snd) ∧
      (store.lookup .allocSize = some (.word (gcAllocSize requested)) ∧
        WordSemStateFiniteExact.hasSpace (.word (gcAllocSize requested)) { state with store := outStore } = some false ∧
        conf.gcKind ≠ .none →
        free1 + free2 < requested ∧ allReachableFromRoots (root1 :: roots1) heap1 ∧
        heapLength heap1 = dataLength heap1 + free1 + free2) := by
  obtain ⟨roots, heap1, gens1, a1, n1, stack1, outMemory, outStore, free1, free2,
    execution, invariant, _, abstractOut, sum, length, full, rootsOut, space, zero, allocation⟩ :=
    wordGc_combined_memory conf value stack refs heap be a sp sp1 limit next gens store memory domain source good heapMem
  cases rootsOut with
  | cons global tail =>
    rename_i root1 roots1
    have zipBound : (stack.map Prod.fst).length ≤ stack1.length := by simp [length]
    have abstractZip : absMlInv conf (value :: (((stack.map Prod.fst).zip stack1).map Prod.fst)) refs
        (root1 :: roots1, heap1, be, a1, free1, free2, gens1) limit next := by
      simpa only [List.map_fst_zip zipBound] using abstractOut
    refine ⟨stack1, outMemory, outStore, heap1, a1, free1, free2, gens1, root1, roots1,
      execution, invariant, abstractZip, global, tail, ?_⟩
    rintro ⟨alloc, failed, nonzero⟩
    have byteBound : free1 * (width / 8) < 2 ^ width := by
      have heapBound := invariant.2.1
      have freeBound := abstractOut.2.2.2.1.2.1
      have le : free1 ≤ heapLength heap1 + 3 := by omega
      exact lt_of_le_of_lt (Nat.mul_le_mul_right _ le) heapBound
    have insufficient := collector_hasSpace_false_bound conf heap1 a1 free1 free2 limit requested gens1
      outStore outMemory domain state good invariant byteBound failed
    have fullCase : conf.gcKind ≠ .none ∧ (conf.gcKind ≠ .simple → doPartial conf store = false) := by
      refine ⟨nonzero, ?_⟩
      intro notSimple
      cases kind : conf.gcKind with
      | none => exact False.elim (nonzero kind)
      | simple => exact False.elim (notSimple kind)
      | generational sizes =>
        by_cases selected : wordGenGcCanDoPartial sizes store
        · have enough := space sizes (gcAllocSize requested) kind selected alloc state
          rw [failed] at enough
          contradiction
        · simp [doPartial, kind, selected]
    have out := full fullCase
    refine ⟨?_, out.1, ?_⟩
    · cases kind : conf.gcKind with
      | none => exact False.elim (nonzero kind)
      | simple =>
        have freeZero := zero (Or.inr kind)
        omega
      | generational sizes =>
        have notSelected : ¬ wordGenGcCanDoPartial sizes store := by
          intro selected
          have enough := space sizes (gcAllocSize requested) kind selected alloc state
          rw [failed] at enough
          contradiction
        have implication := allocation sizes requested kind notSelected alloc
        omega
    · omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
