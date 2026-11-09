import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.GcConfig
import Flapjack.Compiler.Backend.GcCombined.Collector
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CombinedStore

/-! No-collection branch of abstract collector correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.GcCombined

/-- The no-GC branch succeeds and preserves the abstract ML invariant at
the zero allocation boundary used by the combined collector. This is local
case infrastructure for the full collector correctness theorem. -/
theorem combinedGc_none_absMlInv {width : Nat} [NeZero width] (conf : Config)
    (stack : List DataSem.Value) (refs : Spt (BvlSem.Ref DataSem.Value))
    (roots : List (HeapAddress (WordLocW width)))
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (be : Bool) (a sp sp1 limit next : Nat) (gens : GenState) (flag : Bool)
    (source : absMlInv conf stack refs (roots, heap, be, a, sp, sp1, gens) limit next)
    (kind : conf.gcKind = .none) :
    gcCombined (makeGcConf (α := List (WordLocW width)) limit) conf.gcKind
        (roots, heap, gens, a + sp + sp1, flag) = (roots, heap, 0, 0, gens, true) ∧
      absMlInv conf stack refs (roots, heap, be, 0, 0, 0, gens) limit next := by
  obtain ⟨rootsOk, heapOk, gcOk, unused, stackInv⟩ := source
  refine ⟨by simp [gcCombined, kind], rootsOk, heapOk, ?_, ?_, stackInv⟩
  · simp [gcKindInv, kind]
  · refine ⟨by simp, by simp, ?_⟩
    refine ⟨[], heap, ?_, by simp⟩
    cases heap <;> simp [heapSplit]

/-- The no-GC branch executes the word collector and preserves both the
word-level ML invariant and the heap/store invariant. -/
theorem combinedGc_none_wordMlInv {width : Nat} [NeZero width] (conf : Config)
    (value : DataSem.Value) (stack : List (DataSem.Value × WordLocW width))
    (refs : Spt (BvlSem.Ref DataSem.Value))
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (be : Bool) (a sp sp1 limit next : Nat) (gens : GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (source : wordMlInv (heap, be, a, sp, sp1, gens) limit next conf refs
      ((value, holFapply store .globals) :: stack))
    (kind : conf.gcKind = .none) (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ stack1 outMemory outStore,
      WordGcFunctions.wordGcFun conf (stack.map Prod.snd, memory, domain, store) =
        some (stack1, outMemory, outStore) ∧
      heapInMemoryStore heap 0 0 0 gens conf outStore outMemory domain limit ∧
      wordMlInv (heap, be, 0, 0, 0, gens) limit next conf refs
        ((value, holFapply outStore .globals) :: ((stack.map Prod.fst).zip stack1)) ∧
      stack1.length = stack.length := by
  obtain ⟨roots, abstract, related⟩ := source
  simp only [List.map_cons] at abstract related
  obtain ⟨run, abstractOut⟩ := combinedGc_none_absMlInv conf (value :: stack.map Prod.fst) refs roots heap
    be a sp sp1 limit next gens (Gc.doPartial conf store) abstract kind
  obtain ⟨stack1, outMemory, outStore, k2, k3, execution, invariant, sum, _, _, _, rootsOut, length⟩ :=
    Gc.combinedGc_correct conf value stack refs roots roots heap heap be a sp sp1 limit next 0 0 gens gens
      store memory domain abstract good heapMem related run
  have zero2 : k2 = 0 := by omega
  have zero3 : k3 = 0 := by omega
  subst k2
  subst k3
  refine ⟨stack1, outMemory, outStore, execution, invariant, ?_, length⟩
  refine ⟨roots, ?_, ?_⟩
  · have zipBound : (stack.map Prod.fst).length ≤ stack1.length := by simp [length]
    simpa only [List.map_cons, List.map_fst_zip zipBound] using abstractOut
  · simpa using rootsOut

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
