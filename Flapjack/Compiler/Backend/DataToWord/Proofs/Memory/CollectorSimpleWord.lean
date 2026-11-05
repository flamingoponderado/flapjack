import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.CollectorSimple
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CombinedStore

/-! Word-level memory correctness for simple copying collection. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.GcCombined

/-- Simple collection executes at word level and preserves both the heap
representation and word-level ML invariant. This is a Flapjack case of the
combined collector correctness argument. -/
theorem combinedGc_simple_wordMlInv {width : Nat} [NeZero width] (conf : Config)
    (value : DataSem.Value) (stack : List (DataSem.Value × WordLocW width))
    (refs : Spt (BvlSem.Ref DataSem.Value))
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (be : Bool) (a sp sp1 limit next : Nat) (gens : GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (source : wordMlInv (heap, be, a, sp, sp1, gens) limit next conf refs
      ((value, holFapply store .globals) :: stack))
    (kind : conf.gcKind = .simple) (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ roots roots2 heap2 used stack1 outMemory outStore,
      CopyingGc.fullGc (roots, heap, limit) = (roots2, heap2, used, true) ∧
      WordGcFunctions.wordGcFun conf (stack.map Prod.snd, memory, domain, store) =
        some (stack1, outMemory, outStore) ∧
      heapInMemoryStore (heap2 ++ heapExpand (limit - used)) used (limit - used) 0 gens
        conf outStore outMemory domain limit ∧
      wordMlInv (heap2 ++ heapExpand (limit - used), be, used, limit - used, 0, gens)
        limit next conf refs ((value, holFapply outStore .globals) :: ((stack.map Prod.fst).zip stack1)) ∧
      stack1.length = stack.length := by
  obtain ⟨roots, abstract, related⟩ := source
  simp only [List.map_cons] at abstract related
  obtain ⟨roots2, heap2, used, run, abstractOut, _, _, _, _⟩ :=
    fullGc_abstract_memory conf (value :: stack.map Prod.fst) refs roots heap be a sp sp1 gens limit next
      ⟨abstract, kind⟩
  have combinedRun : gcCombined (makeGcConf (α := List (WordLocW width)) limit) conf.gcKind
      (roots, heap, gens, a + sp + sp1, Gc.doPartial conf store) =
      (roots2, heap2 ++ heapExpand (limit - used), used, limit - used, gens, true) := by
    simp [gcCombined, kind, makeGcConf, run]
  obtain ⟨stack1, outMemory, outStore, k2, k3, execution, invariant, sum, _, zero, _, rootsOut, length⟩ :=
    Gc.combinedGc_correct conf value stack refs roots roots2 heap (heap2 ++ heapExpand (limit - used))
      be a sp sp1 limit next used (limit - used) gens gens store memory domain abstract good heapMem related combinedRun
  have zero3 : k3 = 0 := zero (Or.inr kind)
  subst k3
  have space : k2 = limit - used := by omega
  subst k2
  refine ⟨roots, roots2, heap2, used, stack1, outMemory, outStore, run, execution, invariant, ?_, length⟩
  refine ⟨roots2, ?_, ?_⟩
  · have zipBound : (stack.map Prod.fst).length ≤ stack1.length := by simp [length]
    simpa only [List.map_cons, List.map_fst_zip zipBound] using abstractOut
  · simpa using rootsOut

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
