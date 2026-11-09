module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.CollectorGenerational
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CombinedStore

@[expose] public section

/-! Word-level memory correctness for major generational collection. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.GcCombined

/-- When a generational collector takes the major branch, it executes at word
level and restores both the concrete heap representation and the word-level
ML invariant. -/
theorem combinedGc_major_wordMlInv {width : Nat} [NeZero width] (conf : Config)
    (value : DataSem.Value) (stack : List (DataSem.Value × WordLocW width))
    (refs : Spt (BvlSem.Ref DataSem.Value))
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (be : Bool) (a sp sp1 limit next : Nat) (gens : GenState) (sizes : List Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (source : wordMlInv (heap, be, a, sp, sp1, gens) limit next conf refs
      ((value, holFapply store .globals) :: stack))
    (kind : conf.gcKind = .generational sizes) (major : Gc.doPartial conf store = false)
    (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ roots roots1 state stack1 outMemory outStore k2 k3,
      GenGc.genGc (makeGcConf limit) (roots, heap) = (roots1, state) ∧
      WordGcFunctions.wordGcFun conf (stack.map Prod.snd, memory, domain, store) =
        some (stack1, outMemory, outStore) ∧
      heapInMemoryStore (state.h1 ++ heapExpand state.n ++ state.r1) state.a k2 k3
        (.genState 0 (sizes.map fun _ => state.a)) conf outStore outMemory domain limit ∧
      wordMlInv (state.h1 ++ heapExpand state.n ++ state.r1, be, state.a, k2, k3,
        .genState 0 (sizes.map fun _ => state.a)) limit next conf refs
        ((value, holFapply outStore .globals) :: ((stack.map Prod.fst).zip stack1)) ∧
      k2 + k3 = state.n ∧
      (∀ requested, store.lookup .allocSize = some (.word (Gc.gcAllocSize requested)) →
        requested ≤ state.n → requested ≤ k2) ∧ stack1.length = stack.length := by
  obtain ⟨roots, abstract, related⟩ := source
  simp only [List.map_cons] at abstract related
  obtain ⟨roots1, state, run, abstractOut, ok, _, _, _, _⟩ :=
    genGc_generational_abstract_memory conf (value :: stack.map Prod.fst) refs roots heap be a sp sp1 gens limit next sizes abstract kind
  have combinedRun : gcCombined (makeGcConf (α := List (WordLocW width)) limit) conf.gcKind
      (roots, heap, gens, a + sp + sp1, Gc.doPartial conf store) =
      (roots1, state.h1 ++ heapExpand state.n ++ state.r1, state.a, state.n,
        .genState 0 (sizes.map fun _ => state.a), true) := by
    simp [gcCombined, kind, major, run, ok]
  obtain ⟨stack1, outMemory, outStore, k2, k3, execution, invariant, sum, _, _, allocation, rootsOut, length⟩ :=
    Gc.combinedGc_correct conf value stack refs roots roots1 heap (state.h1 ++ heapExpand state.n ++ state.r1)
      be a sp sp1 limit next state.a state.n gens (.genState 0 (sizes.map fun _ => state.a))
      store memory domain abstract good heapMem related combinedRun
  have abstractSplit : absMlInv conf (value :: stack.map Prod.fst) refs
      (roots1, state.h1 ++ heapExpand state.n ++ state.r1, be, state.a, k2, k3,
        .genState 0 (sizes.map fun _ => state.a)) limit next := by
    simpa [absMlInv, gcKindInv, kind, Nat.add_assoc, sum] using abstractOut
  have full : ¬ WordGcFunctions.wordGenGcCanDoPartial sizes store := by
    simpa [Gc.doPartial, kind] using major
  refine ⟨roots, roots1, state, stack1, outMemory, outStore, k2, k3, run, execution, invariant, ?_, sum, ?_, length⟩
  swap
  · intro requested size bound
    exact allocation sizes requested kind full size bound
  refine ⟨roots1, ?_, ?_⟩
  · have zipBound : (stack.map Prod.fst).length ≤ stack1.length := by simp [length]
    simpa only [List.map_cons, List.map_fst_zip zipBound] using abstractSplit
  · simpa using rootsOut

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
