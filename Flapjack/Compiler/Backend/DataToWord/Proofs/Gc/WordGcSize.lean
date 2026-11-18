module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.SizeSoundness
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordGcCorrect
public import Flapjack.Compiler.Backend.WordGcFunctions.Roots

@[expose] public section

/-! Source heap-size consequences of executing word-level collection. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.Compiler.Backend.GcCombined

/-- Flapjack infrastructure: the executed collector's failed-space result
implies the source sizing bound for the input roots. The caller must still
relate these roots to the source stack used by its state relation. -/
theorem wordGcFun_failed_sourceSize {width : Nat} [NeZero width] {C F : Type}
    (limits : DataSem.Limits) (conf : Config) (value : DataSem.Value)
    (stack : List (DataSem.Value × WordLocW width)) (refs : Spt (BvlSem.Ref DataSem.Value))
    (heap : ValueHeap width) (be : Bool) (a sp sp1 limit next requested : Nat) (gens : GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (state : WordSemStateFiniteExact width C F)
    (good : goodDimindex width) (architecture : limits.arch64Bit = decide (width = 64))
    (limitEq : limits.heapLimit = limit) (noThunks : DataSem.noThunksInRefs refs)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit)
    (source : wordMlInv (heap, be, a, sp, sp1, gens) limit next conf refs
      ((value, holFapply store .globals) :: stack)) :
    ∃ (stack1 : List (WordLocW width)) (outMemory : BitVec width → WordLocW width)
      (outStore : HolFiniteMapExact WordStoreHOL (WordLocW width)),
      wordGcFun conf (stack.map Prod.snd, memory, domain, store) = some (stack1, outMemory, outStore) ∧
      (store.lookup .allocSize = some (.word (gcAllocSize requested)) ∧
        WordSemStateFiniteExact.hasSpace (.word (gcAllocSize requested) : WordLocW width)
          { state with store := outStore } = some false ∧
        conf.gcKind ≠ .none →
        ∀ roots2 dups,
          roots2.Perm (dups ++ (value :: stack.map Prod.fst)) →
          (∀ v, v ∈ dups → v ∈ value :: stack.map Prod.fst) →
          limits.heapLimit < (DataSem.sizeOfValues limits roots2 refs .ln).1 + requested) := by
  obtain ⟨stack1, outMemory, outStore, heap1, a1, free1, free2, gens1, root1, roots1,
    run, _, invariant, _, _, failedResult⟩ :=
    wordGcFun_correct conf value stack refs heap be a sp sp1 limit next requested gens store memory domain state
      good heapMem source
  refine ⟨stack1, outMemory, outStore, run, ?_⟩
  intro failed roots2 dups perm duplicates
  obtain ⟨insufficient, reachable, heapSplit⟩ := failedResult failed
  have length := word_gc_fun_LENGTH run
  have zipBound : (stack.map Prod.fst).length ≤ stack1.length := by
    simpa using Nat.le_of_eq length
  have invariant' : absMlInv conf (value :: stack.map Prod.fst) refs
      (root1 :: roots1, heap1, be, a1, free1, free2, gens1) limit next := by
    simpa only [List.map_fst_zip zipBound] using invariant
  exact absMlInv_failed_request limits conf roots2 dups
    (value :: stack.map Prod.fst) (root1 :: roots1) heap1 refs be
    a1 free1 free2 limit next requested gens1 good architecture limitEq invariant' reachable noThunks
    heapSplit insufficient perm duplicates

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
