import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CombinedNone
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CombinedSimple
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalStore
import Flapjack.Compiler.Backend.Semantics.WordSem.Alloc

/-! Collector branch composition for the store-level simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.Compiler.Backend.GcCombined

/-- The concrete word semantics reports sufficient space from the actual
store lookups and unsigned pointer gap. -/
theorem collector_hasSpace_of_gap {width : Nat} [NeZero width] {C F : Type}
    (state : WordSemStateFiniteExact width C F) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (request p t : BitVec width) (next : store.lookup .nextFree = some (.word p))
    (trigger : store.lookup .triggerGC = some (.word t)) (fits : request ≤ t - p) :
    WordSemStateFiniteExact.hasSpace (.word request) { state with store := store } = some true := by
  simpa [WordSemStateFiniteExact.hasSpace, WordSemStateFiniteExact.getStore, next, trigger, BitVec.le_def] using fits

/-- The combined collector preserves the heap/store invariant and stack-root
encoding, and satisfies the allocation-space conclusions for both generational
branches. This local statement assumes the source root list is nonempty. -/
theorem combinedGc_stack_correct {width : Nat} [NeZero width] (conf : Config)
    (value : DataSem.Value) (stack : List (DataSem.Value × WordLocW width))
    (references : Spt (BvlSem.Ref DataSem.Value)) (root : HeapAddress (WordLocW width))
    (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (be : Bool) (a sp sp1 limit next a1 n1 : Nat) (gens gens1 : GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (source : absMlInv conf (value :: stack.map Prod.fst) references (root :: roots, heap, be, a, sp, sp1, gens) limit next)
    (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit)
    (global : wordAddr conf root = holFapply store .globals)
    (related : List.Forall₂ (fun v w => wordAddr conf v = w) roots (stack.map Prod.snd))
    (run : gcCombined (makeGcConf (α := List (WordLocW width)) limit) conf.gcKind
      (root :: roots, heap, gens, a + sp + sp1, doPartial conf store) = (roots1, heap1, a1, n1, gens1, true)) :
    ∃ stack1 outMemory outStore k2 k3 root1 rest,
      wordGcFun conf (stack.map Prod.snd, memory, domain, store) = some (stack1, outMemory, outStore) ∧
      heapInMemoryStore heap1 a1 k2 k3 gens1 conf outStore outMemory domain limit ∧ k2 + k3 = n1 ∧
      ((conf.gcKind = .none ∨ conf.gcKind = .simple) → k3 = 0) ∧
      roots1 = root1 :: rest ∧ wordAddr conf root1 = holFapply outStore .globals ∧
      List.Forall₂ (fun v w => wordAddr conf v = w) rest (((stack.map Prod.fst).zip stack1).map Prod.snd) ∧
      stack1.length = stack.length ∧ (∀ limits, conf.gcKind = .generational limits →
        wordGenGcCanDoPartial limits store → ∃ p t,
          outStore.lookup .nextFree = some (.word p) ∧ outStore.lookup .triggerGC = some (.word t) ∧
            wordSemTheWord (holFapply store .allocSize) ≤ t - p) ∧
      (∀ (limits : List Nat) (request : BitVec width), conf.gcKind = .generational limits →
        wordGenGcCanDoPartial limits store → store.lookup .allocSize = some (.word request) →
        ∀ {C F : Type} (state : WordSemStateFiniteExact width C F),
          WordSemStateFiniteExact.hasSpace (.word request) { state with store := outStore } = some true) ∧
      (∀ limits requested, conf.gcKind = .generational limits → ¬ wordGenGcCanDoPartial limits store →
        store.lookup .allocSize = some (.word
          (if requested * (width / 8) < 2 ^ width then BitVec.ofNat width (requested * (width / 8)) else -1)) →
        requested ≤ n1 → requested ≤ k2) := by
  cases kind : conf.gcKind with
  | none =>
    obtain ⟨stack1, outMemory, outStore, k2, k3, root1, rest, execution, invariant, sum, zero,
      rootsOut, globalOut, stackOut, length⟩ :=
      combinedNone_store_correct conf stack root roots roots1 heap heap1 a sp sp1 limit a1 n1 gens gens1
        store memory domain good heapMem global related run kind
    exact ⟨stack1, outMemory, outStore, k2, k3, root1, rest, execution, invariant, sum, fun _ => zero,
      rootsOut, globalOut, stackOut, length, by simp, by simp, by simp⟩
  | simple =>
    obtain ⟨stack1, outMemory, outStore, k2, k3, root1, rest, execution, invariant, sum, zero,
      rootsOut, globalOut, stackOut, length⟩ :=
      combinedSimple_store_correct conf value stack references root roots roots1 heap heap1 be a sp sp1 limit next
        a1 n1 gens gens1 store memory domain source good heapMem global related run kind
    exact ⟨stack1, outMemory, outStore, k2, k3, root1, rest, execution, invariant, sum, fun _ => zero,
      rootsOut, globalOut, stackOut, length, by simp, by simp, by simp⟩
  | generational limits =>
    have genRun : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits)
        (root :: roots, heap, gens, a + sp + sp1, doPartial conf store) =
        (roots1, heap1, a1, n1, gens1, true) := by simpa [kind] using run
    obtain ⟨stack1, outMemory, outStore, k2, k3, root1, rest, execution, invariant, sum,
      rootsOut, globalOut, stackOut, length, space, allocation⟩ :=
      combinedGenerational_stack_correct conf value stack references root roots roots1 heap heap1 be a sp sp1
        limit next a1 n1 gens gens1 limits store memory domain source kind good heapMem global related genRun
    refine ⟨stack1, outMemory, outStore, k2, k3, root1, rest, execution, invariant, sum, ?_,
      rootsOut, globalOut, stackOut, length, ?_, ?_, ?_⟩
    · simp
    · intro sizes same selected
      have sizesEq : sizes = limits := by simpa [kind] using same.symm
      subst sizes
      exact space selected
    · intro sizes request same selected alloc C F state
      have sizesEq : sizes = limits := by simpa [kind] using same.symm
      subst sizes
      obtain ⟨p, t, next, trigger, fits⟩ := space selected
      have requestFits : request ≤ t - p := by simpa [holFapply_of_lookup alloc, wordSemTheWord] using fits
      exact collector_hasSpace_of_gap state outStore request p t next trigger requestFits
    · intro sizes requested same full alloc bound
      have sizesEq : sizes = limits := by simpa [kind] using same.symm
      subst sizes
      exact allocation full requested alloc bound

/-- Collector correctness without assuming the input roots are nonempty: the
relation to the stored global and stack roots entails that fact. The result
uses the actual word evaluator's space check for arbitrary surrounding word
state; it remains local until the HOL declaration and carrier types are reviewed. -/
theorem combinedGc_correct {width : Nat} [NeZero width] (conf : Config)
    (value : DataSem.Value) (stack : List (DataSem.Value × WordLocW width))
    (references : Spt (BvlSem.Ref DataSem.Value)) (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (be : Bool) (a sp sp1 limit next a1 n1 : Nat) (gens gens1 : GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (source : absMlInv conf (value :: stack.map Prod.fst) references (roots, heap, be, a, sp, sp1, gens) limit next)
    (good : goodDimindex width) (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit)
    (related : List.Forall₂ (fun v w => wordAddr conf v = w) roots
      (holFapply store .globals :: stack.map Prod.snd))
    (run : gcCombined (makeGcConf (α := List (WordLocW width)) limit) conf.gcKind
      (roots, heap, gens, a + sp + sp1, doPartial conf store) = (roots1, heap1, a1, n1, gens1, true)) :
    ∃ stack1 outMemory outStore k2 k3,
      wordGcFun conf (stack.map Prod.snd, memory, domain, store) = some (stack1, outMemory, outStore) ∧
      heapInMemoryStore heap1 a1 k2 k3 gens1 conf outStore outMemory domain limit ∧ k2 + k3 = n1 ∧
      (∀ (limits : List Nat) (request : BitVec width), conf.gcKind = .generational limits →
        wordGenGcCanDoPartial limits store → store.lookup .allocSize = some (.word request) →
        ∀ {C F : Type} (state : WordSemStateFiniteExact width C F),
          WordSemStateFiniteExact.hasSpace (.word request) { state with store := outStore } = some true) ∧
      ((conf.gcKind = .none ∨ conf.gcKind = .simple) → k3 = 0) ∧
      (∀ limits requested, conf.gcKind = .generational limits → ¬ wordGenGcCanDoPartial limits store →
        store.lookup .allocSize = some (.word
          (if requested * (width / 8) < 2 ^ width then BitVec.ofNat width (requested * (width / 8)) else -1)) →
        requested ≤ n1 → requested ≤ k2) ∧
      List.Forall₂ (fun v w => wordAddr conf v = w) roots1
        (holFapply outStore .globals :: (((stack.map Prod.fst).zip stack1).map Prod.snd)) ∧
      stack1.length = stack.length := by
  cases related with
  | cons global tail =>
    obtain ⟨stack1, outMemory, outStore, k2, k3, root1, rest, execution, invariant, freeSum, zero,
      rootsOut, globalOut, stackOut, length, _, space, allocation⟩ :=
      combinedGc_stack_correct conf value stack references _ _ roots1 heap heap1 be a sp sp1 limit next a1 n1
        gens gens1 store memory domain source good heapMem global tail run
    refine ⟨stack1, outMemory, outStore, k2, k3, execution, invariant, freeSum, space, zero, allocation, ?_, length⟩
    rw [rootsOut]
    exact .cons globalOut stackOut

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
