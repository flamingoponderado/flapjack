import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CombinedNone
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CombinedSimple
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalStore

/-! Collector branch composition for the store-level simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.Compiler.Backend.GcCombined

/-- The combined collector preserves the heap/store invariant and stack-root
encoding for each GC kind. The original collector theorem also proves
allocation-space guarantees, which this local composition does not state. -/
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
      stack1.length = stack.length := by
  cases kind : conf.gcKind with
  | none =>
    obtain ⟨stack1, outMemory, outStore, k2, k3, root1, rest, execution, invariant, sum, zero,
      rootsOut, globalOut, stackOut, length⟩ :=
      combinedNone_store_correct conf stack root roots roots1 heap heap1 a sp sp1 limit a1 n1 gens gens1
        store memory domain good heapMem global related run kind
    exact ⟨stack1, outMemory, outStore, k2, k3, root1, rest, execution, invariant, sum, fun _ => zero,
      rootsOut, globalOut, stackOut, length⟩
  | simple =>
    obtain ⟨stack1, outMemory, outStore, k2, k3, root1, rest, execution, invariant, sum, zero,
      rootsOut, globalOut, stackOut, length⟩ :=
      combinedSimple_store_correct conf value stack references root roots roots1 heap heap1 be a sp sp1 limit next
        a1 n1 gens gens1 store memory domain source good heapMem global related run kind
    exact ⟨stack1, outMemory, outStore, k2, k3, root1, rest, execution, invariant, sum, fun _ => zero,
      rootsOut, globalOut, stackOut, length⟩
  | generational limits =>
    have genRun : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits)
        (root :: roots, heap, gens, a + sp + sp1, doPartial conf store) =
        (roots1, heap1, a1, n1, gens1, true) := by simpa [kind] using run
    obtain ⟨stack1, outMemory, outStore, k2, k3, root1, rest, execution, invariant, sum,
      rootsOut, globalOut, stackOut, length⟩ :=
      combinedGenerational_stack_correct conf value stack references root roots roots1 heap heap1 be a sp sp1
        limit next a1 n1 gens gens1 limits store memory domain source kind good heapMem global related genRun
    refine ⟨stack1, outMemory, outStore, k2, k3, root1, rest, execution, invariant, sum, ?_,
      rootsOut, globalOut, stackOut, length⟩
    simp

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
