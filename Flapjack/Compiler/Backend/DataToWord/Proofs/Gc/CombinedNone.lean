import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.None
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.DoPartial
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.GcConfig
import Flapjack.Compiler.Backend.GcCombined.Collector

/-! No-collection case of the combined GC simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.GcCombined
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Flapjack-specific composition of the no-collection store invariant and
combined collector; the general source theorem also covers other GC kinds. -/
theorem combinedNone_store_correct {width : Nat} [NeZero width] (conf : Config)
    (stack : List (DataSem.Value × WordLocW width)) (root : HeapAddress (WordLocW width))
    (roots roots2 : List (HeapAddress (WordLocW width)))
    (heap heap2 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit a2 n2 : Nat) (gens gens2 : GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit)
    (global : wordAddr conf root = holFapply store .globals)
    (related : List.Forall₂ (fun v w => wordAddr conf v = w) roots (stack.map Prod.snd))
    (run : gcCombined (makeGcConf limit) conf.gcKind (root :: roots, heap, gens, a + sp + sp1,
      doPartial conf store) = (roots2, heap2, a2, n2, gens2, true))
    (kind : conf.gcKind = .none) :
    ∃ (stack1 : List (WordLocW width)) (outMemory : BitVec width → WordLocW width)
      (outStore : HolFiniteMapExact WordStoreHOL (WordLocW width)) (k2 k3 : Nat)
      (root1 : HeapAddress (WordLocW width)) (roots1 : List (HeapAddress (WordLocW width))),
      wordGcFun conf (stack.map Prod.snd, memory, domain, store) = some (stack1, outMemory, outStore) ∧
      heapInMemoryStore heap2 a2 k2 k3 gens2 conf outStore outMemory domain limit ∧
      k2 + k3 = n2 ∧ k3 = 0 ∧ roots2 = root1 :: roots1 ∧
      wordAddr conf root1 = holFapply outStore .globals ∧
      List.Forall₂ (fun v w => wordAddr conf v = w) roots1
        (((stack.map Prod.fst).zip stack1).map Prod.snd) ∧ stack1.length = stack.length := by
  simp only [gcCombined, kind, Prod.mk.injEq] at run
  obtain ⟨rfl, rfl, rfl, rfl, rfl, _⟩ := run
  obtain ⟨outStore, execution, invariant, globals⟩ :=
    noneGc_store_correct conf (stack.map Prod.snd) heap a sp sp1 limit gens store memory domain kind good heapMem
  refine ⟨stack.map Prod.snd, memory, outStore, 0, 0, root, roots, execution, invariant, rfl, rfl, rfl, ?_, ?_, by simp⟩
  · simpa [holFapply, globals] using global
  · have zipped : ((stack.map Prod.fst).zip (stack.map Prod.snd)).map Prod.snd = stack.map Prod.snd :=
      List.map_snd_zip (by simp)
    rw [zipped]
    exact related

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
