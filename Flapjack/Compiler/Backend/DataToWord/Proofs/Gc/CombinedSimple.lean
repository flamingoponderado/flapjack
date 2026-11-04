import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Simple
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.DoPartial
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.GcConfig
import Flapjack.Compiler.Backend.GcCombined.Collector

/-! Simple-collector case of the combined GC simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.CopyingGc Flapjack.Compiler.Backend.GcCombined
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Flapjack-specific composition of the source Simple collector theorem
with the corresponding combined-collector branch. The general HOL theorem
also covers the no-GC and generational cases. -/
theorem combinedSimple_store_correct {width : Nat} [NeZero width] (conf : Config)
    (value : DataSem.Value) (stack : List (DataSem.Value × WordLocW width))
    (refs : Spt (BvlSem.Ref DataSem.Value)) (root : HeapAddress (WordLocW width))
    (roots roots2 : List (HeapAddress (WordLocW width)))
    (heap heap2 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (be : Bool) (a sp sp1 limit ts a2 n2 : Nat) (gens gens2 : GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (abstractInv : absMlInv conf (value :: stack.map Prod.fst) refs
      (root :: roots, heap, be, a, sp, sp1, gens) limit ts)
    (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit)
    (global : wordAddr conf root = holFapply store .globals)
    (related : List.Forall₂ (fun v w => wordAddr conf v = w) roots (stack.map Prod.snd))
    (run : gcCombined (makeGcConf limit) conf.gcKind (root :: roots, heap, gens, a + sp + sp1,
      doPartial conf store) = (roots2, heap2, a2, n2, gens2, true))
    (kind : conf.gcKind = .simple) :
    ∃ (stack1 : List (WordLocW width)) (outMemory : BitVec width → WordLocW width)
      (outStore : HolFiniteMapExact WordStoreHOL (WordLocW width)) (k2 k3 : Nat)
      (root1 : HeapAddress (WordLocW width)) (roots1 : List (HeapAddress (WordLocW width))),
      wordGcFun conf (stack.map Prod.snd, memory, domain, store) = some (stack1, outMemory, outStore) ∧
      heapInMemoryStore heap2 a2 k2 k3 gens2 conf outStore outMemory domain limit ∧
      k2 + k3 = n2 ∧ k3 = 0 ∧ roots2 = root1 :: roots1 ∧
      wordAddr conf root1 = holFapply outStore .globals ∧
      List.Forall₂ (fun v w => wordAddr conf v = w) roots1
        (((stack.map Prod.fst).zip stack1).map Prod.snd) ∧ stack1.length = stack.length := by
  simp only [gcCombined, kind, makeGcConf] at run
  generalize fullRun : fullGc (root :: roots, heap, limit) = fullResult at run
  rcases fullResult with ⟨moved, copied, used, ok⟩
  simp only [Prod.mk.injEq] at run
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := run
  have allocEq := fullGc_alloc (root :: roots) moved heap copied limit used fullRun
  subst used
  obtain ⟨stack1, outMemory, outStore, root1, roots1, execution, invariant, rootsEq, globalEq, rootsRel, length⟩ :=
    wordGcFun_lemma_simple conf value stack refs root roots moved heap copied be a sp sp1 limit ts gens
      store memory domain abstractInv good heapMem global related fullRun kind
  exact ⟨stack1, outMemory, outStore, limit - heapLength copied, 0, root1, roots1,
    execution, invariant, by simp, rfl, rootsEq, globalEq, rootsRel, length⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
