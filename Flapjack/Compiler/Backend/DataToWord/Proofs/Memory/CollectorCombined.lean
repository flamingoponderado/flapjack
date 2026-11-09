import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.CollectorPartial
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.CollectorNone
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.CollectorSimple

/-! Abstract memory correctness for the combined collector. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.GcCombined

/-- The combined collector restores abstract memory and, for a full
collection, its reachability and space guarantees. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gc_combined_thm"
  (words_as_type_indexed_bitvec)]
theorem combinedGc_abstractMemory {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width)))
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (be : Bool) (a sp sp1 : Nat) (gens : GenState) (limit next : Nat) (doPartial : Bool)
    (valid : absMlInv conf stack refs (roots, heap, be, a, sp, sp1, gens) limit next)
    (active : doPartial = true → hasGen gens) :
    ∃ roots1 heap1 gens1 n1 a1,
      gcCombined (makeGcConf limit) conf.gcKind (roots, heap, gens, a + sp + sp1, doPartial) =
        (roots1, heap1, a1, n1, gens1, true) ∧
      absMlInv conf stack refs (roots1, heap1, be, a1, n1, 0, gens1) limit next ∧
      (conf.gcKind ≠ .none ∧ (conf.gcKind ≠ .simple → doPartial = false) →
        allReachableFromRoots roots1 heap1 ∧ heapLength heap1 = dataLength heap1 + n1) := by
  cases kind : conf.gcKind with
  | none =>
    obtain ⟨run, result⟩ := combinedGc_none_absMlInv conf stack refs roots heap be a sp sp1 limit next gens doPartial valid kind
    exact ⟨roots, heap, gens, 0, 0, by simpa [kind] using run, result, by simp⟩
  | simple =>
    obtain ⟨roots1, heap1, a1, run, result, heapSize, _, reachable, allData⟩ :=
      fullGc_abstract_memory conf stack refs roots heap be a sp sp1 gens limit next ⟨valid, kind⟩
    refine ⟨roots1, heap1 ++ heapExpand (limit - a1), gens, limit - a1, a1, ?_, result, ?_⟩
    · simp [gcCombined, makeGcConf, run]
    · intro _
      refine ⟨reachable, ?_⟩
      simp [heapLength_append, heapLength_heapExpand, dataLength_append_heapExpand,
        dataLength_heapLength heap1 (List.forall_iff_forall_mem.mp allData)]
  | generational sizes =>
    cases doPartial with
    | false =>
      obtain ⟨roots1, state, run, result, ok, _, data, refData, reachable⟩ :=
        genGc_abstract_memory_allKinds conf stack refs roots heap be a sp sp1 gens limit next valid
      refine ⟨roots1, state.h1 ++ heapExpand state.n ++ state.r1,
        resetGens conf state.a, state.n, state.a, ?_, result, ?_⟩
      · simp [gcCombined, kind, resetGens, run, ok]
      · intro _
        refine ⟨reachable, ?_⟩
        simp [heapLength_append, heapLength_heapExpand, dataLength_append, dataLength_heapExpand,
          dataLength_heapLength state.h1 (List.forall_iff_forall_mem.mp data), dataLength_heapLength state.r1 (List.forall_iff_forall_mem.mp refData), Nat.add_comm,
          Nat.add_left_comm]
    | true =>
      obtain ⟨roots1, state, run, result, ok⟩ :=
        genGcPartial_abstractMemory conf stack refs roots heap be a sp sp1 gens limit next sizes valid (active rfl) kind
      refine ⟨roots1, state.old ++ state.h1 ++ heapExpand state.n ++ state.r1,
        resetGens conf state.a, state.n, state.a, ?_, result, ?_⟩
      · simp [gcCombined, kind, resetGens, Nat.add_assoc, run, ok]
      · simp

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
