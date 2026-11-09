module

public import Flapjack.Compiler.Backend.GenGc.Proofs.Correct
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.GcConfig

@[expose] public section

/-! Abstract memory conditions for major generational collection. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend

/-- Reset generation starts to the new allocation boundary. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "reset_gens_def"]
def resetGens (conf : DataToWord.Config) (a : Nat) : GcCombined.GenState :=
  match conf.gcKind with
  | .generational sizes => .genState 0 (sizes.map fun _ => a)
  | _ => .genState 0 []

/-- Major generational collection restores the complete abstract ML
invariant, reachability, and live-heap length. This Flapjack result covers
the generational case; the source theorem also covers other collector kinds. -/
theorem genGc_generational_abstract_memory {width : Nat} [NeZero width]
    (conf : DataToWord.Config) (stack : List DataSem.Value)
    (refs : Spt (BvlSem.Ref DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (bigEndian : Bool) (a sp sp1 : Nat) (gens : GcCombined.GenState)
    (limit next : Nat) (sizes : List Nat)
    (valid : absMlInv conf stack refs (roots, heap, bigEndian, a, sp, sp1, gens) limit next)
    (kind : conf.gcKind = .generational sizes) :
    ∃ roots1 state,
      GenGc.genGc (makeGcConf limit) (roots, heap) = (roots1, state) ∧
      absMlInv conf stack refs
        (roots1, state.h1 ++ heapExpand state.n ++ state.r1, bigEndian,
          state.a, state.n, 0, .genState 0 (sizes.map fun _ => state.a)) limit next ∧
      state.ok = true ∧
      heapLength (state.h1 ++ state.r1) = heapLength (heapFilter (reachableAddresses roots heap) heap) ∧
      List.Forall isDataElement state.h1 ∧ List.Forall isDataElement state.r1 ∧
      allReachableFromRoots roots1 (state.h1 ++ heapExpand state.n ++ state.r1) := by
  obtain ⟨rootOk, heapGood, _, _, stackValid⟩ := valid
  have classify : ∀ tag payload, (makeGcConf (α := List (WordLocW width)) limit).isRef (tag, payload) = true ↔ isMutTag tag := by
    intro tag payload
    simp [makeGcConf]
  obtain ⟨roots1, state, run, ok, _, rootsGood, heapWell, free, reachable, filtered, stackGood⟩ :=
    GenGc.genGc_abstract_memory conf next stack refs roots heap (makeGcConf limit) bigEndian rootOk heapGood stackValid
  obtain ⟨roots2, state2, run2, kindGood⟩ :=
    GenGc.genGc_kindInv conf (makeGcConf limit) sizes roots heap kind classify rootOk heapGood
  have equal : (roots1, state) = (roots2, state2) := run.symm.trans run2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have partition := genGc_dataRefsSplit (makeGcConf limit) roots heap classify
  rw [run] at partition
  refine ⟨roots1, state, run, ⟨rootsGood, heapWell, kindGood, ?_, stackGood⟩,
    ok, filtered.symm, ?_, ?_, reachable⟩
  · simpa using free
  · exact List.forall_iff_forall_mem.mpr (fun e member => (partition.1 e member).1)
  · have source := (GenGc.genGc_invariant (makeGcConf limit) roots heap rootOk heapGood)
    obtain ⟨state3, run3, _, invariant, _, _, _, _⟩ := source
    have same : (roots1, state) = (addrMap (heapMap1 state3.heap) roots, state3) := run.symm.trans run3
    have stateEq : state = state3 := (Prod.mk.inj same).2
    rw [stateEq]
    exact List.forall_iff_forall_mem.mpr invariant.2.2.2.2.2.2.2.2.2.1

/-- Major collection restores the complete abstract ML invariant for any
collector kind. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gen_gc_thm"
  (words_as_type_indexed_bitvec)]
theorem genGc_abstract_memory_allKinds {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width)))
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (bigEndian : Bool) (a sp sp1 : Nat) (gens : GcCombined.GenState)
    (limit next : Nat)
    (valid : absMlInv conf stack refs (roots, heap, bigEndian, a, sp, sp1, gens) limit next) :
    ∃ roots1 state,
      GenGc.genGc (makeGcConf limit) (roots, heap) = (roots1, state) ∧
      absMlInv conf stack refs
        (roots1, state.h1 ++ heapExpand state.n ++ state.r1, bigEndian,
          state.a, state.n, 0, resetGens conf state.a) limit next ∧
      state.ok = true ∧
      heapLength (state.h1 ++ state.r1) = heapLength (heapFilter (reachableAddresses roots heap) heap) ∧
      List.Forall isDataElement state.h1 ∧ List.Forall isDataElement state.r1 ∧
      allReachableFromRoots roots1 (state.h1 ++ heapExpand state.n ++ state.r1) := by
  cases kind : conf.gcKind with
  | generational sizes =>
    simpa [resetGens, kind] using
      genGc_generational_abstract_memory conf stack refs roots heap bigEndian a sp sp1 gens limit next sizes valid kind
  | none | simple =>
    obtain ⟨rootOk, heapGood, _, _, stackValid⟩ := valid
    obtain ⟨roots1, state, run, ok, _, rootsGood, heapWell, free, reachable, filtered, stackGood⟩ :=
      GenGc.genGc_abstract_memory conf next stack refs roots heap (makeGcConf limit) bigEndian rootOk heapGood stackValid
    obtain ⟨state2, run2, _, invariant, _, _, _, _⟩ :=
      GenGc.genGc_invariant (makeGcConf limit) roots heap rootOk heapGood
    have same : (roots1, state) = (addrMap (heapMap1 state2.heap) roots, state2) := run.symm.trans run2
    have stateEq : state = state2 := (Prod.mk.inj same).2
    subst state2
    refine ⟨roots1, state, run, ⟨rootsGood, heapWell, ?_, ?_, stackGood⟩, ok, filtered.symm, ?_, ?_, reachable⟩
    · simp [gcKindInv, kind]
    · simpa using free
    · exact List.forall_iff_forall_mem.mpr invariant.2.2.2.2.2.2.2.1
    · exact List.forall_iff_forall_mem.mpr invariant.2.2.2.2.2.2.2.2.2.1

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
