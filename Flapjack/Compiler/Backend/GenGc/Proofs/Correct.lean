import Flapjack.Compiler.Backend.GenGc.Proofs.Invariant
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.CollectorSimple

/-! Abstract heap correctness for major collection. -/
namespace Flapjack.Compiler.Backend.GenGc
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- A major collection of well-formed input produces well-formed roots and
heap, with all objects reachable and free space at the recorded boundary.
This Flapjack consequence connects the collector invariant with the abstract
memory infrastructure; it is not yet a reviewed HOL theorem port. -/
theorem genGc_abstract_structure {α β : Type} (conf : Config β)
    (roots : List (HeapAddress α)) (heap : List (HeapElement α β))
    (rootOk : rootsOk roots heap) (heapGood : heapOk heap conf.limit) :
    ∃ (roots1 : List (HeapAddress α)) (state : GcState α β),
      genGc conf (roots, heap) = (roots1, state) ∧
      state.ok = true ∧ state.a = heapLength state.h1 ∧
      rootsOk roots1 (state.h1 ++ heapExpand state.n ++ state.r1) ∧
      heapOk (state.h1 ++ heapExpand state.n ++ state.r1) conf.limit ∧
      unusedSpaceInv state.a state.n (state.h1 ++ heapExpand state.n ++ state.r1) ∧
      allReachableFromRoots roots1 (state.h1 ++ heapExpand state.n ++ state.r1) ∧
      heapLength (heapFilter (reachableAddresses roots heap) heap) = heapLength (state.h1 ++ state.r1) := by
  obtain ⟨state, run, rootDomain, invariant, h2, r4, r3, r2⟩ :=
    genGc_invariant conf roots heap rootOk heapGood
  let f := heapMap 0 state.heap
  have domain := gcInv_final_domain conf state heap roots invariant h2 r4 r3 r2 rootDomain
  have range := gcInv_final_range conf state heap roots invariant h2 r4 r3 r2
  have related := gcInv_final_related conf state heap roots invariant h2 r4 r3 r2
  have filtered := gcInv_final_filterLength conf state heap roots invariant h2 r4 r3 r2
  have allocated : state.a = heapLength state.h1 := by simpa [h2] using invariant.1.symm
  have size : heapLength (state.h1 ++ heapExpand state.n ++ state.r1) = conf.limit := by
    have balance := invariant.2.1
    simpa [heapLength_append, heapLength_heapExpand, h2, r4, r3, r2, allocated, Nat.add_assoc] using balance
  have h1Data : ∀ element ∈ state.h1, isDataElement element := invariant.2.2.2.2.2.2.2.1
  have r1Data : ∀ element ∈ state.r1, isDataElement element := invariant.2.2.2.2.2.2.2.2.2.1
  have h1NoForward : state.h1.filter isForwardPointer = [] := by
    have result := filter_forward_heapExpand state.h1 0 h1Data
    simpa [heapExpand] using result
  have r1NoForward : state.r1.filter isForwardPointer = [] := by
    have result := filter_forward_heapExpand state.r1 0 r1Data
    simpa [heapExpand] using result
  have expansionNoForward : (heapExpand state.n : List (HeapElement α β)).filter isForwardPointer = [] := by
    cases state.n <;> simp [heapExpand, isForwardPointer]
  have noForward : (state.h1 ++ heapExpand state.n ++ state.r1).filter isForwardPointer = [] := by
    simp [List.filter_append, h1NoForward, r1NoForward, expansionNoForward]
  have free : unusedSpaceInv state.a state.n (state.h1 ++ heapExpand state.n ++ state.r1) := by
    refine ⟨?_, ?_, ?_⟩
    · intro nonzero
      cases eq : state.n with
      | zero => exact False.elim (nonzero eq)
      | succ n =>
        rw [allocated]
        simpa [eq, heapExpand, List.append_assoc] using
          (heapLookup_prefix state.h1 state.r1 (.unused n))
    · simp [heapLength_append, heapLength_heapExpand, allocated]
    · refine ⟨state.h1, heapExpand state.n ++ state.r1, ?_, h1Data⟩
      simpa [allocated, List.append_assoc] using DataToWord.Proofs.Gc.heapSplit_append state.h1 (heapExpand state.n ++ state.r1)
  refine ⟨addrMap (holFapply f) roots, state, run, invariant.2.2.2.2.1, allocated, ?_, ?_, free, ?_, ?_⟩
  · exact rootsOk_gcRelated roots heap _ f related rootDomain
  · exact heapOk_gcRelated heap _ f conf.limit related range size noForward
  · exact imp_allReachableFromRoots f roots heap _ domain range related
  · rw [← domain]
    exact filtered.symm

/-- Major collection preserves the combined data stack and reference
invariant. The source's separate thunk-inlining stage is not included here. -/
theorem genGc_stack_reference {width : Nat} [NeZero width]
    (wordConf : DataToWord.Config) (next : Nat) (stack : List DataSem.Value)
    (refs : Spt (BvlSem.Ref DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (conf : Config (HeapTag × List (WordLocW width))) (bigEndian : Bool)
    (rootOk : rootsOk roots heap) (heapGood : heapOk heap conf.limit)
    (valid : bcStackRefInv wordConf next stack refs (roots, heap, bigEndian)) :
    ∃ roots1 state,
      genGc conf (roots, heap) = (roots1, state) ∧
      bcStackRefInv wordConf next stack refs
        (roots1, state.h1 ++ heapExpand state.n ++ state.r1, bigEndian) := by
  obtain ⟨state, run, rootDomain, invariant, h2, r4, r3, r2⟩ :=
    genGc_invariant conf roots heap rootOk heapGood
  let f := heapMap 0 state.heap
  have related := gcInv_final_related conf state heap roots invariant h2 r4 r3 r2
  exact ⟨addrMap (holFapply f) roots, state, run,
    bcStackRefInv_gcRelated wordConf next stack refs roots heap _ bigEndian f related rootDomain valid⟩

/-- The same major-collection result satisfies both the abstract heap
conditions and the stack/reference invariant. -/
theorem genGc_abstract_memory {width : Nat} [NeZero width]
    (wordConf : DataToWord.Config) (next : Nat) (stack : List DataSem.Value)
    (refs : Spt (BvlSem.Ref DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (conf : Config (HeapTag × List (WordLocW width))) (bigEndian : Bool)
    (rootOk : rootsOk roots heap) (heapGood : heapOk heap conf.limit)
    (valid : bcStackRefInv wordConf next stack refs (roots, heap, bigEndian)) :
    ∃ roots1 state,
      genGc conf (roots, heap) = (roots1, state) ∧
      state.ok = true ∧ state.a = heapLength state.h1 ∧
      rootsOk roots1 (state.h1 ++ heapExpand state.n ++ state.r1) ∧
      heapOk (state.h1 ++ heapExpand state.n ++ state.r1) conf.limit ∧
      unusedSpaceInv state.a state.n (state.h1 ++ heapExpand state.n ++ state.r1) ∧
      allReachableFromRoots roots1 (state.h1 ++ heapExpand state.n ++ state.r1) ∧
      heapLength (heapFilter (reachableAddresses roots heap) heap) = heapLength (state.h1 ++ state.r1) ∧
      bcStackRefInv wordConf next stack refs
        (roots1, state.h1 ++ heapExpand state.n ++ state.r1, bigEndian) := by
  obtain ⟨roots1, state, run, ok, allocated, rootsGood, heapWell, free, reachable, filtered⟩ :=
    genGc_abstract_structure conf roots heap rootOk heapGood
  obtain ⟨roots2, state2, run2, stackValid⟩ :=
    genGc_stack_reference wordConf next stack refs roots heap conf bigEndian rootOk heapGood valid
  have equal : (roots1, state) = (roots2, state2) := run.symm.trans run2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  exact ⟨roots1, state, run, ok, allocated, rootsGood, heapWell, free, reachable, filtered, stackValid⟩

end Flapjack.Compiler.Backend.GenGc
