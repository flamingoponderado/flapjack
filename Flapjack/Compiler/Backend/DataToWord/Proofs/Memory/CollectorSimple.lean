import Flapjack.Compiler.Backend.CopyingGc.Proofs.Invariant
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialSplit
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Relocation

/-! Abstract memory conditions for the simple copying collector. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend

/-- A data-only copied heap followed by unused space satisfies the abstract
unused-space condition. This Flapjack lemma supports simple collection. -/
theorem unusedSpaceInv_heapExpand {α β : Type} (heap : List (HeapElement α β)) (free : Nat)
    (allData : ∀ element ∈ heap, isDataElement element) :
    unusedSpaceInv (heapLength heap) free (heap ++ heapExpand free) := by
  refine ⟨?_, ?_, ?_⟩
  · intro nonzero
    rw [GenGc.heapLookup_append]
    simp [heapExpand, nonzero, heapLookup]
  · simp [heapLength_append, heapLength_heapExpand]
  · exact ⟨heap, heapExpand free, Gc.heapSplit_append heap _, allData⟩

/-- A related heap makes every renamed root point to a data element whenever
the original root addresses are in the relation's domain. -/
theorem rootsOk_gcRelated {α β : Type} (roots : List (HeapAddress α))
    (heap heap2 : List (HeapElement α β)) (f : HolFiniteMapExact Nat Nat)
    (related : gcRelated f heap heap2)
    (domain : ∀ ptr u, .pointer ptr u ∈ roots → f.lookup ptr ≠ none) :
    rootsOk (addrMap (holFapply f) roots) heap2 := by
  intro ptr u member
  obtain ⟨old, oldMember, mapped⟩ := mem_addrMap roots (holFapply f) ptr u member
  rw [← mapped]
  exact related.1 old (domain old u oldMember)

/-- A related heap whose data addresses are exactly the map range is
well-formed when it has the requested length and no forwarding pointers. -/
theorem heapOk_gcRelated {α β : Type} (heap heap2 : List (HeapElement α β))
    (f : HolFiniteMapExact Nat Nat) (limit : Nat)
    (related : gcRelated f heap heap2)
    (range : (fun target => ∃ ptr, f.lookup ptr = some target) =
      (fun target => isSomeDataElement (heapLookup target heap2)))
    (size : heapLength heap2 = limit) (noForward : heap2.filter isForwardPointer = []) :
    heapOk heap2 limit := by
  refine ⟨size, noForward, ?_⟩
  intro xs len payload ptr u pair
  obtain ⟨member, childMember⟩ := pair
  obtain ⟨target, found⟩ := mem_imp_heapLookup heap2 (.dataElement xs len payload) member
  have present : isSomeDataElement (heapLookup target heap2) := ⟨xs, len, payload, found⟩
  obtain ⟨old, lookup⟩ := (congrFun range target).mpr present
  have defined : f.lookup old ≠ none := by rw [lookup]; simp
  obtain ⟨oldRoots, oldLen, oldData, oldFound⟩ := related.2.2.1 old defined
  obtain ⟨mappedFound, oldChildren⟩ := related.2.2.2 old oldRoots oldLen oldData defined oldFound
  have mappedEq : holFapply f old = target := holFapply_of_lookup lookup
  rw [mappedEq] at mappedFound
  have same : HeapElement.dataElement (addrMap (holFapply f) oldRoots) oldLen oldData =
      .dataElement xs len payload := Option.some.inj (mappedFound.symm.trans found)
  cases same
  obtain ⟨child, originalMember, childEq⟩ := mem_addrMap oldRoots (holFapply f) ptr u childMember
  rw [← childEq]
  exact related.1 child (oldChildren child u originalMember)

/-- A data-only heap followed by an unused expansion has no forwarding
pointers. This Flapjack lemma supports simple-collector heap well-formedness. -/
theorem filter_forward_heapExpand {α β : Type} (heap : List (HeapElement α β)) (free : Nat)
    (allData : ∀ element ∈ heap, isDataElement element) :
    (heap ++ heapExpand free).filter isForwardPointer = [] := by
  have none : heap.filter isForwardPointer = [] := by
    induction heap with
    | nil => rfl
    | cons head tail ih =>
      have headData := allData head (by simp)
      have tailData : ∀ element ∈ tail, isDataElement element := by
        intro element member
        exact allData element (by simp [member])
      obtain ⟨xs, len, data, rfl⟩ := headData
      simp [isForwardPointer, ih tailData]
  cases free <;> simp [List.filter_append, none, heapExpand, isForwardPointer]

/-- Full copying collection establishes the roots, heap well-formedness,
unused-space, reachability, and length components needed by the simple
collector's abstract memory proof. The stack/reference invariant remains a
separate obligation. -/
theorem fullGc_abstract_structure {α β : Type} (roots : List (HeapAddress α))
    (heap : List (HeapElement α β)) (limit : Nat)
    (rootOk : rootsOk roots heap) (heapGood : heapOk heap limit) :
    ∃ roots2 heap2 a2,
      CopyingGc.fullGc (roots, heap, limit) = (roots2, heap2, a2, true) ∧
      rootsOk roots2 (heap2 ++ heapExpand (limit - a2)) ∧
      heapOk (heap2 ++ heapExpand (limit - a2)) limit ∧
      unusedSpaceInv a2 (limit - a2) (heap2 ++ heapExpand (limit - a2)) ∧
      allReachableFromRoots roots2 (heap2 ++ heapExpand (limit - a2)) ∧
      heapLength (heapFilter (reachableAddresses roots heap) heap) = heapLength heap2 ∧
      (∀ element ∈ heap2, isDataElement element) ∧ heapLength heap2 = a2 := by
  obtain ⟨heap2, a2, heap3, run, rootDomain, invariant⟩ :=
    CopyingGc.fullGc_invariant roots heap limit rootOk heapGood
  let f := heapMap 0 heap3
  have domain := CopyingGc.gcInv_final_domain heap2 heap3 heap a2 (limit - a2) limit true roots invariant rootDomain
  have range := CopyingGc.gcInv_final_range heap2 heap3 heap a2 (limit - a2) limit true roots invariant
  have related := CopyingGc.gcInv_final_related heap2 heap3 heap a2 (limit - a2) limit true roots invariant
  have lengthEq : heapLength heap2 = a2 := by simpa using invariant.2.1.symm
  have allData : ∀ element ∈ heap2, isDataElement element := invariant.2.2.2.2.2.2.2.1
  have filtered := CopyingGc.gcInv_final_filterLength heap2 heap3 heap a2 (limit - a2) limit true roots invariant
  have expandedRel : gcRelated f heap (heap2 ++ heapExpand (limit - a2)) :=
    (gcRelated_append_heapExpand f heap heap2 (limit - a2)).mpr related
  have expandedRange : (fun target => ∃ ptr, f.lookup ptr = some target) =
      (fun target => isSomeDataElement (heapLookup target (heap2 ++ heapExpand (limit - a2)))) := by
    rw [range]
    funext target
    exact propext (isSomeDataElement_heapLookup_expand target heap2 (limit - a2)).symm
  have within : a2 ≤ limit := by have balance := invariant.1; omega
  have expandedSize : heapLength (heap2 ++ heapExpand (limit - a2)) = limit := by
    rw [heapLength_append, heapLength_heapExpand, lengthEq]
    omega
  refine ⟨addrMap (holFapply f) roots, heap2, a2, run, ?_, ?_, ?_, ?_, ?_, allData, lengthEq⟩
  · exact rootsOk_gcRelated roots heap (heap2 ++ heapExpand (limit - a2)) f expandedRel rootDomain
  · exact heapOk_gcRelated heap (heap2 ++ heapExpand (limit - a2)) f limit expandedRel expandedRange
      expandedSize (filter_forward_heapExpand heap2 (limit - a2) allData)
  · simpa [lengthEq] using unusedSpaceInv_heapExpand heap2 (limit - a2) allData
  · exact imp_allReachableFromRoots f roots heap (heap2 ++ heapExpand (limit - a2)) domain expandedRange expandedRel
  · rw [← domain]
    exact filtered.symm

/-- The simple copying collector preserves the combined stack/reference
invariant, including its appended free space. This Flapjack result handles
direct collection; the source's separate thunk-inlining stage remains open. -/
theorem fullGc_stack_reference {width : Nat} [NeZero width]
    (conf : Config) (next : Nat) (stack : List DataSem.Value)
    (refs : Spt (BvlSem.Ref DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (limit : Nat) (bigEndian : Bool)
    (rootOk : rootsOk roots heap) (heapGood : heapOk heap limit)
    (valid : bcStackRefInv conf next stack refs (roots, heap, bigEndian)) :
    ∃ roots2 heap2 a2,
      CopyingGc.fullGc (roots, heap, limit) = (roots2, heap2, a2, true) ∧
      bcStackRefInv conf next stack refs (roots2, heap2 ++ heapExpand (limit - a2), bigEndian) := by
  obtain ⟨heap2, a2, heap3, run, rootDomain, invariant⟩ :=
    CopyingGc.fullGc_invariant roots heap limit rootOk heapGood
  let f := heapMap 0 heap3
  have related := CopyingGc.gcInv_final_related heap2 heap3 heap a2 (limit - a2) limit true roots invariant
  have expanded : gcRelated f heap (heap2 ++ heapExpand (limit - a2)) :=
    (gcRelated_append_heapExpand f heap heap2 (limit - a2)).mpr related
  exact ⟨addrMap (holFapply f) roots, heap2, a2, run,
    bcStackRefInv_gcRelated conf next stack refs roots heap _ bigEndian f expanded rootDomain valid⟩

/-- Simple copying collection re-establishes the entire abstract memory
invariant, with its heap-length and reachability consequences. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "full_gc_thm"
  (words_as_type_indexed_bitvec)]
theorem fullGc_abstract_memory {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width)))
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (bigEndian : Bool) (a sp sp1 : Nat) (gens : GcCombined.GenState) (limit next : Nat)
    (assumptions : absMlInv conf stack refs (roots, heap, bigEndian, a, sp, sp1, gens) limit next ∧
      conf.gcKind = .simple) :
    ∃ roots2 heap2 a2,
      CopyingGc.fullGc (roots, heap, limit) = (roots2, heap2, a2, true) ∧
      absMlInv conf stack refs
        (roots2, heap2 ++ heapExpand (limit - a2), bigEndian, a2, limit - a2, 0, gens) limit next ∧
      heapLength heap2 = a2 ∧
      heapLength (heapFilter (reachableAddresses roots heap) heap) = heapLength heap2 ∧
      allReachableFromRoots roots2 (heap2 ++ heapExpand (limit - a2)) ∧
      List.Forall isDataElement heap2 := by
  obtain ⟨valid, simple⟩ := assumptions
  obtain ⟨rootOk, heapGood, _, _, stackValid⟩ := valid
  obtain ⟨roots2, heap2, a2, run, rootOk2, heapGood2, unused, reachable, filtered, allData, lengthEq⟩ :=
    fullGc_abstract_structure roots heap limit rootOk heapGood
  obtain ⟨roots3, heap3, a3, run3, stackValid3⟩ :=
    fullGc_stack_reference conf next stack refs roots heap limit bigEndian rootOk heapGood stackValid
  have same : (roots2, heap2, a2, true) = (roots3, heap3, a3, true) := run.symm.trans run3
  cases same
  refine ⟨roots2, heap2, a2, run, ⟨rootOk2, heapGood2, ?_, ?_, stackValid3⟩,
    lengthEq, filtered, reachable, List.forall_iff_forall_mem.mpr allData⟩
  · simp [gcKindInv, simple]
  · simpa using unused

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
