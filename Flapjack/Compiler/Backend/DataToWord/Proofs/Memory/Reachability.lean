module

public import Flapjack.Compiler.Backend.GcShared.Reachability
public import Flapjack.Compiler.Backend.GcShared.Related
public import Flapjack.Compiler.Backend.GenGc.Proofs.HeapLookup

@[expose] public section

/-! Abstract collector reachability conditions. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend

/-- Every data element in a heap is reachable from its roots. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_reachable_from_roots_def"]
def allReachableFromRoots {α β γ : Type} (roots : List (HeapAddress α)) (heap : List (HeapElement β γ)) : Prop :=
  ∀ ptr children len payload, heapLookup ptr heap = some (.dataElement children len payload) →
    reachableAddresses roots heap ptr

/-- Appending unused space neither creates nor hides a data-element lookup. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_lookup_expand_eq_SOME"]
theorem heapLookup_expand_eq_some {α β : Type} (a : Nat) (heap : List (HeapElement α β))
    (n : Nat) (ys : List (HeapAddress α)) (len : Nat) (data : β) :
    heapLookup a (heap ++ heapExpand n) = some (.dataElement ys len data) ↔
      heapLookup a heap = some (.dataElement ys len data) := by
  rw [GenGc.heapLookup_append]
  by_cases below : a < heapLength heap
  · simp [below]
  · have noLookup : heapLookup a heap ≠ some (.dataElement ys len data) := by
      intro found
      exact below (heapLookup_less heap a _ found)
    simp only [below, if_false, noLookup, iff_false]
    cases n <;> simp [heapExpand, heapLookup]

/-- Data-element presence is unchanged by appending unused space. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "isSomeDataElement_heap_lookup" 1256]
theorem isSomeDataElement_heapLookup_expand {α β : Type} (a : Nat)
    (heap : List (HeapElement α β)) (n : Nat) :
    isSomeDataElement (heapLookup a (heap ++ heapExpand n)) ↔
      isSomeDataElement (heapLookup a heap) := by
  simp only [isSomeDataElement, heapLookup_expand_eq_some]

/-- The collector map parameter has the same canonical lookup and support
after converting through its explicit representation. -/
theorem holFmapAsFiniteSupportParamWitness_gcRelated_append_heapExpand_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (GcMapBroad.ofBroad (GcMapBroad.toBroad f)).lookup key = f.lookup key ∧
    (GcMapBroad.ofBroad (GcMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    GcMapBroad.ofBroad (GcMapBroad.toBroad f) = f :=
  holFmapAsFiniteSupportParamWitness_gcRelated_f f key

/-- Appending unused space preserves the abstract collector heap relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gc_related_APPEND_heap_expand"
  (fmap_as_finite_support_parameters := [f])]
theorem gcRelated_append_heapExpand {α β : Type} (f : HolFiniteMapExact Nat Nat)
    (heap heap2 : List (HeapElement α β)) (n : Nat) :
    gcRelated f heap (heap2 ++ heapExpand n) ↔ gcRelated f heap heap2 := by
  simp only [gcRelated, isSomeDataElement_heapLookup_expand, heapLookup_expand_eq_some]

private theorem pointer_mem_addrMap {α : Type} (f : Nat → Nat) (xs : List (HeapAddress α))
    (ptr : Nat) (value : α) (member : .pointer ptr value ∈ xs) :
    .pointer (f ptr) value ∈ addrMap f xs := by
  induction xs with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.mem_cons] at member
    rcases member with same | member
    · subst head
      simp [addrMap]
    · cases head <;> simp [addrMap, ih member]

/-- The canonical finite-map codec preserves lookup and support. -/
theorem holFmapAsFiniteSupportParamWitness_reachableAddresses_related_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (GcMapBroad.ofBroad (GcMapBroad.toBroad f)).lookup key = f.lookup key ∧
    (GcMapBroad.ofBroad (GcMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    GcMapBroad.ofBroad (GcMapBroad.toBroad f) = f :=
  holFmapAsFiniteSupportParamWitness_gcRelated_f f key

/-- A related collector heap preserves reachability under address renaming. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "reachable_addresses_related"
  (fmap_as_finite_support_parameters := [f])]
theorem reachableAddresses_related {α β γ : Type} (k : Nat) (roots : List (HeapAddress α))
    (heap heap2 : List (HeapElement β γ)) (f : HolFiniteMapExact Nat Nat)
    (reachable : reachableAddresses roots heap k) (related : gcRelated f heap heap2)
    (domain : ∀ p, reachableAddresses roots heap p → f.lookup p ≠ none) :
    reachableAddresses (addrMap (holFapply f) roots) heap2 (holFapply f k) := by
  obtain ⟨value, source, rootMember, path⟩ := reachable
  refine ⟨value, holFapply f source, pointer_mem_addrMap _ _ _ _ rootMember, ?_⟩
  induction path with
  | refl => exact .refl
  | @tail middle target path edge ih =>
    have middleDomain : f.lookup middle ≠ none :=
      domain middle ⟨value, source, rootMember, path⟩
    obtain ⟨children, len, payload, pointerValue, found, member⟩ := edge
    obtain ⟨mappedFound, _⟩ := related.2.2.2 middle children len payload middleDomain found
    exact ih.tail ⟨addrMap (holFapply f) children, len, payload, pointerValue,
      mappedFound, pointer_mem_addrMap _ _ _ _ member⟩

/-- The canonical finite-map codec preserves lookup and support. -/
theorem holFmapAsFiniteSupportParamWitness_imp_allReachableFromRoots_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (GcMapBroad.ofBroad (GcMapBroad.toBroad f)).lookup key = f.lookup key ∧
    (GcMapBroad.ofBroad (GcMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    GcMapBroad.ofBroad (GcMapBroad.toBroad f) = f :=
  holFmapAsFiniteSupportParamWitness_gcRelated_f f key

/-- A collector mapping precisely the reachable addresses onto the new data
elements makes every data element in the new heap reachable. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "IMP_all_reachable_from_roots"
  (fmap_as_finite_support_parameters := [f])]
theorem imp_allReachableFromRoots {α β γ : Type} (f : HolFiniteMapExact Nat Nat)
    (roots : List (HeapAddress α)) (heap heap2 : List (HeapElement β γ))
    (domain : (fun p => f.lookup p ≠ none) = reachableAddresses roots heap)
    (range : (fun p => ∃ x, f.lookup x = some p) =
      (fun p => isSomeDataElement (heapLookup p heap2)))
    (related : gcRelated f heap heap2) :
    allReachableFromRoots (addrMap (holFapply f) roots) heap2 := by
  intro ptr children len payload found
  have present : isSomeDataElement (heapLookup ptr heap2) := ⟨children, len, payload, found⟩
  have inRange : ∃ x, f.lookup x = some ptr := (congrFun range ptr).mpr present
  obtain ⟨x, lookup⟩ := inRange
  have xDomain : f.lookup x ≠ none := by simp [lookup]
  have xReachable : reachableAddresses roots heap x := by
    rw [← domain]
    exact xDomain
  have subset : ∀ p, reachableAddresses roots heap p → f.lookup p ≠ none := by
    intro p reach
    exact (congrFun domain p).mpr reach
  have mapped := reachableAddresses_related x roots heap heap2 f xReachable related subset
  simpa [holFapply_of_lookup lookup] using mapped

/-- Unused space introduces no edges into the abstract heap graph. This
Flapjack-specific consequence supports the collector reachability proof. -/
theorem gcEdge_heapExpand {α β : Type} (heap : List (HeapElement α β)) (n source target : Nat) :
    gcEdge (heap ++ heapExpand n) source target ↔ gcEdge heap source target := by
  simp only [gcEdge, heapLookup_expand_eq_some]

/-- Heap graph reachability is unchanged by appending unused space. -/
theorem reachableAddresses_heapExpand {α β γ : Type} (roots : List (HeapAddress α))
    (heap : List (HeapElement β γ)) (n target : Nat) :
    reachableAddresses roots (heap ++ heapExpand n) target ↔ reachableAddresses roots heap target := by
  have edgeEq : gcEdge (heap ++ heapExpand n) = gcEdge heap := by
    funext source target
    exact propext (gcEdge_heapExpand heap n source target)
  simp only [reachableAddresses, edgeEq]

/-- All-data reachability survives appending unused space. -/
theorem allReachableFromRoots_heapExpand {α β γ : Type} (roots : List (HeapAddress α))
    (heap : List (HeapElement β γ)) (n : Nat) :
    allReachableFromRoots roots (heap ++ heapExpand n) ↔ allReachableFromRoots roots heap := by
  simp only [allReachableFromRoots, heapLookup_expand_eq_some, reachableAddresses_heapExpand]

/-- Starting addresses of data elements in a heap. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "data_pointers_def"]
def dataPointers {α β : Type} : List (HeapElement α β) → List Nat
  | [] => []
  | .dataElement roots len payload :: tail =>
    0 :: (dataPointers tail).map (fun offset => offset + elLength (.dataElement roots len payload))
  | head :: tail => (dataPointers tail).map (fun offset => offset + elLength head)

/-- Encoded length of the element at an address, or zero if none starts there. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "lookup_len_def"]
def lookupLen {α β : Type} (heap : List (HeapElement α β)) (ptr : Nat) : Nat :=
  match heapLookup ptr heap with
  | none => 0
  | some element => elLength element

/-- Total encoded size at the data-element addresses. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "data_length_def"]
def dataLength {α β : Type} (heap : List (HeapElement α β)) : Nat :=
  ((dataPointers heap).map (lookupLen heap)).sum

/-- Appending an unused heap expansion adds no data addresses. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "data_pointers_heap_expand"]
theorem dataPointers_heapExpand {α β : Type} (heap : List (HeapElement α β)) (n : Nat) :
    dataPointers (heap ++ heapExpand n) = dataPointers heap := by
  have empty : dataPointers (heapExpand n : List (HeapElement α β)) = [] := by
    cases n <;> simp [heapExpand, dataPointers]
  induction heap with
  | nil => simpa [dataPointers] using empty
  | cons head tail ih => cases head <;> simp [dataPointers, ih]

/-- A heap expansion contains no data elements. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "data_length_heap_expand"]
theorem dataLength_heapExpand {α β : Type} (n : Nat) :
    dataLength (heapExpand n : List (HeapElement α β)) = 0 := by
  cases n <;> simp [dataLength, heapExpand, dataPointers]

/-- Looking up beyond a leading element is a lookup in its tail. -/
theorem lookupLen_cons_shift {α β : Type} (head : HeapElement α β) (tail : List (HeapElement α β)) (n : Nat) :
    lookupLen (head :: tail) (n + elLength head) = lookupLen tail n := by
  have positive : 0 < elLength head := by cases head <;> simp [elLength]
  have notZero : n + elLength head ≠ 0 := by omega
  have notInside : ¬ n + elLength head < elLength head := by omega
  simp only [lookupLen, heapLookup, notZero, notInside, if_false, Nat.add_sub_cancel]

/-- Data length is additive across the head of a heap. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "data_length_CONS"]
theorem dataLength_cons {α β : Type} (head : HeapElement α β) (tail : List (HeapElement α β)) :
    dataLength (head :: tail) = dataLength [head] + dataLength tail := by
  cases head <;>
    simp only [dataLength, dataPointers, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.map_map, Function.comp_def, lookupLen_cons_shift] <;>
    simp [lookupLen, heapLookup] <;> rfl

/-- Data length is additive under heap concatenation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "data_length_APPEND"]
theorem dataLength_append {α β : Type} (xs ys : List (HeapElement α β)) :
    dataLength (xs ++ ys) = dataLength xs + dataLength ys := by
  induction xs with
  | nil => simp [dataLength, dataPointers]
  | cons head tail ih =>
    rw [List.cons_append, dataLength_cons head (tail ++ ys), ih, dataLength_cons head tail,
      Nat.add_assoc]

/-- Appending unused space preserves data length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "data_length_APPEND_heap_expand"]
theorem dataLength_append_heapExpand {α β : Type} (heap : List (HeapElement α β)) (n : Nat) :
    dataLength (heap ++ heapExpand n) = dataLength heap := by
  simp [dataLength_append, dataLength_heapExpand]

/-- A heap consisting entirely of data elements has no non-data length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "data_length_heap_length"]
theorem dataLength_heapLength {α β : Type} (heap : List (HeapElement α β))
    (allData : ∀ element ∈ heap, isDataElement element) :
    dataLength heap = heapLength heap := by
  induction heap with
  | nil => simp [dataLength, dataPointers, heapLength]
  | cons head tail ih =>
    have headData : isDataElement head := allData head (by simp)
    have tailData : ∀ element ∈ tail, isDataElement element := by
      intro element member
      exact allData element (by simp [member])
    obtain ⟨ptrs, len, payload, rfl⟩ := headData
    rw [dataLength_cons, ih tailData]
    simp [dataLength, dataPointers, lookupLen, heapLookup, heapLength, elLength]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
