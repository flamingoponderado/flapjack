module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.FreshBlockGc
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend

/-- A fitting element can be allocated in unused space, preserving the original heap relations. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "IMP_heap_store_unused_alt"]
theorem heapStoreUnusedAlt_exists {α β : Type} (a sp : Nat) (heap : List (HeapElement α β))
    (x : HeapElement α β) (unused : unusedSpaceInv a sp heap) (fits : elLength x ≤ sp) :
    ∃ heap2, heapStoreUnusedAlt a sp x heap = (heap2,true) ∧
      (isDataElement x → unusedSpaceInv (a + elLength x) (sp - elLength x) heap2) ∧
      heapLookup a heap2 = some x ∧ ¬ isSomeDataElement (heapLookup a heap) ∧
      heapLength heap2 = heapLength heap ∧
      (isForwardPointer x = false → heap2.filter isForwardPointer = heap.filter isForwardPointer) ∧
      (∀ xs l d, .dataElement xs l d ∈ heap2 ↔ x = .dataElement xs l d ∨ .dataElement xs l d ∈ heap) ∧
      (isDataElement x → (fun p => isSomeDataElement (heapLookup p heap2)) =
        (fun p => p = a ∨ isSomeDataElement (heapLookup p heap))) ∧
      heapStoreRel heap heap2 := by
  classical
  have xPos : 0 < elLength x := by cases x <;> simp [elLength]
  have spPos : 0 < sp := by omega
  have found := unused.1 (by omega)
  obtain ⟨pre, post, shape, aEq⟩ := heapLookup_split heap a _ found
  have preData : ∀ element ∈ pre, isDataElement element := by
    apply dataUpTo_prefix_data pre (.unused (sp - 1) :: post)
    simpa [shape, aEq] using unused.2.2
  let rest : List (HeapElement α β) := heapExpand (sp - elLength x)
  let heap2 := pre ++ [x] ++ rest ++ post
  have size : heapLength ([x] ++ rest) = sp := by
    change elLength x + heapLength rest = sp
    rw [show heapLength rest = sp - elLength x from heapLength_heapExpand _]
    omega
  have stored : heapStoreUnusedAlt a sp x heap = (heap2,true) := by
    unfold heapStoreUnusedAlt
    simp only [found, fits, and_self, ↓reduceIte]
    rw [shape, aEq, heapStore_atPrefix]
    have eqLen : heapLength ([x] ++ rest) = elLength (.unused (sp - 1) : HeapElement α β) := by
      rw [size]
      simp [elLength, show sp - 1 + 1 = sp by omega]
    change (pre ++ ([x] ++ rest) ++ post, decide (heapLength ([x] ++ rest) = elLength (.unused (sp - 1) : HeapElement α β))) = (heap2, true)
    have eqLen2 : heapLength (x :: rest) = elLength (.unused (sp - 1) : HeapElement α β) := by
      simpa only [List.singleton_append] using eqLen
    simp [heap2, eqLen2, List.append_assoc]
  have oldNot : ¬ isSomeDataElement (heapLookup a heap) := by
    rw [found]; simp [isSomeDataElement]
  have resultLookup : heapLookup a heap2 = some x := by
    rw [aEq]
    simpa [heap2, rest, List.append_assoc] using heapLookup_prefix pre (rest ++ post) x
  have newInv (isData : isDataElement x) : unusedSpaceInv (a + elLength x) (sp - elLength x) heap2 := by
    have data : ∀ e ∈ pre ++ [x], isDataElement e := by
      intro e member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with h | rfl
      · exact preData e h
      · exact isData
    have result := unusedSpaceInv_heapExpand_suffix (pre ++ [x]) post (sp - elLength x) data
    simpa [heap2, rest, heapLength_append, heapLength, aEq, List.append_assoc] using result
  have lengthEq : heapLength heap2 = heapLength heap := by
    rw [shape]
    change heapLength (pre ++ [x] ++ rest ++ post) = heapLength (pre ++ .unused (sp - 1) :: post)
    rw [show pre ++ [x] ++ rest ++ post = pre ++ ([x] ++ rest) ++ post by simp [List.append_assoc]]
    simp only [heapLength_append, size]
    have hlen : heapLength (.unused (sp - 1) :: post) = (sp - 1 + 1) + heapLength post := rfl
    rw [hlen]
    omega
  have forward (h : isForwardPointer x = false) : heap2.filter isForwardPointer = heap.filter isForwardPointer := by
    cases x <;> simp_all [heap2, rest, heapExpand, List.filter_append, isForwardPointer]
  have members (xs : List (HeapAddress α)) (l : Nat) (d : β) :
      .dataElement xs l d ∈ heap2 ↔ x = .dataElement xs l d ∨ .dataElement xs l d ∈ heap := by
    simp [heap2, rest, shape, heapExpand, List.mem_append, eq_comm, or_left_comm]
  have preserved : heapStoreRel heap heap2 := by
    intro p ⟨xs, n, data, lookup⟩
    have sz : heapLength ([x] ++ rest) = (sp - 1) + 1 := by rw [size]; omega
    have h := heapLookup_allocate_preservesData pre post ([x] ++ rest) (sp - 1) sz p (.dataElement xs n data)
      (by simp [isDataElement]) (by simpa [shape] using lookup)
    simpa [heap2, List.append_assoc, lookup] using h
  refine ⟨heap2, stored, newInv, resultLookup, oldNot, lengthEq, forward, members, ?_, preserved⟩
  intro data
  funext p
  apply propext
  constructor
  · intro h
    by_cases same : p = a
    · exact Or.inl same
    · right
      rw [shape, GenGc.heapLookup_append]
      have hnew : isSomeDataElement (heapLookup p (pre ++ ([x] ++ rest ++ post))) := by
        simpa [heap2, List.append_assoc] using h
      rw [GenGc.heapLookup_append] at hnew
      by_cases before : p < heapLength pre
      · simpa [before] using hnew
      · simp only [before, ↓reduceIte] at hnew ⊢
        have nz : p - heapLength pre ≠ 0 := by omega
        change isSomeDataElement (heapLookup (p - heapLength pre) (x :: (rest ++ post))) at hnew
        have pass := (isSomeData_lookup_cons (p - heapLength pre) x (rest ++ post) nz).mp hnew
        have expanded := (isSomeData_lookup_expand (p - heapLength pre - elLength x)
          (sp - elLength x) post).mp (by simpa [rest] using pass.2)
        apply (isSomeData_lookup_unused (p - heapLength pre) (sp - 1) post).mpr
        constructor
        · omega
        · have eq : p - heapLength pre - elLength x - (sp - elLength x) =
              p - heapLength pre - ((sp - 1) + 1) := by omega
          simpa [eq] using expanded.2
  · intro h
    rcases h with rfl | old
    · rw [resultLookup]
      rcases data with ⟨xs, len, d, rfl⟩
      simp [isSomeDataElement]
    · have eq := preserved p old
      rw [eq]; exact old
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
