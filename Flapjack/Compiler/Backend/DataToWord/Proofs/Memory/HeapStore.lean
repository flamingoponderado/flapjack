import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ArrayUpdateValue

/-! The abstract heap-store operation used by data-to-word memory proofs. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack

/-- Replace the heap element at a word offset with a list of heap elements.
The returned flag records whether the replacement has exactly the old size. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_store_def"]
def heapStore {α β : Type} (offset : Nat) (replacement : List (HeapElement α β)) :
    List (HeapElement α β) → List (HeapElement α β) × Bool
  | [] => ([], false)
  | head :: tail =>
      if offset = 0 then (replacement ++ tail, decide (elLength head = heapLength replacement))
      else if offset < elLength head then (head :: tail, false)
      else let (rest, success) := heapStore (offset - elLength head) replacement tail
        (head :: rest, success)

/-- Storing at a heap-pre boundary replaces exactly the next element and
reports whether its allocated length matches the replacement. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_store_lemma"]
theorem heapStore_atPrefix {α β : Type} (pre replacement : List (HeapElement α β))
    (cell : HeapElement α β) (suffix : List (HeapElement α β)) :
    heapStore (heapLength pre) replacement (pre ++ cell :: suffix) =
      (pre ++ replacement ++ suffix, decide (heapLength replacement = elLength cell)) := by
  induction pre with
  | nil =>
    by_cases same : (replacement.map elLength).sum = elLength cell <;>
      simp [heapStore, heapLength, eq_comm, same]
  | cons head tail ih =>
    have positive : 0 < elLength head := by cases head <;> simp [elLength]
    change heapStore (elLength head + heapLength tail) replacement (head :: (tail ++ cell :: suffix)) = _
    simp only [heapStore, show ¬ elLength head + heapLength tail = 0 by omega, ↓reduceIte,
      show ¬ elLength head + heapLength tail < elLength head by omega, Nat.add_sub_cancel_left, ih]
    rfl

/-- Equal-sized reference blocks can be replaced at their heap-pre boundary. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_store_RefBlock_thm"]
theorem heapStore_refBlock {α β : Type} (pre suffix : List (HeapElement α (HeapTag × List β)))
    (after before : List (HeapAddress α)) :
    after.length = before.length →
      heapStore (heapLength pre) [refBlock after] (pre ++ refBlock before :: suffix) =
        (pre ++ refBlock after :: suffix, true) := by
  intro sameLength
  rw [heapStore_atPrefix]
  simp [heapLength, refBlock, elLength, sameLength]

/-- Equal-sized reference-block replacement preserves data-cell lookup at every
heap offset. Unlike payload-only updates, the pointer fields may change. -/
theorem refBlock_replace_isSomeData {α β : Type} (pre post : List (HeapElement α (HeapTag × List β)))
    (before after : List (HeapAddress α)) (sameLength : before.length = after.length) (offset : Nat) :
    isSomeDataElement (heapLookup offset (pre ++ [refBlock before] ++ post)) ↔
      isSomeDataElement (heapLookup offset (pre ++ [refBlock after] ++ post)) := by
  by_cases here : offset = heapLength pre
  · subst offset
    rw [heapLookup_refBlock_here, heapLookup_refBlock_here]
    simp [isSomeDataElement, refBlock]
  · have size : elLength (refBlock (β := β) before) = elLength (refBlock (β := β) after) := by
      simp [refBlock, elLength, sameLength]
    rw [heapLookup_replace_ne pre post _ _ size offset here]

/-- Storing an equally sized reference block gives an explicit new heap,
preserves other data-cell locations and leaves every other lookup unchanged.
This is Flapjack infrastructure toward the original local heap-store lemma. -/
theorem heapStore_refBlock_effect {α β : Type} (heap : List (HeapElement α (HeapTag × List β)))
    (offset : Nat) (before after : List (HeapAddress α))
    (sameLength : before.length = after.length)
    (found : heapLookup offset heap = some (refBlock before)) :
    ∃ heap2, heapStore offset [refBlock after] heap = (heap2, true) ∧
      refBlockInv heap heap2 ∧ heapLookup offset heap2 = some (refBlock after) ∧
      heapLength heap2 = heapLength heap ∧
      heap2.filter isForwardPointer = heap.filter isForwardPointer ∧
      (∀ pointers len data, .dataElement pointers len data ∈ heap2 →
        .dataElement pointers len data = refBlock after ∨ .dataElement pointers len data ∈ heap) ∧
      (∀ n, isSomeDataElement (heapLookup n heap2) ↔ isSomeDataElement (heapLookup n heap)) ∧
      ∀ n cell, n ≠ offset → heapLookup n heap = some cell → heapLookup n heap2 = some cell := by
  obtain ⟨pre, post, heapEq, offsetEq⟩ := heapLookup_split heap offset _ found
  subst heap
  subst offset
  refine ⟨pre ++ [refBlock after] ++ post, ?_, ?_, heapLookup_refBlock_here pre post after, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [List.append_assoc] using heapStore_refBlock pre post after before sameLength.symm
  · simpa only [List.append_assoc, List.singleton_append] using refBlockInv_replace pre post before after sameLength
  · simp [heapLength, refBlock, elLength, sameLength, List.map_append, List.sum_append]
  · simp [List.filter_append, refBlock, isForwardPointer]
  · intro pointers len data member
    simp only [List.mem_append, List.mem_cons] at member ⊢
    rcases member with (inPre | equal) | inPost <;> simp_all
  · intro n
    simpa only [List.append_assoc, List.singleton_append] using
      (refBlock_replace_isSomeData pre post before after sameLength n).symm
  · intro n cell different old
    have size : elLength (refBlock (β := β) before) = elLength (refBlock (β := β) after) := by
      simp [refBlock, elLength, sameLength]
    rw [← heapLookup_replace_ne pre post _ _ size n different]
    simpa only [List.append_assoc, List.singleton_append] using old

/-- Storing a reference block preserves heap validity when every resulting
pointer was already in the block or appears among the roots. -/
theorem heapStore_refBlock_preservesRootsHeap {α β : Type}
    (heap : List (HeapElement α (HeapTag × List β))) (roots : List (HeapAddress α))
    (offset limit : Nat) (before after : List (HeapAddress α))
    (sameLength : before.length = after.length)
    (found : heapLookup offset heap = some (refBlock before))
    (rootsValid : rootsOk roots heap) (heapValid : heapOk heap limit)
    (newRoots : ∀ address ∈ after, address ∈ roots ∨ address ∈ before) :
    ∃ heap2, heapStore offset [refBlock after] heap = (heap2, true) ∧
      refBlockInv heap heap2 ∧ rootsOk roots heap2 ∧ heapOk heap2 limit := by
  obtain ⟨heap2, stored, unchanged, _, lengths, forwards, members, lookupData, _⟩ :=
    heapStore_refBlock_effect heap offset before after sameLength found
  refine ⟨heap2, stored, unchanged, ?_, ?_⟩
  · intro ptr value member
    exact (lookupData ptr).mpr (rootsValid ptr value member)
  · refine ⟨lengths.trans heapValid.1, forwards.trans heapValid.2.1, ?_⟩
    intro pointers len data ptr value conditions
    rcases members pointers len data conditions.1 with newCell | oldCell
    · have pointersEq : pointers = after := by
        simp only [refBlock, HeapElement.dataElement.injEq] at newCell
        exact newCell.1
      subst pointers
      apply (lookupData ptr).mpr
      rcases newRoots _ conditions.2 with root | old
      · exact rootsValid ptr value root
      · apply heapValid.2.2 before before.length (HeapTag.refTag, []) ptr value
        exact ⟨by simpa [refBlock] using heapLookup_mem heap offset (refBlock before) found, old⟩
    · exact (lookupData ptr).mpr (heapValid.2.2 pointers len data ptr value ⟨oldCell, conditions.2⟩)

/-- Equal cell lengths and matching data-cell classification are enough to
transport heap splits and data-only prefixes, without fixing pointer contents. -/
def HeapCellLayout {α β : Type} (left right : HeapElement α β) : Prop :=
  elLength left = elLength right ∧ (isDataElement left ↔ isDataElement right)

/-- Replacing equal-sized reference blocks preserves cell layout. -/
theorem refBlock_replace_layout {α β : Type} (pre post : List (HeapElement α (HeapTag × List β)))
    (before after : List (HeapAddress α)) (sameLength : before.length = after.length) :
    List.Forall₂ HeapCellLayout (pre ++ [refBlock before] ++ post) (pre ++ [refBlock after] ++ post) := by
  have self (heap : List (HeapElement α (HeapTag × List β))) : List.Forall₂ HeapCellLayout heap heap := by
    induction heap with
    | nil => exact .nil
    | cons head tail ih => exact .cons ⟨rfl, Iff.rfl⟩ ih
  induction pre with
  | nil =>
    refine .cons ⟨?_, ?_⟩ (self post)
    · simp [refBlock, elLength, sameLength]
    · simp [refBlock, isDataElement]
  | cons head tail ih => exact .cons ⟨rfl, Iff.rfl⟩ ih

/-- Data-only prefixes survive equal-sized reference-block replacement. -/
theorem dataUpTo_refBlockReplace {α β : Type} (pre post : List (HeapElement α (HeapTag × List β)))
    (before after : List (HeapAddress α)) (sameLength : before.length = after.length) (offset : Nat)
    (valid : dataUpTo offset (pre ++ [refBlock before] ++ post)) :
    dataUpTo offset (pre ++ [refBlock after] ++ post) := by
  obtain ⟨left, right, split, allData⟩ := valid
  obtain ⟨left2, right2, split2, leftLayout, _⟩ :=
    heapSplit_relation (fun h : HeapCellLayout _ _ => h.1)
      (refBlock_replace_layout pre post before after sameLength) offset left right split
  refine ⟨left2, right2, split2, ?_⟩
  exact forall_mem_of_forall₂ leftLayout (fun h data => h.2.mp data) allData

/-- Equal-sized reference-block updates preserve unused-space bookkeeping. -/
theorem unusedSpaceInv_refBlockReplace {α β : Type} (pre post : List (HeapElement α (HeapTag × List β)))
    (before after : List (HeapAddress α)) (sameLength : before.length = after.length) (offset length : Nat)
    (valid : unusedSpaceInv offset length (pre ++ [refBlock before] ++ post)) :
    unusedSpaceInv offset length (pre ++ [refBlock after] ++ post) := by
  have inv := refBlockInv_replace pre post before after sameLength
  refine ⟨?_, ?_, dataUpTo_refBlockReplace pre post before after sameLength offset valid.2.2⟩
  · intro nonzero
    apply inv.1 offset (.unused (length - 1))
    exact ⟨valid.1 nonzero, by simp [isRefBlock, refBlock]⟩
  · have lengthEq : heapLength (pre ++ [refBlock before] ++ post) =
        heapLength (pre ++ [refBlock after] ++ post) := by
      simp [heapLength, List.map_append, List.sum_append, refBlock, elLength, sameLength]
    rw [← lengthEq]
    exact valid.2.1

/-- Splitting at or before a prefix boundary leaves the first part unchanged
when the following cell is replaced. -/
theorem heapSplit_before_replacement {α β : Type} (pre post : List (HeapElement α β))
    (before after : HeapElement α β) (offset : Nat) (bound : offset ≤ heapLength pre)
    (first second : List (HeapElement α β))
    (split : heapSplit offset (pre ++ before :: post) = some (first, second)) :
    ∃ second2, heapSplit offset (pre ++ after :: post) = some (first, second2) := by
  induction pre generalizing offset first second with
  | nil =>
    have zero : offset = 0 := by simpa [heapLength] using bound
    subst offset
    simp [heapSplit] at split
    obtain ⟨rfl, rfl⟩ := split
    exact ⟨after :: post, by simp [heapSplit]⟩
  | cons head tail ih =>
    by_cases zero : offset = 0
    · subst offset
      simp [heapSplit] at split
      obtain ⟨rfl, rfl⟩ := split
      exact ⟨head :: (tail ++ after :: post), by simp [heapSplit]⟩
    · by_cases inside : offset < elLength head
      · simp [heapSplit, zero, inside] at split
      · have remain : offset - elLength head ≤ heapLength tail := by
          change offset ≤ elLength head + heapLength tail at bound
          omega
        cases tailSplit : heapSplit (offset - elLength head) (tail ++ before :: post) with
        | none => simp [heapSplit, zero, inside, tailSplit] at split
        | some pair =>
          obtain ⟨left, right⟩ := pair
          have eq : (head :: left, right) = (first, second) := by
            simpa [heapSplit, zero, inside, tailSplit] using split
          cases eq
          obtain ⟨right2, split2⟩ := ih _ remain left second tailSplit
          exact ⟨right2, by simp [heapSplit, zero, inside, split2]⟩

/-- If a reference-block update occurs at or after the allocation point,
all generation-start pointer restrictions remain unchanged. -/
theorem genStateOk_refBlockReplace {α β : Type} (pre post : List (HeapElement α (HeapTag × List β)))
    (before after : List (HeapAddress α)) (a refsStart : Nat) (gens : GcCombined.GenState)
    (afterAlloc : a ≤ heapLength pre)
    (valid : genStateOk a refsStart (pre ++ [refBlock before] ++ post) gens) :
    genStateOk a refsStart (pre ++ [refBlock after] ++ post) gens := by
  cases gens with
  | genState _ starts =>
    refine ⟨valid.1, ?_⟩
    intro start member
    obtain ⟨first, second, split, pointers⟩ := valid.2 start member
    have bound : start ≤ heapLength pre := (valid.1 start member).trans afterAlloc
    have split' : heapSplit start (pre ++ refBlock before :: post) = some (first, second) := by
      simpa [List.append_assoc] using split
    obtain ⟨second2, split2⟩ := heapSplit_before_replacement pre post (refBlock before) (refBlock after)
      start bound first second split'
    exact ⟨first, second2, by simpa [List.append_assoc] using split2, pointers⟩

/-- Equal-sized reference blocks preserve both layout and the collector's
mutable-reference classification. -/
theorem refBlock_replace_gcLayout {α β : Type} (pre post : List (HeapElement α (HeapTag × List β)))
    (before after : List (HeapAddress α)) (sameLength : before.length = after.length) :
    List.Forall₂ (fun left right => HeapCellLayout left right ∧ (isRef left ↔ isRef right))
      (pre ++ [refBlock before] ++ post) (pre ++ [refBlock after] ++ post) := by
  have self (heap : List (HeapElement α (HeapTag × List β))) :
      List.Forall₂ (fun left right => HeapCellLayout left right ∧ (isRef left ↔ isRef right)) heap heap := by
    induction heap with
    | nil => exact .nil
    | cons head tail ih => exact .cons ⟨⟨rfl, Iff.rfl⟩, Iff.rfl⟩ ih
  induction pre with
  | nil =>
    refine .cons ⟨⟨?_, ?_⟩, ?_⟩ (self post)
    · simp [refBlock, elLength, sameLength]
    · simp [refBlock, isDataElement]
    · simp [refBlock, isRef, isMutTag]
  | cons head tail ih => exact .cons ⟨⟨rfl, Iff.rfl⟩, Iff.rfl⟩ ih

/-- A reference-block update at or after allocation preserves the complete
garbage-collector invariant, including generational heap partitioning. -/
theorem gcKindInv_refBlockReplace {α β : Type} (conf : Config)
    (pre post : List (HeapElement α (HeapTag × List β))) (before after : List (HeapAddress α))
    (a sp sp1 : Nat) (gens : GcCombined.GenState) (sameLength : before.length = after.length)
    (afterAlloc : a ≤ heapLength pre)
    (valid : gcKindInv conf a sp sp1 gens (pre ++ [refBlock before] ++ post)) :
    gcKindInv conf a sp sp1 gens (pre ++ [refBlock after] ++ post) := by
  cases kind : conf.gcKind with
  | none => simpa [gcKindInv, kind] using valid
  | simple => simpa [gcKindInv, kind] using valid
  | generational sizes =>
    simp only [gcKindInv, kind] at valid ⊢
    obtain ⟨gensOk, first, second, split, noRefs, refs⟩ := valid
    obtain ⟨first2, second2, split2, firstLayout, secondLayout⟩ :=
      heapSplit_relation (fun h : HeapCellLayout _ _ ∧ (_ ↔ _) => h.1.1)
        (refBlock_replace_gcLayout pre post before after sameLength) (a + sp + sp1) first second split
    refine ⟨genStateOk_refBlockReplace pre post before after a (a + sp + sp1) gens afterAlloc gensOk,
      first2, second2, split2, ?_, ?_⟩
    · exact forall_mem_of_forall₂ firstLayout (fun h noRef ref => noRef (h.2.mpr ref)) noRefs
    · exact forall_mem_of_forall₂ secondLayout (fun h ref => h.2.mp ref) refs

/-- A successful heap split decomposes the original heap at the requested
word offset. -/
theorem heapSplit_decomposition {α β : Type} (heap : List (HeapElement α β)) (offset : Nat)
    (first second : List (HeapElement α β))
    (split : heapSplit offset heap = some (first, second)) :
    heap = first ++ second ∧ heapLength first = offset := by
  induction heap generalizing offset first second with
  | nil =>
    by_cases zero : offset = 0
    · subst offset
      simp [heapSplit] at split
      obtain ⟨rfl, rfl⟩ := split
      simp [heapLength]
    · simp [heapSplit, zero] at split
  | cons head tail ih =>
    by_cases zero : offset = 0
    · subst offset
      simp [heapSplit] at split
      obtain ⟨rfl, rfl⟩ := split
      simp [heapLength]
    · by_cases inside : offset < elLength head
      · simp [heapSplit, zero, inside] at split
      · cases tailSplit : heapSplit (offset - elLength head) tail with
        | none => simp [heapSplit, zero, inside, tailSplit] at split
        | some pair =>
          obtain ⟨left, right⟩ := pair
          have eq : (head :: left, right) = (first, second) := by
            simpa [heapSplit, zero, inside, tailSplit] using split
          cases eq
          obtain ⟨heapEq, lengthEq⟩ := ih _ left second tailSplit
          constructor
          · simp [heapEq]
          · change elLength head + heapLength left = offset
            omega

/-- A successful lookup strictly before a heap prefix's end belongs to that
prefix, even when the full heap has an additional suffix. -/
theorem heapLookup_mem_beforePrefix {α β : Type} (pre post : List (HeapElement α β))
    (offset : Nat) (cell : HeapElement α β) (bound : offset < heapLength pre)
    (found : heapLookup offset (pre ++ post) = some cell) : cell ∈ pre := by
  induction pre generalizing offset with
  | nil => simp [heapLength] at bound
  | cons head tail ih =>
    by_cases zero : offset = 0
    · subst offset
      simp [heapLookup] at found
      simp [found]
    · by_cases inside : offset < elLength head
      · simp [heapLookup, zero, inside] at found
      · have remain : offset - elLength head < heapLength tail := by
          change offset < elLength head + heapLength tail at bound
          omega
        have tailFound : heapLookup (offset - elLength head) (tail ++ post) = some cell := by
          simpa [heapLookup, zero, inside] using found
        exact List.mem_cons_of_mem head (ih _ remain tailFound)

/-- In a generational heap, every reference block lies at or beyond the
collector's reference boundary: the preceding partition contains no refs. -/
theorem gcKindInv_refBlock_afterBoundary {α β : Type} (conf : Config) (sizes : List Nat)
    (heap : List (HeapElement α (HeapTag × List β))) (a sp sp1 : Nat) (gens : GcCombined.GenState)
    (ptr : Nat) (pointers : List (HeapAddress α)) (kind : conf.gcKind = .generational sizes)
    (valid : gcKindInv conf a sp sp1 gens heap) (found : heapLookup ptr heap = some (refBlock pointers)) :
    a + sp + sp1 ≤ ptr := by
  simp only [gcKindInv, kind] at valid
  obtain ⟨_, first, second, split, noRefs, _⟩ := valid
  obtain ⟨heapEq, lengthEq⟩ := heapSplit_decomposition heap (a + sp + sp1) first second split
  by_contra notAfter
  have before : ptr < heapLength first := by omega
  have member : refBlock pointers ∈ first := heapLookup_mem_beforePrefix first second ptr _ before (by simpa [heapEq] using found)
  have notRef := noRefs _ member
  apply notRef
  simp [isRef, isMutTag, refBlock]

/-- The existing GC invariant itself supplies the allocation-position fact in
the generational case, so no separate bound is needed for a reference update. -/
theorem gcKindInv_refBlockReplace_of_valid {α β : Type} (conf : Config)
    (pre post : List (HeapElement α (HeapTag × List β))) (before after : List (HeapAddress α))
    (a sp sp1 : Nat) (gens : GcCombined.GenState) (sameLength : before.length = after.length)
    (valid : gcKindInv conf a sp sp1 gens (pre ++ [refBlock before] ++ post)) :
    gcKindInv conf a sp sp1 gens (pre ++ [refBlock after] ++ post) := by
  cases kind : conf.gcKind with
  | none => simpa [gcKindInv, kind] using valid
  | simple => simpa [gcKindInv, kind] using valid
  | generational sizes =>
    have afterBoundary := gcKindInv_refBlock_afterBoundary conf sizes _ a sp sp1 gens
      (heapLength pre) before kind valid (heapLookup_refBlock_here pre post before)
    have afterAlloc : a ≤ heapLength pre := by omega
    exact gcKindInv_refBlockReplace conf pre post before after a sp sp1 gens sameLength afterAlloc valid

/-- All heap-side abstract invariants survive an equal-sized reference-block
update whose new pointers are roots; the GC case derives its own location bound. -/
theorem refBlockReplace_heapInvariants {α β : Type} (conf : Config)
    (pre post : List (HeapElement α (HeapTag × List β))) (roots : List (HeapAddress α))
    (before after : List (HeapAddress α)) (a sp sp1 limit : Nat) (gens : GcCombined.GenState)
    (sameLength : before.length = after.length)
    (rootsValid : rootsOk roots (pre ++ [refBlock before] ++ post))
    (heapValid : heapOk (pre ++ [refBlock before] ++ post) limit)
    (gcValid : gcKindInv conf a sp sp1 gens (pre ++ [refBlock before] ++ post))
    (unused : unusedSpaceInv a (sp + sp1) (pre ++ [refBlock before] ++ post))
    (newRoots : ∀ address ∈ after, address ∈ roots ∨ address ∈ before) :
    rootsOk roots (pre ++ [refBlock after] ++ post) ∧
      heapOk (pre ++ [refBlock after] ++ post) limit ∧
      gcKindInv conf a sp sp1 gens (pre ++ [refBlock after] ++ post) ∧
      unusedSpaceInv a (sp + sp1) (pre ++ [refBlock after] ++ post) := by
  obtain ⟨heap2, stored, _, rootNew, heapNew⟩ :=
    heapStore_refBlock_preservesRootsHeap (pre ++ [refBlock before] ++ post) roots (heapLength pre) limit
      before after sameLength (heapLookup_refBlock_here pre post before) rootsValid heapValid newRoots
  have canonical : heap2 = pre ++ [refBlock after] ++ post := by
    have exactStore := heapStore_refBlock pre post after before sameLength.symm
    simp only [List.append_assoc, List.singleton_append] at exactStore stored ⊢
    rw [exactStore] at stored
    exact (Prod.mk.inj stored).1.symm
  subst heap2
  exact ⟨rootNew, heapNew, gcKindInv_refBlockReplace_of_valid conf pre post before after a sp sp1 gens sameLength gcValid,
    unusedSpaceInv_refBlockReplace pre post before after sameLength a (sp + sp1) unused⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
