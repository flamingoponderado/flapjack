import Flapjack.Compiler.Backend.GcShared.HeapMap.Properties
import Flapjack.Compiler.Backend.GenGc.Proofs.HeapLookup
import Mathlib.Data.List.Forall2

/-! The source heap and its forwarding-pointer version. -/
namespace Flapjack.Compiler.Backend

/-- Recognize a successful forwarding-pointer lookup. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "isSomeForwardPointer_def"]
def isSomeForwardPointer {α β : Type} (element : Option (HeapElement α β)) : Prop :=
  ∃ ptr value len, element = some (.forwardPointer ptr value len)

/-- Recognize a successful data-element or forwarding-pointer lookup. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "isSomeDataOrForward_def"]
def isSomeDataOrForward {α β : Type} (element : Option (HeapElement α β)) : Prop :=
  isSomeForwardPointer element ∨ isSomeDataElement element

/-- Looking up the boundary after a prefix returns its next element. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_lookup_PREFIX"]
theorem heapLookup_prefix {α β : Type} (xs ys : List (HeapElement α β)) (x : HeapElement α β) :
    heapLookup (heapLength xs) (xs ++ x :: ys) = some x := by
  rw [GenGc.heapLookup_append]
  simp [heapLookup]

/-- Appending a heap does not change an existing successful lookup. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_lookup_EXTEND"]
theorem heapLookup_extend {α β : Type} (xs ys : List (HeapElement α β)) (n : Nat)
    (x : HeapElement α β) (found : heapLookup n xs = some x) :
    heapLookup n (xs ++ ys) = some x := by
  rw [GenGc.heapLookup_append]
  simp [heapLookup_less xs n x found, found]

/-- Replacing a data element with a same-size forwarding pointer preserves
whether any heap lookup finds data or a forwarding pointer. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "isSomeDataOrForward_lemma"]
theorem isSomeDataOrForward_replace {α β : Type} (ha hb : List (HeapElement α β))
    (ptr target len : Nat) (ys : List (HeapAddress α)) (data : β) (u : α) :
    isSomeDataOrForward (heapLookup ptr (ha ++ .dataElement ys len data :: hb)) ↔
      isSomeDataOrForward (heapLookup ptr (ha ++ [.forwardPointer target u len] ++ hb)) := by
  rw [List.append_assoc]
  simp only [List.singleton_append]
  rw [GenGc.heapLookup_append ptr ha, GenGc.heapLookup_append ptr ha]
  by_cases below : ptr < heapLength ha
  · simp [below]
  · simp only [below, if_false]
    by_cases zero : ptr - heapLength ha = 0
    · simp [heapLookup, zero, isSomeDataOrForward, isSomeDataElement, isSomeForwardPointer]
    · by_cases inside : ptr - heapLength ha < len + 1
      · simp [heapLookup, zero, elLength, inside, isSomeDataOrForward,
          isSomeDataElement, isSomeForwardPointer]
      · simp [heapLookup, zero, elLength, inside]

/-- A forwarded element preserves the original data element's size; all
other elements remain unchanged. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heaps_similar_def"]
def heapsSimilar {α β : Type} (original current : List (HeapElement α β)) : Prop :=
  List.Forall₂ (fun old now =>
    if isForwardPointer now then elLength now = elLength old ∧ isDataElement old
    else now = old) original current

/-- If no element is a forwarding pointer, filtering for non-forwarding
elements retains the whole heap. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "FILTER_LEMMA"]
theorem filter_notForward {α β : Type} (heap : List (HeapElement α β))
    (noForward : heap.filter isForwardPointer = []) :
    heap.filter (fun h => !(isForwardPointer h)) = heap := by
  induction heap with
  | nil => rfl
  | cons head tail ih =>
    cases head with
    | unused len =>
      simp only [List.filter_cons, isForwardPointer, Bool.false_eq_true, ↓reduceIte] at noForward
      simpa [isForwardPointer] using ih noForward
    | forwardPointer ptr value len => simp [isForwardPointer] at noForward
    | dataElement roots len data =>
      simp only [List.filter_cons, isForwardPointer, Bool.false_eq_true, ↓reduceIte] at noForward
      simpa [isForwardPointer] using ih noForward

/-- A heap without forwarding pointers is similar to itself. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heaps_similar_REFL"]
theorem heapsSimilar_refl {α β : Type} (heap : List (HeapElement α β))
    (noForward : heap.filter isForwardPointer = []) : heapsSimilar heap heap := by
  induction heap with
  | nil => exact .nil
  | cons head tail ih =>
    cases head with
    | unused len =>
      simp only [List.filter_cons, isForwardPointer, Bool.false_eq_true, ↓reduceIte] at noForward
      exact .cons rfl (ih noForward)
    | forwardPointer ptr value len => simp [isForwardPointer] at noForward
    | dataElement roots len data =>
      simp only [List.filter_cons, isForwardPointer, Bool.false_eq_true, ↓reduceIte] at noForward
      exact .cons rfl (ih noForward)

/-- Similar heaps occupy the same number of words. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heaps_similar_IMP_heap_length"]
theorem heapsSimilar_imp_heapLength {α β : Type} (xs ys : List (HeapElement α β))
    (similar : heapsSimilar xs ys) : heapLength xs = heapLength ys := by
  induction similar with
  | nil => rfl
  | @cons old now xs ys head tail ih =>
    have lengthEq : elLength old = elLength now := by
      cases now <;> simp [isForwardPointer] at head ⊢
      · subst old; rfl
      · exact head.1.symm
      · subst old; rfl
    simp only [heapLength, List.map_cons, List.sum_cons] at ih ⊢
    rw [lengthEq, ih]

/-- Data elements in the original heap remain data elements or become
forwarding pointers at the same address in a similar heap. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_similar_Data_IMP_DataOrForward"]
theorem heapSimilar_data_imp_dataOrForward {α β : Type} (heap0 heap1 : List (HeapElement α β))
    (ptr : Nat) (similar : heapsSimilar heap0 heap1)
    (present : isSomeDataElement (heapLookup ptr heap0)) :
    isSomeDataOrForward (heapLookup ptr heap1) := by
  induction similar generalizing ptr with
  | nil => simp [heapLookup, isSomeDataElement] at present
  | @cons old now oldTail nowTail head tail ih =>
    have lengthEq : elLength old = elLength now := by
      cases now <;> simp [isForwardPointer] at head ⊢
      · subst old; rfl
      · exact head.1.symm
      · subst old; rfl
    by_cases zero : ptr = 0
    · subst ptr
      simp only [heapLookup, if_true, isSomeDataElement, Option.some.injEq] at present
      obtain ⟨xs, len, data, oldEq⟩ := present
      subst old
      cases now with
      | unused n => simp [isForwardPointer] at head
      | forwardPointer target value len =>
        exact Or.inl ⟨target, value, len, by simp [heapLookup]⟩
      | dataElement children len payload =>
        exact Or.inr ⟨children, len, payload, by simp [heapLookup]⟩
    · by_cases inside : ptr < elLength old
      · simp [heapLookup, zero, inside, isSomeDataElement] at present
      · have next : isSomeDataElement (heapLookup (ptr - elLength old) oldTail) := by
          simpa only [heapLookup, zero, inside, if_false] using present
        have notInside : ¬ ptr < elLength now := by simpa [← lengthEq] using inside
        simpa only [heapLookup, zero, notInside, inside, if_false, ← lengthEq] using ih _ next

/-- A data element in the current heap occurs at the same boundary in the
original heap. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_similar_Data_IMP"]
theorem heapSimilar_data_imp {α β : Type} (heap0 ha hb : List (HeapElement α β))
    (ys : List (HeapAddress α)) (len : Nat) (data : β)
    (similar : heapsSimilar heap0 (ha ++ .dataElement ys len data :: hb)) :
    ∃ ha0 hb0, heap0 = ha0 ++ .dataElement ys len data :: hb0 ∧
      heapLength ha = heapLength ha0 := by
  induction ha generalizing heap0 with
  | nil =>
    cases heap0 with
    | nil => simp [heapsSimilar] at similar
    | cons head tail =>
      simp only [List.nil_append, heapsSimilar] at similar
      cases similar with
      | cons headRel tailRel =>
        simp only [isForwardPointer, Bool.false_eq_true, ↓reduceIte] at headRel
        subst head
        exact ⟨[], tail, rfl, rfl⟩
  | cons head tail ih =>
    cases heap0 with
    | nil => simp [heapsSimilar] at similar
    | cons old rest =>
      simp only [List.cons_append, heapsSimilar] at similar
      cases similar with
      | cons headRel tailRel =>
        obtain ⟨before, after, eq, lengthEq⟩ := ih rest tailRel
        refine ⟨old :: before, after, ?_, ?_⟩
        · simp [eq]
        · have headLength : elLength head = elLength old := by
            cases head <;> simp [isForwardPointer] at headRel ⊢
            · subst old; rfl
            · exact headRel.1
            · subst old; rfl
          simp only [heapLength, List.map_cons, List.sum_cons] at lengthEq ⊢
          rw [headLength, lengthEq]

/-- Replacing a data element with a same-size forwarding pointer preserves
heap similarity. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heaps_similar_lemma"]
theorem heapsSimilar_forward {α β γ δ : Type} (ha heap0 hb : List (HeapElement α β))
    (h1 h2 : List (HeapElement γ δ))
    (ys : List (HeapAddress α)) (len : Nat) (data : β) (u : α)
    (similar : heapsSimilar heap0 (ha ++ .dataElement ys len data :: hb)) :
    heapsSimilar heap0 (ha ++ [.forwardPointer (heapLength (h1 ++ h2)) u len] ++ hb) := by
  induction ha generalizing heap0 with
  | nil =>
    cases heap0 with
    | nil => simp [heapsSimilar] at similar
    | cons old rest =>
      simp only [List.nil_append, heapsSimilar] at similar ⊢
      cases similar with
      | cons headRel tailRel =>
        simp only [isForwardPointer, Bool.false_eq_true, ↓reduceIte] at headRel
        subst old
        apply List.Forall₂.cons
        · simp [isForwardPointer, elLength, isDataElement]
        · exact tailRel
  | cons head tail ih =>
    cases heap0 with
    | nil => simp [heapsSimilar] at similar
    | cons old rest =>
      simp only [List.cons_append, heapsSimilar] at similar ⊢
      cases similar with
      | cons headRel tailRel => exact List.Forall₂.cons headRel (ih rest tailRel)

end Flapjack.Compiler.Backend
