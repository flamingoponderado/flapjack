import Flapjack.Compiler.Backend.GcShared.HeapMap.Properties
import Mathlib.Data.List.Forall2

/-! The source heap and its forwarding-pointer version. -/
namespace Flapjack.Compiler.Backend

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
