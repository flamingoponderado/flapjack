import Flapjack.Compiler.Backend.GenGcPartial
import Flapjack.Compiler.Backend.GenGc
import Mathlib.Data.List.Basic

/-! Translation from a partial collector state to a major collector state. -/
namespace Flapjack.Compiler.Backend.GenGcPartial

/-- Values outside the collected generation are protected, while values in
the collected generation remain ordinary values. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "data_sort"]
inductive DataSort (α β : Type) where
  | protectedValue : α → DataSort α β
  | real : β → DataSort α β

/-- Translate pointers to the major collector's local address space. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "to_gen_heap_address_def"]
def toGenHeapAddress {α β : Type} (conf : Config β) :
    HeapAddress α → HeapAddress (DataSort (HeapAddress α) α)
  | .data a => .data (.real a)
  | .pointer ptr a =>
    if ptr < conf.genStart then .data (.protectedValue (.pointer ptr a))
    else if conf.refsStart ≤ ptr then .data (.protectedValue (.pointer ptr a))
    else .pointer (ptr - conf.genStart) (.real a)

/-- Restrict the major collector limit to the current generation. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "to_gen_conf_def"]
def toGenConf {β : Type} (conf : Config β) : GenGc.Config β :=
  ⟨conf.limit - conf.genStart - (conf.limit - conf.refsStart), conf.isRef⟩

/-- Translate one heap element, preserving its payload and encoded size. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "to_gen_heap_element_def"]
def toGenHeapElement {α β γ : Type} (conf : Config γ) :
    HeapElement α β → HeapElement (DataSort (HeapAddress α) α) β
  | .unused n => .unused n
  | .forwardPointer ptr a len => .forwardPointer (ptr - conf.genStart) (.real a) len
  | .dataElement ptrs len payload => .dataElement (ptrs.map (toGenHeapAddress conf)) len payload

/-- Translate a list of heap elements. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "to_gen_heap_list_def"]
def toGenHeapList {α β γ : Type} (conf : Config γ) (heap : List (HeapElement α β)) :
    List (HeapElement (DataSort (HeapAddress α) α) β) := heap.map (toGenHeapElement conf)

/-- Translate the current-generation segment of an entire heap. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "to_gen_heap_def"]
def toGenHeap {α β γ : Type} (conf : Config γ) (heap : List (HeapElement α β)) :
    List (HeapElement (DataSort (HeapAddress α) α) β) :=
  toGenHeapList conf (heapRestrict conf.genStart conf.refsStart heap)

/-- Translate the data segments and source heaps of a partial state. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "to_gen_state_def"]
def toGenState {α β γ : Type} (conf : Config γ) (state : GcState α β) :
    GcState (DataSort (HeapAddress α) α) β :=
  { emptyGcState with
    h1 := toGenHeapList conf state.h1, h2 := toGenHeapList conf state.h2,
    r4 := [], r3 := [], r2 := [], r1 := [], a := state.a - conf.genStart, n := state.n,
    ok := state.ok, heap := toGenHeap conf state.heap, heap0 := toGenHeap conf state.heap0 }

/-- Translate roots to the major collector's address space. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "to_gen_roots_def"]
def toGenRoots {α β : Type} (conf : Config β) (roots : List (HeapAddress α)) :
    List (HeapAddress (DataSort (HeapAddress α) α)) := roots.map (toGenHeapAddress conf)

/-- Extract and translate children from reference elements. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "refs_to_roots_def"]
def refsToRoots {α β γ : Type} (conf : Config β) : List (HeapElement α γ) →
    List (HeapAddress (DataSort (HeapAddress α) α))
  | [] => []
  | .dataElement ptrs _ _ :: refs => ptrs.map (toGenHeapAddress conf) ++ refsToRoots conf refs
  | _ :: refs => refsToRoots conf refs

/-- Test whether a heap element is a reference according to the collector. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "heap_element_is_ref_def"]
def heapElementIsRef {α β : Type} (conf : Config β) : HeapElement α β → Bool
  | .dataElement _ _ payload => conf.isRef payload
  | _ => false

/-- Heap-generation constraints required by the partial collector. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "heap_gen_ok_def"]
def heapGenOk {α β : Type} (heap : List (HeapElement α β)) (conf : Config β) : Prop :=
  ∃ old current refs,
    conf.genStart ≤ conf.refsStart ∧ conf.refsStart ≤ conf.limit ∧
    List.Forall isDataElement old ∧ List.Forall isDataElement refs ∧
    some (old, current, refs) = heapSegment (conf.genStart, conf.refsStart) heap ∧
    (∀ ptr xs len payload value, .dataElement xs len payload ∈ old ∧ .pointer ptr value ∈ xs →
      ptr < conf.genStart ∨ conf.refsStart ≤ ptr) ∧
    (∀ xs len payload, .dataElement xs len payload ∈ old → conf.isRef payload = false) ∧
    (∀ xs len payload, .dataElement xs len payload ∈ current → conf.isRef payload = false) ∧
    ∀ xs len payload, .dataElement xs len payload ∈ refs → conf.isRef payload = true

/-- Original generation invariant for the partial collector's source heap. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gen_inv_def"]
def genInv {α β : Type} (conf : Config β) (heap : List (HeapElement α β)) : Prop :=
  conf.genStart ≤ conf.refsStart ∧ conf.refsStart ≤ conf.limit ∧
  ∃ old current refs,
    heapSegment (conf.genStart, conf.refsStart) heap = some (old, current, refs) ∧
    List.Forall (fun e => heapElementIsRef conf e = false) old ∧
    List.Forall (fun e => heapElementIsRef conf e = false) current ∧
    List.Forall isDataElement refs ∧
    (∀ n a len, .forwardPointer n a len ∈ heap → conf.genStart ≤ n ∧ n < conf.refsStart) ∧
    List.Forall isDataElement old ∧
    ∀ xs len payload ptr value, .dataElement xs len payload ∈ old ∧ .pointer ptr value ∈ xs →
      ptr < conf.genStart ∨ conf.refsStart ≤ ptr

/-- Protected pointer locations occurring in heap-element children. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "has_old_ptr_def"]
def hasOldPtr {α β γ : Type} (conf : Config α) (heap : List (HeapElement β γ)) (ptr : Nat) : Prop :=
  ∃ xs len payload value, .dataElement xs len payload ∈ heap ∧ .pointer ptr value ∈ xs ∧
    (ptr < conf.genStart ∨ conf.refsStart ≤ ptr)

/-- Protected pointer locations in one address list. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "all_old_ptrs_def"]
def allOldPtrs {α β : Type} (conf : Config α) (xs : List (HeapAddress β)) (ptr : Nat) : Prop :=
  ∃ value, .pointer ptr value ∈ xs ∧ (ptr < conf.genStart ∨ conf.refsStart ≤ ptr)

/-- Invariant used by the source partial-to-major simulation. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "sim_inv_def"]
def simInv {α β : Type} (conf : Config β) (heap0 : List (HeapElement α β)) (state : GcState α β) : Prop :=
  genInv conf state.heap ∧ conf.genStart ≤ state.a ∧ state.a + state.n ≤ conf.refsStart ∧
  conf.genStart + heapLength (state.h1 ++ state.h2) + state.n = conf.refsStart ∧
  (conf.refsStart ≤ conf.genStart → state.h1 = [] ∧ state.h2 = []) ∧
  ∀ ptr, hasOldPtr conf (state.heap ++ state.h1 ++ state.h2 ++ state.r1) ptr → hasOldPtr conf heap0 ptr

/-- Translating heap elements preserves their encoded word length. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "heap_length_to_gen_heap_list"]
theorem heapLength_toGenHeapList {α β γ : Type} (conf : Config γ) (heap : List (HeapElement α β)) :
    heapLength (toGenHeapList conf heap) = heapLength heap := by
  induction heap with
  | nil => rfl
  | cons head tail ih =>
    cases head <;> simp [toGenHeapList, toGenHeapElement, heapLength, elLength] at ih ⊢ <;> omega

/-- The source heap-generation conditions imply the simulation's initial
heap invariant when the heap is well formed. -/
theorem heapGenOk_genInv {α β : Type} (conf : Config β) (heap : List (HeapElement α β))
    (good : heapOk heap conf.limit) (generations : heapGenOk heap conf) : genInv conf heap := by
  obtain ⟨old, current, refs, ordered, within, oldData, refsData, split,
    pointers, oldNotRef, currentNotRef, _⟩ := generations
  refine ⟨ordered, within, old, current, refs, split.symm, ?_, ?_, refsData, ?_, oldData,
    fun xs len payload ptr value => pointers ptr xs len payload value⟩
  · rw [List.forall_iff_forall_mem]
    intro element member
    cases element with
    | unused n => rfl
    | forwardPointer ptr value len => rfl
    | dataElement xs len payload => exact oldNotRef xs len payload member
  · rw [List.forall_iff_forall_mem]
    intro element member
    cases element with
    | unused n => rfl
    | forwardPointer ptr value len => rfl
    | dataElement xs len payload => exact currentNotRef xs len payload member
  · intro n a len member
    have filtered := good.2.1
    have inFilter : .forwardPointer n a len ∈ heap.filter isForwardPointer := by
      simp [member, isForwardPointer]
    rw [filtered] at inFilter
    simp at inFilter

end Flapjack.Compiler.Backend.GenGcPartial
