import Flapjack.Compiler.Backend.GenGcPartial
import Flapjack.Compiler.Backend.GenGc
import Mathlib.Data.List.Basic
import Flapjack.Compiler.Backend.GcShared.Slice
import Flapjack.Compiler.Backend.GenGc.Proofs.HeapLookup
import Flapjack.Compiler.Backend.GenGc.Proofs.Progress
import Flapjack.Compiler.Backend.GenGcPartial.Proofs.Forward
import Flapjack.Compiler.Backend.GenGcPartial.Proofs.Conservation
import Flapjack.Compiler.Backend.GenGcPartial.Proofs.Accumulator
import Flapjack.Compiler.Backend.GcShared.ForwardPtr
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialSplit

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

/-- Translating a heap list commutes with element lookup. This Flapjack
helper is used to compare current-generation moves. -/
theorem heapLookup_toGenHeapList {α β γ : Type} (conf : Config γ)
    (heap : List (HeapElement α β)) (ptr : Nat) :
    heapLookup ptr (toGenHeapList conf heap) = (heapLookup ptr heap).map (toGenHeapElement conf) := by
  induction heap generalizing ptr with
  | nil => simp [toGenHeapList, heapLookup]
  | cons head tail ih =>
    simp only [toGenHeapList] at ih
    cases head <;> simp only [toGenHeapList, List.map_cons, toGenHeapElement, heapLookup, elLength]
    all_goals split_ifs <;> simp_all [toGenHeapElement]
    all_goals
      rename_i h
      have hnot := Nat.not_lt_of_ge h
      simp [hnot]

/-- Within a successfully split current generation, major-heap lookup is the
translated original lookup at the corresponding absolute address. -/
theorem heapLookup_toGenHeap {α β γ : Type} (conf : Config γ)
    (heap old current refs : List (HeapElement α β)) (ptr : Nat)
    (segment : heapSegment (conf.genStart, conf.refsStart) heap = some (old, current, refs))
    (lower : conf.genStart ≤ ptr) (upper : ptr < conf.refsStart) :
    heapLookup (ptr - conf.genStart) (toGenHeap conf heap) =
      (heapLookup ptr heap).map (toGenHeapElement conf) := by
  obtain ⟨whole, oldLen, endLen, _⟩ := heapSegment_imp heap conf.genStart conf.refsStart old current refs segment
  have inside : ptr - conf.genStart < heapLength current := by
    rw [heapLength_append, oldLen] at endLen
    omega
  have lookup : heapLookup ptr heap = heapLookup (ptr - conf.genStart) current := by
    rw [← whole, List.append_assoc, GenGc.heapLookup_append, oldLen,
      if_neg (Nat.not_lt.mpr lower), GenGc.heapLookup_append, if_pos inside]
  simp [toGenHeap, heapRestrict, segment, heapLookup_toGenHeapList, lookup]

/-- Replacing a current-generation data object by a forwarding pointer
commutes with the partial-to-major heap translation and leaves the outer
segments intact. -/
theorem toGenHeap_forward {α β γ : Type} (conf : Config γ)
    (heap old current refs : List (HeapElement α β)) (ptr address : Nat) (value : α)
    (roots : List (HeapAddress α)) (len : Nat) (payload : β) (ok : Bool)
    (segment : heapSegment (conf.genStart, conf.refsStart) heap = some (old, current, refs))
    (lower : conf.genStart ≤ ptr) (upper : ptr < conf.refsStart)
    (found : heapLookup ptr heap = some (.dataElement roots len payload)) :
    ∃ current1,
      gcForwardPtr ptr heap address value ok = (old ++ current1 ++ refs, ok) ∧
      gcForwardPtr (ptr - conf.genStart) (toGenHeap conf heap) (address - conf.genStart) (.real value) ok =
        (toGenHeapList conf current1, ok) ∧
      heapSegment (conf.genStart, conf.refsStart) (old ++ current1 ++ refs) = some (old, current1, refs) := by
  obtain ⟨whole, oldLen, endLen, _⟩ := heapSegment_imp heap conf.genStart conf.refsStart old current refs segment
  have inside : ptr - conf.genStart < heapLength current := by
    rw [heapLength_append, oldLen] at endLen
    omega
  have currentFound : heapLookup (ptr - conf.genStart) current = some (.dataElement roots len payload) := by
    rw [← whole, List.append_assoc, GenGc.heapLookup_append, oldLen,
      if_neg (Nat.not_lt.mpr lower), GenGc.heapLookup_append, if_pos inside] at found
    exact found
  obtain ⟨before, after, currentEq, indexEq⟩ := heapLookup_split current (ptr - conf.genStart) _ currentFound
  have ptrEq : ptr = heapLength (old ++ before) := by
    rw [heapLength_append, oldLen, ← indexEq]
    omega
  let current1 := before ++ .forwardPointer address value len :: after
  have currentLen : heapLength current1 = heapLength current := by
    simp [current1, currentEq, heapLength, List.map_append, List.sum_append, elLength]
  have sourceForward : gcForwardPtr ptr heap address value ok = (old ++ current1 ++ refs, ok) := by
    rw [← whole, currentEq, ptrEq]
    simpa [current1, List.append_assoc] using
      gcForwardPtr_thm (old ++ before) (after ++ refs) roots len payload address value ok
  have genForward : gcForwardPtr (ptr - conf.genStart) (toGenHeap conf heap) (address - conf.genStart) (.real value) ok =
      (toGenHeapList conf current1, ok) := by
    rw [toGenHeap, heapRestrict, segment, currentEq, indexEq, ← heapLength_toGenHeapList conf before]
    simpa [toGenHeapList, toGenHeapElement, current1, List.map_append] using
      gcForwardPtr_thm (toGenHeapList conf before) (toGenHeapList conf after)
        (roots.map (toGenHeapAddress conf)) len payload (address - conf.genStart) (.real value) ok
  have finalSegment : heapSegment (conf.genStart, conf.refsStart) (old ++ current1 ++ refs) = some (old, current1, refs) := by
    have lenEq : heapLength (old ++ current1) = conf.refsStart := by
      rw [heapLength_append, currentLen, ← heapLength_append]
      exact endLen
    simp only [heapSegment, List.append_assoc, ← oldLen,
      DataToWord.Proofs.Gc.heapSplit_append]
    have sub : conf.refsStart - heapLength old = heapLength current1 := by
      rw [← lenEq, heapLength_append]
      omega
    rw [sub, DataToWord.Proofs.Gc.heapSplit_append]
    have ordered : ¬ conf.refsStart < heapLength old := by omega
    simp [ordered]
  exact ⟨current1, sourceForward, genForward, finalSegment⟩

/-- Forwarding a current-generation data object to an address inside that
generation preserves the partial collector's source heap invariant. -/
theorem genInv_forward {α β : Type} (conf : Config β)
    (heap : List (HeapElement α β)) (ptr target : Nat) (value : α)
    (roots : List (HeapAddress α)) (len : Nat) (payload : β)
    (invariant : genInv conf heap) (lower : conf.genStart ≤ ptr) (upper : ptr < conf.refsStart)
    (targetLower : conf.genStart ≤ target) (targetUpper : target < conf.refsStart)
    (found : heapLookup ptr heap = some (.dataElement roots len payload)) :
    genInv conf (gcForwardPtr ptr heap target value true).1 := by
  obtain ⟨ordered, within, old, current, refs, segment, oldNotRef, currentNotRef,
    refsData, forwardBounds, oldData, oldPointers⟩ := invariant
  obtain ⟨whole, oldLen, endLen, _⟩ := heapSegment_imp heap conf.genStart conf.refsStart old current refs segment
  have inside : ptr - conf.genStart < heapLength current := by
    rw [heapLength_append, oldLen] at endLen
    omega
  have currentFound : heapLookup (ptr - conf.genStart) current = some (.dataElement roots len payload) := by
    rw [← whole, List.append_assoc, GenGc.heapLookup_append, oldLen,
      if_neg (Nat.not_lt.mpr lower), GenGc.heapLookup_append, if_pos inside] at found
    exact found
  obtain ⟨before, after, currentEq, indexEq⟩ := heapLookup_split current (ptr - conf.genStart) _ currentFound
  let current1 := before ++ .forwardPointer target value len :: after
  have ptrEq : ptr = heapLength (old ++ before) := by
    rw [heapLength_append, oldLen, ← indexEq]
    omega
  have forwardEq : gcForwardPtr ptr heap target value true = (old ++ current1 ++ refs, true) := by
    rw [← whole, currentEq, ptrEq]
    simpa [current1, List.append_assoc] using gcForwardPtr_thm (old ++ before) (after ++ refs) roots len payload target value true
  obtain ⟨other, sourceForward, _, finalSegment⟩ :=
    toGenHeap_forward conf heap old current refs ptr target value roots len payload true segment lower upper (by
      rw [← whole, List.append_assoc, GenGc.heapLookup_append, oldLen,
        if_neg (Nat.not_lt.mpr lower), GenGc.heapLookup_append, if_pos inside]
      exact currentFound)
  have sameHeap : old ++ current1 ++ refs = old ++ other ++ refs := by
    exact Prod.mk.inj (forwardEq.symm.trans sourceForward) |>.1
  have sameCurrent : current1 = other := by
    exact List.append_cancel_left (List.append_cancel_right sameHeap)
  rw [← sameCurrent] at finalSegment
  have newNotRef : List.Forall (fun e => heapElementIsRef conf e = false) current1 := by
    rw [List.forall_iff_forall_mem] at currentNotRef ⊢
    intro e member
    simp only [current1, List.mem_append, List.mem_cons] at member
    rcases member with beforeMem | rfl | afterMem
    · exact currentNotRef e (by simp [currentEq, beforeMem])
    · rfl
    · exact currentNotRef e (by simp [currentEq, afterMem])
  have newForward : ∀ n a l, .forwardPointer n a l ∈ old ++ current1 ++ refs →
      conf.genStart ≤ n ∧ n < conf.refsStart := by
    intro n a l member
    simp only [current1, List.mem_append, List.mem_cons, or_assoc] at member
    rcases member with oldMem | beforeMem | eq | afterMem | refsMem
    · apply forwardBounds n a l
      rw [← whole, currentEq]
      simp only [List.mem_append, List.mem_cons, or_assoc]
      exact Or.inl oldMem
    · apply forwardBounds n a l
      rw [← whole, currentEq]
      simp only [List.mem_append, List.mem_cons, or_assoc]
      exact Or.inr (Or.inl beforeMem)
    · cases eq
      exact ⟨targetLower, targetUpper⟩
    · apply forwardBounds n a l
      rw [← whole, currentEq]
      simp only [List.mem_append, List.mem_cons, or_assoc]
      exact Or.inr (Or.inr (Or.inr (Or.inl afterMem)))
    · apply forwardBounds n a l
      rw [← whole, currentEq]
      simp only [List.mem_append, List.mem_cons, or_assoc]
      exact Or.inr (Or.inr (Or.inr (Or.inr refsMem)))
  rw [forwardEq]
  exact ⟨ordered, within, old, current1, refs, finalSegment, oldNotRef, newNotRef,
    refsData, newForward, oldData, oldPointers⟩

/-- Moving a data object into the copied queue while installing a forwarding
pointer introduces no new protected child pointers. -/
theorem hasOldPtr_forward_copy {α β γ : Type} (conf : Config γ)
    (before after h1 h2 r1 : List (HeapElement α β)) (target : Nat) (value : α)
    (roots : List (HeapAddress α)) (len : Nat) (payload : β) (ptr : Nat) :
    hasOldPtr conf ((before ++ .forwardPointer target value len :: after) ++ h1 ++
      (h2 ++ [.dataElement roots len payload]) ++ r1) ptr →
    hasOldPtr conf ((before ++ .dataElement roots len payload :: after) ++ h1 ++ h2 ++ r1) ptr := by
  rintro ⟨xs, n, data, u, member, child, outside⟩
  refine ⟨xs, n, data, u, ?_, child, outside⟩
  simp only [List.mem_append, List.mem_cons, or_assoc] at member ⊢
  aesop

/-- A successful fresh data move preserves the full partial-collector
simulation invariant. -/
theorem simInv_fresh_move {α β : Type} (conf : Config β)
    (state state1 : GcState α β) (heap0 : List (HeapElement α β))
    (ptr : Nat) (value : α) (roots : List (HeapAddress α)) (len : Nat) (payload : β)
    (root1 : HeapAddress α) (invariant : simInv conf heap0 state)
    (lower : conf.genStart ≤ ptr) (upper : ptr < conf.refsStart)
    (bounded : ptr < heapLength state.heap)
    (found : heapLookup ptr state.heap = some (.dataElement roots len payload))
    (enough : len + 1 ≤ state.n) (nonref : conf.isRef payload = false)
    (stateOk : state.ok = true) (run : gcMove conf state (.pointer ptr value) = (root1, state1)) :
    simInv conf heap0 state1 := by
  have allocLower := invariant.2.1
  have allocUpper := invariant.2.2.1
  have targetUpper : state.a < conf.refsStart := by omega
  have outside : ¬ (ptr < conf.genStart ∨ conf.refsStart ≤ ptr) := by omega
  obtain ⟨before, after, heapEq, ptrEq⟩ := heapLookup_split state.heap ptr _ found
  have direct : gcForwardPtr ptr state.heap state.a value true =
      (before ++ .forwardPointer state.a value len :: after, true) := by
    rw [heapEq, ptrEq]
    exact gcForwardPtr_thm before after roots len payload state.a value true
  have nextGen := genInv_forward conf state.heap ptr state.a value roots len payload
    invariant.1 lower upper allocLower targetUpper found
  rw [direct] at nextGen
  have step : gcMove conf state (.pointer ptr value) =
      (.pointer state.a value, { state with h2 := state.h2 ++ [.dataElement roots len payload], n := state.n - (len + 1), a := state.a + len + 1, heap := before ++ .forwardPointer state.a value len :: after, ok := true }) := by
    simp [gcMove, outside, found, bounded, enough, nonref, stateOk, direct]
  rw [step] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  obtain ⟨_, start, space, balance, empty, pointers⟩ := invariant
  simp only [simInv]
  refine ⟨nextGen, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · rw [← List.append_assoc, heapLength_append]
    simp only [heapLength, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, elLength]
    simp only [heapLength] at balance
    omega
  · intro reversed
    omega
  · intro p member
    apply pointers p
    have member' := hasOldPtr_forward_copy conf before after state.h1 state.h2 state.r1 state.a value roots len payload p member
    simpa [heapEq] using member'

/-- A successful fresh partial move had a successful input state, enough
space, and a nonreference source object. -/
theorem gcMove_fresh_success_conditions {α β : Type} (conf : Config β)
    (state state1 : GcState α β) (ptr : Nat) (value : α)
    (roots : List (HeapAddress α)) (len : Nat) (payload : β) (root1 : HeapAddress α)
    (lower : conf.genStart ≤ ptr) (upper : ptr < conf.refsStart)
    (found : heapLookup ptr state.heap = some (.dataElement roots len payload))
    (run : gcMove conf state (.pointer ptr value) = (root1, state1))
    (ok : state1.ok = true) :
    state.ok = true ∧ len + 1 ≤ state.n ∧ conf.isRef payload = false := by
  have outside : ¬ (ptr < conf.genStart ∨ conf.refsStart ≤ ptr) := by omega
  obtain ⟨before, after, heapEq, ptrEq⟩ := heapLookup_split state.heap ptr _ found
  let status := ((state.ok && decide (ptr < heapLength state.heap)) && decide (len + 1 ≤ state.n)) && !(conf.isRef payload)
  have direct : gcForwardPtr ptr state.heap state.a value status =
      (before ++ .forwardPointer state.a value len :: after, status) := by
    rw [heapEq, ptrEq]
    exact gcForwardPtr_thm before after roots len payload state.a value status
  simp only [gcMove, outside, ↓reduceIte, found] at run
  change (.pointer state.a value, { state with h2 := state.h2 ++ [.dataElement roots len payload], n := state.n - (len + 1), a := state.a + len + 1, heap := (gcForwardPtr ptr state.heap state.a value status).1, ok := (gcForwardPtr ptr state.heap state.a value status).2 }) = (root1, state1) at run
  rw [direct] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  simp [status] at ok
  exact ⟨ok.1.1.1, ok.1.2, ok.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- In the fresh-object case, a successful major move determines a matching
partial move and translated state. Preservation of `simInv` is a separate
obligation. -/
theorem gcMove_fresh_translation {α β : Type} (conf : Config β)
    (state : GcState α β) (heap0 : List (HeapElement α β))
    (ptr : Nat) (value : α) (roots : List (HeapAddress α)) (len : Nat) (payload : β)
    (lower : conf.genStart ≤ ptr) (upper : ptr < conf.refsStart)
    (bounded : ptr < heapLength state.heap)
    (found : heapLookup ptr state.heap = some (.dataElement roots len payload))
    (invariant : simInv conf heap0 state)
    (majorOk : (GenGc.gcMove (toGenConf conf) (toGenState conf state)
      (toGenHeapAddress conf (.pointer ptr value))).2.ok = true) :
    ∃ root1 state1,
      gcMove conf state (.pointer ptr value) = (root1, state1) ∧
      GenGc.gcMove (toGenConf conf) (toGenState conf state) (toGenHeapAddress conf (.pointer ptr value)) =
        (toGenHeapAddress conf root1, toGenState conf state1) ∧ state1.ok = true := by
  obtain ⟨gen, allocLower, allocUpper, _, _, _⟩ := invariant
  obtain ⟨_, _, old, current, refs, segment, _, currentNotRef, _, _, _, _⟩ := gen
  have inside : ¬ (ptr < conf.genStart ∨ conf.refsStart ≤ ptr) := by omega
  have translatedLookup := heapLookup_toGenHeap conf state.heap old current refs ptr segment lower upper
  rw [found] at translatedLookup
  have majorFound : heapLookup (ptr - conf.genStart) (toGenState conf state).heap =
      some (.dataElement (roots.map (toGenHeapAddress conf)) len payload) := by
    simpa [toGenState, toGenHeapElement] using translatedLookup
  have currentFound : heapLookup (ptr - conf.genStart) current = some (.dataElement roots len payload) := by
    obtain ⟨whole, oldLen, endLen, _⟩ := heapSegment_imp state.heap conf.genStart conf.refsStart old current refs segment
    have bound : ptr - conf.genStart < heapLength current := by
      rw [heapLength_append, oldLen] at endLen
      omega
    rw [← whole, List.append_assoc, GenGc.heapLookup_append, oldLen,
      if_neg (Nat.not_lt.mpr lower), GenGc.heapLookup_append, if_pos bound] at found
    exact found
  have nonref : conf.isRef payload = false := by
    have member := heapLookup_mem current (ptr - conf.genStart) _ currentFound
    exact List.forall_iff_forall_mem.mp currentNotRef _ member
  let status := state.ok && decide (len + 1 ≤ state.n)
  obtain ⟨current1, sourceForward, majorForward, finalSegment⟩ :=
    toGenHeap_forward conf state.heap old current refs ptr state.a value roots len payload status segment lower upper found
  have inputEq : toGenHeapAddress conf (.pointer ptr value) = .pointer (ptr - conf.genStart) (.real value) := by
    simp [toGenHeapAddress, Nat.not_lt.mpr lower, Nat.not_le.mpr upper]
  have majorExec : GenGc.gcMove (toGenConf conf) (toGenState conf state) (toGenHeapAddress conf (.pointer ptr value)) =
      (.pointer (state.a - conf.genStart) (.real value),
        { toGenState conf state with h2 := (toGenState conf state).h2 ++ [.dataElement (roots.map (toGenHeapAddress conf)) len payload], n := state.n - (len + 1), a := (state.a - conf.genStart) + len + 1, heap := toGenHeapList conf current1, ok := status }) := by
    rw [inputEq]
    simp only [GenGc.gcMove, majorFound]
    dsimp only [toGenState, toGenConf]
    simp only [nonref, Bool.false_eq_true, ↓reduceIte]
    have forwardEq : gcForwardPtr (ptr - conf.genStart) (toGenHeap conf state.heap) (state.a - conf.genStart) (.real value)
        (state.ok && decide (len + 1 ≤ state.n)) = (toGenHeapList conf current1, state.ok && decide (len + 1 ≤ state.n)) := by
      simpa [status] using majorForward
    simp only [status]
    rw [forwardEq]
  rw [majorExec] at majorOk
  change status = true at majorOk
  have enough : len + 1 ≤ state.n := by
    have parts : state.ok = true ∧ decide (len + 1 ≤ state.n) = true := by
      simpa [status] using majorOk
    exact of_decide_eq_true parts.2
  have allocInside : state.a < conf.refsStart := by omega
  have outputEq : toGenHeapAddress conf (.pointer state.a value) = .pointer (state.a - conf.genStart) (.real value) := by
    simp [toGenHeapAddress, Nat.not_lt.mpr allocLower, Nat.not_le.mpr allocInside]
  let result : GcState α β := { state with h2 := state.h2 ++ [.dataElement roots len payload], n := state.n - (len + 1), a := state.a + len + 1, heap := old ++ current1 ++ refs, ok := status }
  have partialExec : gcMove conf state (.pointer ptr value) = (.pointer state.a value, result) := by
    simp only [gcMove, inside, ↓reduceIte, found, bounded, decide_true, Bool.and_true, nonref, Bool.not_false, Bool.and_true]
    have forwardEq : gcForwardPtr ptr state.heap state.a value (state.ok && decide (len + 1 ≤ state.n)) =
        (old ++ current1 ++ refs, state.ok && decide (len + 1 ≤ state.n)) := by
      simpa [status] using sourceForward
    simp [result, status, forwardEq]
  have translatedState : toGenState conf result =
      { toGenState conf state with h2 := (toGenState conf state).h2 ++ [.dataElement (roots.map (toGenHeapAddress conf)) len payload], n := state.n - (len + 1), a := (state.a - conf.genStart) + len + 1, heap := toGenHeapList conf current1, ok := status } := by
    have addressEq : state.a + len + 1 - conf.genStart = (state.a - conf.genStart) + len + 1 := by omega
    simp only [List.append_assoc] at finalSegment
    simp [toGenState, result, toGenHeap, heapRestrict, finalSegment, toGenHeapList, toGenHeapElement, addressEq]
  exact ⟨.pointer state.a value, result, partialExec, by simpa [outputEq, translatedState] using majorExec, majorOk⟩

/-- Immediate values take the data case of the partial-to-major move
simulation. This is one constructor case of the source theorem. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_simulation"]
theorem gcMove_simulation_data {α β : Type} (conf : Config β)
    (state state1 : GcState α β) (heap0 : List (HeapElement α β))
    (d : α) (root1 : HeapAddress α) (majorRoot : HeapAddress (DataSort (HeapAddress α) α))
    (majorState : GcState (DataSort (HeapAddress α) α) β)
    (partialRun : gcMove conf state (.data d) = (root1, state1))
    (_bounded : ∀ ptr u, HeapAddress.data d = .pointer ptr u → ptr < heapLength state.heap)
    (_heapLengthEq : heapLength state.heap = conf.limit)
    (invariant : simInv conf heap0 state)
    (majorRun : GenGc.gcMove (toGenConf conf) (toGenState conf state) (toGenHeapAddress conf (.data d)) =
      (majorRoot, majorState)) (majorOk : majorState.ok = true) :
    simInv conf heap0 state1 ∧
    (majorRoot, majorState) = (toGenHeapAddress conf root1, toGenState conf state1) ∧
    ∀ ptr, allOldPtrs conf [root1] ptr → allOldPtrs conf [.data d] ptr := by
  simp only [gcMove, Prod.mk.injEq] at partialRun
  obtain ⟨rfl, rfl⟩ := partialRun
  simp only [toGenHeapAddress, GenGc.gcMove, Prod.mk.injEq] at majorRun
  obtain ⟨rfl, rfl⟩ := majorRun
  exact ⟨invariant, rfl, fun _ h => h⟩

/-- Protected pointers take the unchanged-root case of the partial-to-major
move simulation. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_simulation"]
theorem gcMove_simulation_protected {α β : Type} (conf : Config β)
    (state state1 : GcState α β) (heap0 : List (HeapElement α β))
    (ptr : Nat) (value : α) (root1 : HeapAddress α)
    (majorRoot : HeapAddress (DataSort (HeapAddress α) α))
    (majorState : GcState (DataSort (HeapAddress α) α) β)
    (outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr)
    (partialRun : gcMove conf state (.pointer ptr value) = (root1, state1))
    (bounded : ∀ p u, HeapAddress.pointer ptr value = .pointer p u → p < heapLength state.heap)
    (_heapLengthEq : heapLength state.heap = conf.limit)
    (invariant : simInv conf heap0 state)
    (majorRun : GenGc.gcMove (toGenConf conf) (toGenState conf state) (toGenHeapAddress conf (.pointer ptr value)) =
      (majorRoot, majorState)) (majorOk : majorState.ok = true) :
    simInv conf heap0 state1 ∧
    (majorRoot, majorState) = (toGenHeapAddress conf root1, toGenState conf state1) ∧
    ∀ p, allOldPtrs conf [root1] p → allOldPtrs conf [.pointer ptr value] p := by
  have bound := bounded ptr value rfl
  have unchanged : gcMove conf state (.pointer ptr value) = (.pointer ptr value, state) := by
    simp [gcMove, outside, bound]
  rw [unchanged] at partialRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj partialRun
  have translated : toGenHeapAddress conf (.pointer ptr value) = .data (.protectedValue (.pointer ptr value)) := by
    rcases outside with below | above
    · simp [toGenHeapAddress, below]
    · by_cases below : ptr < conf.genStart
      · simp [toGenHeapAddress, below]
      · simp [toGenHeapAddress, below, above]
  rw [translated] at majorRun
  simp only [GenGc.gcMove, Prod.mk.injEq] at majorRun
  obtain ⟨rfl, rfl⟩ := majorRun
  refine ⟨invariant, ?_, fun _ h => h⟩
  simp [translated]

/-- The forwarding-pointer case of the partial-to-major root-move
simulation preserves the state and translates the forwarded address. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_simulation"]
theorem gcMove_simulation_forward {α β : Type} (conf : Config β)
    (state state1 : GcState α β) (heap0 : List (HeapElement α β))
    (ptr target len : Nat) (value oldValue : α) (root1 : HeapAddress α)
    (majorRoot : HeapAddress (DataSort (HeapAddress α) α))
    (majorState : GcState (DataSort (HeapAddress α) α) β)
    (lower : conf.genStart ≤ ptr) (upper : ptr < conf.refsStart)
    (found : heapLookup ptr state.heap = some (.forwardPointer target oldValue len))
    (partialRun : gcMove conf state (.pointer ptr value) = (root1, state1))
    (_bounded : ∀ p u, HeapAddress.pointer ptr value = .pointer p u → p < heapLength state.heap)
    (_heapLengthEq : heapLength state.heap = conf.limit)
    (invariant : simInv conf heap0 state)
    (majorRun : GenGc.gcMove (toGenConf conf) (toGenState conf state) (toGenHeapAddress conf (.pointer ptr value)) =
      (majorRoot, majorState)) (majorOk : majorState.ok = true) :
    simInv conf heap0 state1 ∧
    (majorRoot, majorState) = (toGenHeapAddress conf root1, toGenState conf state1) ∧
    ∀ p, allOldPtrs conf [root1] p → allOldPtrs conf [.pointer ptr value] p := by
  have gen := invariant.1
  obtain ⟨_, _, old, current, refs, segment, _, _, _, forwardBounds, _, _⟩ := gen
  have targetBounds := forwardBounds target oldValue len (heapLookup_mem state.heap ptr _ found)
  have inside : ¬ (ptr < conf.genStart ∨ conf.refsStart ≤ ptr) := by omega
  have partialEq : gcMove conf state (.pointer ptr value) = (.pointer target value, state) := by
    simp [gcMove, inside, found]
  rw [partialEq] at partialRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj partialRun
  have translatedLookup := heapLookup_toGenHeap conf state.heap old current refs ptr segment lower upper
  rw [found] at translatedLookup
  have majorFound : heapLookup (ptr - conf.genStart) (toGenState conf state).heap =
      some (.forwardPointer (target - conf.genStart) (.real oldValue) len) := by
    simpa [toGenState, toGenHeapElement] using translatedLookup
  have inputEq : toGenHeapAddress conf (.pointer ptr value) = .pointer (ptr - conf.genStart) (.real value) := by
    simp [toGenHeapAddress, Nat.not_lt.mpr lower, Nat.not_le.mpr upper]
  have outputEq : toGenHeapAddress conf (.pointer target value) = .pointer (target - conf.genStart) (.real value) := by
    simp [toGenHeapAddress, Nat.not_lt.mpr targetBounds.1, Nat.not_le.mpr targetBounds.2]
  rw [inputEq] at majorRun
  simp only [GenGc.gcMove, majorFound, Prod.mk.injEq] at majorRun
  obtain ⟨rfl, rfl⟩ := majorRun
  refine ⟨invariant, ?_, ?_⟩
  · simp [outputEq]
  · intro p member
    simp only [allOldPtrs, List.mem_singleton, HeapAddress.pointer.injEq] at member
    obtain ⟨_, ⟨rfl, _⟩, outside⟩ := member
    omega

/-- The fresh current-generation data-object case of the partial-to-major
root-move simulation. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_simulation"]
theorem gcMove_simulation_fresh {α β : Type} (conf : Config β)
    (state state1 : GcState α β) (heap0 : List (HeapElement α β))
    (ptr len : Nat) (value : α) (roots : List (HeapAddress α)) (payload : β) (root1 : HeapAddress α)
    (majorRoot : HeapAddress (DataSort (HeapAddress α) α))
    (majorState : GcState (DataSort (HeapAddress α) α) β)
    (lower : conf.genStart ≤ ptr) (upper : ptr < conf.refsStart)
    (found : heapLookup ptr state.heap = some (.dataElement roots len payload))
    (partialRun : gcMove conf state (.pointer ptr value) = (root1, state1))
    (bounded : ∀ p u, HeapAddress.pointer ptr value = .pointer p u → p < heapLength state.heap)
    (_heapLengthEq : heapLength state.heap = conf.limit)
    (invariant : simInv conf heap0 state)
    (majorRun : GenGc.gcMove (toGenConf conf) (toGenState conf state) (toGenHeapAddress conf (.pointer ptr value)) =
      (majorRoot, majorState)) (majorOk : majorState.ok = true) :
    simInv conf heap0 state1 ∧
    (majorRoot, majorState) = (toGenHeapAddress conf root1, toGenState conf state1) ∧
    ∀ p, allOldPtrs conf [root1] p → allOldPtrs conf [.pointer ptr value] p := by
  have bound := bounded ptr value rfl
  have majorSuccess : (GenGc.gcMove (toGenConf conf) (toGenState conf state)
      (toGenHeapAddress conf (.pointer ptr value))).2.ok = true := by
    rw [majorRun]
    exact majorOk
  obtain ⟨moved, next, partialEq, translated, nextOk⟩ :=
    gcMove_fresh_translation conf state heap0 ptr value roots len payload lower upper bound found invariant majorSuccess
  rw [partialRun] at partialEq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj partialEq
  obtain ⟨stateOk, enough, nonref⟩ :=
    gcMove_fresh_success_conditions conf state state1 ptr value roots len payload root1 lower upper found partialRun nextOk
  have post := simInv_fresh_move conf state state1 heap0 ptr value roots len payload root1 invariant lower upper bound found enough nonref stateOk partialRun
  have equal : (majorRoot, majorState) = (toGenHeapAddress conf root1, toGenState conf state1) :=
    majorRun.symm.trans translated
  have outside : ¬ (ptr < conf.genStart ∨ conf.refsStart ≤ ptr) := by omega
  have rootEq : root1 = .pointer state.a value := by
    simp only [gcMove, outside, ↓reduceIte, found, Prod.mk.injEq] at partialRun
    exact partialRun.1.symm
  refine ⟨post, equal, ?_⟩
  intro p member
  rw [rootEq] at member
  simp only [allOldPtrs, List.mem_singleton, HeapAddress.pointer.injEq] at member
  obtain ⟨_, ⟨rfl, _⟩, disjoint⟩ := member
  have start := invariant.2.1
  have limit := invariant.2.2.1
  omega

/-- Partial root movement simulates the corresponding major root movement,
preserves the simulation invariant, and does not introduce protected roots. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_simulation"]
theorem gcMove_simulation {α β : Type} (conf : Config β)
    (state state1 : GcState α β) (heap0 : List (HeapElement α β))
    (root root1 : HeapAddress α) (majorRoot : HeapAddress (DataSort (HeapAddress α) α))
    (majorState : GcState (DataSort (HeapAddress α) α) β)
    (partialRun : gcMove conf state root = (root1, state1))
    (bounded : ∀ p u, root = .pointer p u → p < heapLength state.heap)
    (heapLengthEq : heapLength state.heap = conf.limit)
    (invariant : simInv conf heap0 state)
    (majorRun : GenGc.gcMove (toGenConf conf) (toGenState conf state) (toGenHeapAddress conf root) =
      (majorRoot, majorState)) (majorOk : majorState.ok = true) :
    simInv conf heap0 state1 ∧
    (majorRoot, majorState) = (toGenHeapAddress conf root1, toGenState conf state1) ∧
    ∀ p, allOldPtrs conf [root1] p → allOldPtrs conf [root] p := by
  cases root with
  | data d =>
    exact gcMove_simulation_data conf state state1 heap0 d root1 majorRoot majorState
      partialRun bounded heapLengthEq invariant majorRun majorOk
  | pointer ptr value =>
    by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
    · exact gcMove_simulation_protected conf state state1 heap0 ptr value root1 majorRoot majorState
        outside partialRun bounded heapLengthEq invariant majorRun majorOk
    · have lower : conf.genStart ≤ ptr := by omega
      have upper : ptr < conf.refsStart := by omega
      obtain ⟨_, _, old, current, refs, segment, _, _, _, _, _, _⟩ := invariant.1
      have lookup := heapLookup_toGenHeap conf state.heap old current refs ptr segment lower upper
      have inputEq : toGenHeapAddress conf (.pointer ptr value) = .pointer (ptr - conf.genStart) (.real value) := by
        simp [toGenHeapAddress, Nat.not_lt.mpr lower, Nat.not_le.mpr upper]
      cases found : heapLookup ptr state.heap with
      | none =>
        have missing : heapLookup (ptr - conf.genStart) (toGenState conf state).heap = none := by
          simpa [toGenState, found] using lookup
        rw [inputEq] at majorRun
        simp only [GenGc.gcMove, missing, Prod.mk.injEq] at majorRun
        obtain ⟨_, rfl⟩ := majorRun
        simp at majorOk
      | some element =>
        cases element with
        | unused len =>
          have unused : heapLookup (ptr - conf.genStart) (toGenState conf state).heap = some (.unused len) := by
            simpa [toGenState, found, toGenHeapElement] using lookup
          rw [inputEq] at majorRun
          simp only [GenGc.gcMove, unused, Prod.mk.injEq] at majorRun
          obtain ⟨_, rfl⟩ := majorRun
          simp at majorOk
        | forwardPointer target oldValue len =>
          exact gcMove_simulation_forward conf state state1 heap0 ptr target len value oldValue root1 majorRoot majorState
            lower upper found partialRun bounded heapLengthEq invariant majorRun majorOk
        | dataElement roots len payload =>
          exact gcMove_simulation_fresh conf state state1 heap0 ptr len value roots payload root1 majorRoot majorState
            lower upper found partialRun bounded heapLengthEq invariant majorRun majorOk

/-- Partial root-list movement simulates major root-list movement and does
not introduce protected roots. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_list_simulation"]
theorem gcMoveList_simulation {α β : Type} (conf : Config β)
    (heap0 : List (HeapElement α β)) (roots : List (HeapAddress α))
    (state state1 : GcState α β) (roots1 : List (HeapAddress α))
    (majorRoots : List (HeapAddress (DataSort (HeapAddress α) α)))
    (majorState : GcState (DataSort (HeapAddress α) α) β)
    (partialRun : gcMoveList conf state roots = (roots1, state1))
    (invariant : simInv conf heap0 state)
    (bounded : ∀ ptr u, .pointer ptr u ∈ roots → ptr < heapLength state.heap)
    (heapLengthEq : heapLength state.heap = conf.limit)
    (majorRun : GenGc.gcMoveList (toGenConf conf) (toGenState conf state)
      (roots.map (toGenHeapAddress conf)) = (majorRoots, majorState))
    (majorOk : majorState.ok = true) :
    simInv conf heap0 state1 ∧
    (majorRoots, majorState) = (roots1.map (toGenHeapAddress conf), toGenState conf state1) ∧
    ∀ p, allOldPtrs conf roots1 p → allOldPtrs conf roots p := by
  induction roots generalizing state state1 roots1 majorRoots majorState with
  | nil =>
    simp only [gcMoveList, Prod.mk.injEq] at partialRun
    obtain ⟨rfl, rfl⟩ := partialRun
    simp only [List.map_nil, GenGc.gcMoveList, Prod.mk.injEq] at majorRun
    obtain ⟨rfl, rfl⟩ := majorRun
    exact ⟨invariant, rfl, fun _ h => h⟩
  | cons head tail ih =>
    simp only [gcMoveList] at partialRun
    generalize headRun : gcMove conf state head = partialHead at partialRun
    obtain ⟨head1, middle⟩ := partialHead
    generalize tailRun : gcMoveList conf middle tail = partialTail at partialRun
    obtain ⟨tail1, final⟩ := partialTail
    simp only [Prod.mk.injEq] at partialRun
    obtain ⟨rfl, rfl⟩ := partialRun
    simp only [List.map_cons, GenGc.gcMoveList] at majorRun
    generalize majorHeadRun : GenGc.gcMove (toGenConf conf) (toGenState conf state)
      (toGenHeapAddress conf head) = majorHead at majorRun
    obtain ⟨head2, middle2⟩ := majorHead
    generalize majorTailRun : GenGc.gcMoveList (toGenConf conf) middle2
      (tail.map (toGenHeapAddress conf)) = majorTail at majorRun
    obtain ⟨tail2, final2⟩ := majorTail
    simp only [Prod.mk.injEq] at majorRun
    obtain ⟨rfl, rfl⟩ := majorRun
    have middleOk := GenGc.gcMoveList_ok (toGenConf conf) (tail.map (toGenHeapAddress conf)) tail2 middle2 final2 majorTailRun majorOk
    have headBound : ∀ ptr u, head = .pointer ptr u → ptr < heapLength state.heap := by
      intro ptr u eq
      exact bounded ptr u (by simp [← eq])
    obtain ⟨middleInv, equal, headOld⟩ :=
      gcMove_simulation conf state middle heap0 head head1 head2 middle2 headRun headBound heapLengthEq invariant majorHeadRun middleOk
    obtain ⟨headEq, middleEq⟩ := Prod.mk.inj equal
    subst head2
    subst middle2
    have sizeEq := gcMove_heapLength conf state middle head head1 headRun
    have tailBound : ∀ ptr u, .pointer ptr u ∈ tail → ptr < heapLength middle.heap := by
      intro ptr u member
      rw [← sizeEq]
      exact bounded ptr u (by simp [member])
    obtain ⟨finalInv, tailEq, tailOld⟩ :=
      ih middle final tail1 tail2 final2 tailRun middleInv tailBound (sizeEq.symm.trans heapLengthEq) majorTailRun majorOk
    obtain ⟨rootsEq, stateEq⟩ := Prod.mk.inj tailEq
    refine ⟨finalInv, ?_, ?_⟩
    · simp [rootsEq, stateEq]
    · intro p member
      obtain ⟨u, membership, outside⟩ := member
      simp only [List.mem_cons] at membership
      rcases membership with eq | member
      · have old : allOldPtrs conf [head1] p := ⟨u, by simp [eq], outside⟩
        obtain ⟨v, member, outside⟩ := headOld p old
        simp only [List.mem_singleton] at member
        exact ⟨v, List.mem_cons.mpr (Or.inl member), outside⟩
      · have old : allOldPtrs conf tail1 p := ⟨u, member, outside⟩
        obtain ⟨v, member, outside⟩ := tailOld p old
        exact ⟨v, by simp [member], outside⟩

/-- Flapjack proof infrastructure: the pointer bound needed by the copied-data
scan survives traversal of a list of roots. -/
theorem gcMoveList_dataPointersBound {α β : Type} (conf : Config β)
    (state state1 : GcState α β) (roots roots1 : List (HeapAddress α))
    (run : gcMoveList conf state roots = (roots1, state1))
    (bounded : ∀ children len data ptr value,
      .pointer ptr value ∈ children → .dataElement children len data ∈ state.heap ++ state.h2 →
        ptr < heapLength state.heap) :
    ∀ children len data ptr value,
      .pointer ptr value ∈ children → .dataElement children len data ∈ state1.heap ++ state1.h2 →
        ptr < heapLength state1.heap := by
  intro children len data ptr value member object
  have original := (gcMoveList_dataMem conf roots roots1 state state1 children len data run).mp object
  have size := gcMoveList_heapLength roots roots1 conf state state1 run
  rw [← size]
  exact bounded children len data ptr value member original

/-- Flapjack proof infrastructure: after the scan removes its current pending
object, every remaining object's pointers still satisfy the recursive bound. -/
theorem gcMoveList_dataScanNextBound {α β : Type} (conf : Config β)
    (state state1 : GcState α β) (roots roots1 : List (HeapAddress α))
    (run : gcMoveList conf state roots = (roots1, state1))
    (bounded : ∀ children len data ptr value,
      .pointer ptr value ∈ children → .dataElement children len data ∈ state.heap ++ state.h2 →
        ptr < heapLength state.heap) :
    ∀ children len data ptr value,
      .pointer ptr value ∈ children → .dataElement children len data ∈ state1.heap ++ state1.h2.drop 1 →
        ptr < heapLength state1.heap := by
  intro children len data ptr value member object
  apply gcMoveList_dataPointersBound conf state state1 roots roots1 run bounded children len data ptr value member
  apply List.mem_append.mpr
  rcases List.mem_append.mp object with inHeap | inTail
  · exact Or.inl inHeap
  · right
    cases h : state1.h2 with
    | nil => simp [h] at inTail
    | cons head tail => simp only [h, List.drop_succ_cons, List.drop_zero] at inTail; simp [inTail]

/-- Flapjack proof infrastructure: the simulation invariant keeps the pending
data within both collectors' limits. -/
theorem simInv_dataScanLimits {α β : Type} (conf : Config β)
    (heap0 : List (HeapElement α β)) (state : GcState α β)
    (invariant : simInv conf heap0 state) :
    heapLength (state.h1 ++ state.h2) ≤ conf.limit ∧
      heapLength (state.h1 ++ state.h2) ≤ (toGenConf conf).limit := by
  have lower := invariant.1.1
  have upper := invariant.1.2.1
  have size := invariant.2.2.2.1
  simp only [toGenConf]
  omega

/-- Flapjack proof infrastructure: traversing an object's children keeps that
object at the front of the pending data queue. -/
theorem gcMoveList_preservesPendingHead {α β : Type} (conf : Config β)
    (state state1 : GcState α β) (roots roots1 : List (HeapAddress α))
    (head : HeapElement α β) (tail : List (HeapElement α β))
    (pending : state.h2 = head :: tail)
    (run : gcMoveList conf state roots = (roots1, state1)) :
    ∃ tail1, state1.h2 = head :: tail1 := by
  have fact := gcMoveList_accumulate conf { state with h2 := tail } roots [head] []
  have initial : { state with h2 := [head] ++ tail, r4 := state.r4 ++ [] } = state := by
    simp [← pending]
  simp only [initial] at fact
  rw [run] at fact
  cases clearRun : gcMoveList conf { state with h2 := tail } roots with
  | mk out final =>
    simp only [clearRun, Prod.mk.injEq] at fact
    obtain ⟨_, eq⟩ := fact
    exact ⟨final.h2, by rw [eq]; rfl⟩

/-- Major root traversal factors over concatenated input lists. -/
theorem majorMoveList_append {α β : Type} (conf : GenGc.Config β) (state : GcState α β)
    (xs ys : List (HeapAddress α)) :
    GenGc.gcMoveList conf state (xs ++ ys) =
      let (xs1, middle) := GenGc.gcMoveList conf state xs
      let (ys1, final) := GenGc.gcMoveList conf middle ys
      (xs1 ++ ys1, final) := by
  induction xs generalizing state with
  | nil => simp [GenGc.gcMoveList]
  | cons head tail ih =>
    simp only [List.cons_append, GenGc.gcMoveList]
    generalize move : GenGc.gcMove conf state head = result
    obtain ⟨head1, middle⟩ := result
    simp only
    rw [ih middle]

/-- Reference-object traversal simulates a major root-list traversal over the
flattened translated children and preserves the protected-pointer subset. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_ref_list_simulation"]
theorem gcMoveRefList_simulation {α β γ : Type} (conf : Config β)
    (state state1 : GcState α β) (refs0 refs1 : List (HeapElement α γ))
    (heap0 : List (HeapElement α β))
    (majorRoots : List (HeapAddress (DataSort (HeapAddress α) α)))
    (majorState : GcState (DataSort (HeapAddress α) α) β)
    (partialRun : gcMoveRefList conf state refs0 = (refs1, state1))
    (majorRun : GenGc.gcMoveList (toGenConf conf) (toGenState conf state) (refsToRoots conf refs0) =
      (majorRoots, majorState)) (majorOk : majorState.ok = true)
    (invariant : simInv conf heap0 state)
    (bounded : ∀ ptrs len data ptr u, .pointer ptr u ∈ ptrs ∧ .dataElement ptrs len data ∈ refs0 →
      ptr < heapLength state.heap)
    (heapLengthEq : heapLength state.heap = conf.limit) (allData : List.Forall isDataElement refs0) :
    simInv conf heap0 state1 ∧ majorRoots = refsToRoots conf refs1 ∧ majorState = toGenState conf state1 ∧
    ∀ p, hasOldPtr conf refs1 p → hasOldPtr conf refs0 p := by
  induction refs0 generalizing state state1 refs1 majorRoots majorState with
  | nil =>
    simp only [gcMoveRefList, Prod.mk.injEq] at partialRun
    obtain ⟨rfl, rfl⟩ := partialRun
    simp only [refsToRoots, GenGc.gcMoveList, Prod.mk.injEq] at majorRun
    obtain ⟨rfl, rfl⟩ := majorRun
    exact ⟨invariant, rfl, rfl, fun _ h => h⟩
  | cons head tail ih =>
    have headData : isDataElement head := List.forall_iff_forall_mem.mp allData head (by simp)
    have tailData : List.Forall isDataElement tail := by
      apply List.forall_iff_forall_mem.mpr
      intro e member
      exact List.forall_iff_forall_mem.mp allData e (by simp [member])
    obtain ⟨roots, len, data, rfl⟩ := headData
    simp only [gcMoveRefList] at partialRun
    generalize headRun : gcMoveList conf state roots = partialHead at partialRun
    obtain ⟨roots1, middle⟩ := partialHead
    generalize tailRun : gcMoveRefList conf middle tail = partialTail at partialRun
    obtain ⟨tail1, final⟩ := partialTail
    simp only [Prod.mk.injEq] at partialRun
    obtain ⟨rfl, rfl⟩ := partialRun
    simp only [refsToRoots, majorMoveList_append] at majorRun
    generalize majorHeadRun : GenGc.gcMoveList (toGenConf conf) (toGenState conf state)
      (roots.map (toGenHeapAddress conf)) = majorHead at majorRun
    obtain ⟨headRoots, middle2⟩ := majorHead
    generalize majorTailRun : GenGc.gcMoveList (toGenConf conf) middle2 (refsToRoots conf tail) = majorTail at majorRun
    obtain ⟨tailRoots, final2⟩ := majorTail
    simp only [Prod.mk.injEq] at majorRun
    obtain ⟨rfl, rfl⟩ := majorRun
    have middleOk := GenGc.gcMoveList_ok (toGenConf conf) (refsToRoots conf tail) tailRoots middle2 final2 majorTailRun majorOk
    have headBound : ∀ ptr u, .pointer ptr u ∈ roots → ptr < heapLength state.heap := by
      intro ptr u member
      exact bounded roots len data ptr u ⟨member, by simp⟩
    obtain ⟨middleInv, equal, headOld⟩ :=
      gcMoveList_simulation conf heap0 roots state middle roots1 headRoots middle2 headRun invariant headBound heapLengthEq majorHeadRun middleOk
    obtain ⟨headEq, middleEq⟩ := Prod.mk.inj equal
    subst headRoots
    subst middle2
    have sizeEq := gcMoveList_heapLength roots roots1 conf state middle headRun
    have tailBound : ∀ ptrs len data ptr u, .pointer ptr u ∈ ptrs ∧ .dataElement ptrs len data ∈ tail →
        ptr < heapLength middle.heap := by
      intro ptrs len data ptr u pair
      rw [← sizeEq]
      exact bounded ptrs len data ptr u ⟨pair.1, by simp [pair.2]⟩
    obtain ⟨finalInv, tailEq, stateEq, tailOld⟩ :=
      ih middle final tail1 tailRoots final2 tailRun majorTailRun majorOk middleInv tailBound (sizeEq.symm.trans heapLengthEq) tailData
    refine ⟨finalInv, ?_, stateEq, ?_⟩
    · simp [refsToRoots, tailEq]
    · intro p member
      obtain ⟨xs, size, payload, u, membership, child, outside⟩ := member
      simp only [List.mem_cons] at membership
      rcases membership with eq | member
      · cases eq
        have headMember : allOldPtrs conf roots1 p := ⟨u, child, outside⟩
        obtain ⟨v, oldChild, outside⟩ := headOld p headMember
        exact ⟨roots, len, data, v, by simp, oldChild, outside⟩
      · obtain ⟨xs, size, payload, v, oldMember, oldChild, outside⟩ :=
          tailOld p ⟨xs, size, payload, u, member, child, outside⟩
        exact ⟨xs, size, payload, v, by simp [oldMember], oldChild, outside⟩

end Flapjack.Compiler.Backend.GenGcPartial
