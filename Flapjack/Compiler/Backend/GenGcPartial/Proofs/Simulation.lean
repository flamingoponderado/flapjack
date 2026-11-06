import Flapjack.Compiler.Backend.GenGcPartial
import Flapjack.Compiler.Backend.GenGc
import Mathlib.Data.List.Basic
import Flapjack.Compiler.Backend.GcShared.Slice
import Flapjack.Compiler.Backend.GenGc.Proofs.HeapLookup
import Flapjack.Compiler.Backend.GenGc.Proofs.Progress
import Flapjack.Compiler.Backend.GenGc.Proofs.Invariant
import Flapjack.Compiler.Backend.GenGc.Proofs.Correct
import Flapjack.Compiler.Backend.GenGcPartial.Proofs.Forward
import Flapjack.Compiler.Backend.GenGcPartial.Proofs.Conservation
import Flapjack.Compiler.Backend.GenGcPartial.Proofs.Accumulator
import Flapjack.Compiler.Backend.GcShared.ForwardPtr
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialSplit
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialFull

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

/-- Flapjack proof infrastructure: reference traversal preserves the data
pointer bound needed by the subsequent copied-data scan. -/
theorem gcMoveRefList_dataPointersBound {α β γ : Type} (conf : Config γ)
    (state state1 : GcState α γ) (refs refs1 : List (HeapElement α β))
    (run : gcMoveRefList conf state refs = (refs1, state1))
    (bounded : ∀ children len data ptr value,
      .pointer ptr value ∈ children → .dataElement children len data ∈ state.heap ++ state.h2 →
        ptr < heapLength state.heap) :
    ∀ children len data ptr value,
      .pointer ptr value ∈ children → .dataElement children len data ∈ state1.heap ++ state1.h2 →
        ptr < heapLength state1.heap := by
  intro children len data ptr value member object
  have original := (gcMoveRefList_dataMem conf refs refs1 state state1 children len data run).mp object
  have size := gcMoveRefList_heapLength conf refs refs1 state state1 run
  rw [← size]
  exact bounded children len data ptr value member original

/-- Flapjack proof infrastructure: pointers in valid heap objects lie within
the heap's encoded extent. -/
theorem heapOk_dataPointersBound {α β : Type} (heap : List (HeapElement α β)) (limit : Nat)
    (valid : heapOk heap limit) :
    ∀ children len data ptr value,
      .pointer ptr value ∈ children → .dataElement children len data ∈ heap → ptr < heapLength heap := by
  intro children len data ptr value child object
  obtain ⟨xs, size, payload, found⟩ := valid.2.2 children len data ptr value ⟨object, child⟩
  exact heapLookup_less heap ptr (.dataElement xs size payload) found

/-- Flapjack proof infrastructure: roots valid for a heap are within its
encoded extent. -/
theorem rootsOk_pointersBound {α β γ : Type} (heap : List (HeapElement β γ))
    (roots : List (HeapAddress α)) (valid : rootsOk roots heap) :
    ∀ ptr value, .pointer ptr value ∈ roots → ptr < heapLength heap := by
  intro ptr value member
  obtain ⟨children, len, data, found⟩ := valid ptr value member
  exact heapLookup_less heap ptr (.dataElement children len data) found

/-- Flapjack proof infrastructure: the original heap's pointer bounds survive
both the initial root traversal and remembered-reference traversal. -/
theorem gcMoveRootsRefs_dataPointersBound {α β γ : Type} (conf : Config β)
    (state middle final : GcState α β) (roots roots1 : List (HeapAddress α))
    (refs refs1 : List (HeapElement α γ)) (limit : Nat)
    (valid : heapOk state.heap limit) (empty : state.h2 = [])
    (rootRun : gcMoveList conf state roots = (roots1, middle))
    (refsRun : gcMoveRefList conf middle refs = (refs1, final)) :
    ∀ children len data ptr value,
      .pointer ptr value ∈ children → .dataElement children len data ∈ final.heap ++ final.h2 →
        ptr < heapLength final.heap := by
  have initial : ∀ children len data ptr value,
      .pointer ptr value ∈ children → .dataElement children len data ∈ state.heap ++ state.h2 →
        ptr < heapLength state.heap := by
    intro children len data ptr value child object
    apply heapOk_dataPointersBound state.heap limit valid children len data ptr value child
    simpa [empty] using object
  have middleBound := gcMoveList_dataPointersBound conf state middle roots roots1 rootRun initial
  exact gcMoveRefList_dataPointersBound conf middle final refs refs1 refsRun middleBound

/-- Flapjack proof infrastructure: children of the original reference segment
remain bounded after a heap-length-preserving root traversal. -/
theorem heapOk_referenceSegmentBound {α β : Type} (conf : Config β)
    (heap old current refs : List (HeapElement α β)) (state : GcState α β)
    (valid : heapOk heap conf.limit)
    (segment : heapSegment (conf.genStart, conf.refsStart) heap = some (old, current, refs))
    (size : heapLength state.heap = heapLength heap) :
    ∀ children len data ptr value,
      .pointer ptr value ∈ children ∧ .dataElement children len data ∈ refs →
        ptr < heapLength state.heap := by
  obtain ⟨whole, _, _, _⟩ := heapSegment_imp heap conf.genStart conf.refsStart old current refs segment
  intro children len data ptr value ⟨child, object⟩
  rw [size]
  apply heapOk_dataPointersBound heap conf.limit valid children len data ptr value child
  rw [← whole]
  simp [object]

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

/-- Flapjack proof infrastructure: moving the processed object from the
pending queue to the scanned prefix preserves the simulation invariant when
its rewritten children introduce no protected pointers. -/
theorem simInv_dataScanStep {α β : Type} (conf : Config β)
    (heap0 : List (HeapElement α β)) (state : GcState α β)
    (roots roots1 : List (HeapAddress α)) (len : Nat) (payload : β)
    (tail : List (HeapElement α β)) (flag : Bool)
    (invariant : simInv conf heap0 state)
    (pending : state.h2 = .dataElement roots len payload :: tail)
    (oldRoots : ∀ p, allOldPtrs conf roots1 p → allOldPtrs conf roots p) :
    simInv conf heap0 { state with
      h1 := state.h1 ++ [.dataElement roots1 len payload], h2 := tail, ok := flag } := by
  rcases invariant with ⟨gen, address, remaining, size, empty, old⟩
  refine ⟨gen, address, remaining, ?_, ?_, ?_⟩
  · simp only at size ⊢
    rw [pending] at size
    simp [heapLength, elLength] at size ⊢
    omega
  · intro degenerate
    obtain ⟨_, impossible⟩ := empty degenerate
    rw [pending] at impossible
    contradiction
  · intro ptr witness
    obtain ⟨children, objectLen, objectData, value, member, child, outside⟩ := witness
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with (((inHeap | inPrefix) | inTail) | inRefs)
    · exact old ptr ⟨children, objectLen, objectData, value, by simp [inHeap], child, outside⟩
    · rcases inPrefix with inPrefix | eq
      · exact old ptr ⟨children, objectLen, objectData, value, by simp [inPrefix], child, outside⟩
      · cases eq
        obtain ⟨prior, priorMem, priorOutside⟩ := oldRoots ptr ⟨value, child, outside⟩
        apply old ptr
        exact ⟨roots, len, payload, prior, by simp [pending], priorMem, priorOutside⟩
    · exact old ptr ⟨children, objectLen, objectData, value, by simp [pending, inTail], child, outside⟩
    · exact old ptr ⟨children, objectLen, objectData, value, by simp [inRefs], child, outside⟩

/-- Flapjack proof infrastructure: translating a partial scan step produces
the major collector's corresponding queue and scanned-prefix update. -/
theorem toGenState_dataScanStep {α β : Type} (conf : Config β)
    (state : GcState α β) (roots roots1 : List (HeapAddress α))
    (len : Nat) (payload : β) (tail : List (HeapElement α β)) (flag : Bool)
    (pending : state.h2 = .dataElement roots len payload :: tail) :
    toGenState conf { state with
      h1 := state.h1 ++ [.dataElement roots1 len payload], h2 := tail, ok := flag } =
    { toGenState conf state with
      h1 := (toGenState conf state).h1 ++
        [.dataElement (roots1.map (toGenHeapAddress conf)) len payload],
      h2 := (toGenState conf state).h2.drop 1, ok := flag } := by
  simp [toGenState, toGenHeapList, toGenHeapElement, pending]

/-- Flapjack proof infrastructure: a successful pair of child-list moves
establishes the invariant and pointer bound for the next copied-data scan. -/
theorem gcMoveData_simulationStep {α β : Type} (conf : Config β)
    (heap0 : List (HeapElement α β)) (state middle : GcState α β)
    (roots roots1 : List (HeapAddress α)) (len : Nat) (payload : β)
    (tail : List (HeapElement α β))
    (majorRoots : List (HeapAddress (DataSort (HeapAddress α) α)))
    (majorMiddle : GcState (DataSort (HeapAddress α) α) β)
    (pending : state.h2 = .dataElement roots len payload :: tail)
    (invariant : simInv conf heap0 state)
    (bounded : ∀ children size data ptr value,
      .pointer ptr value ∈ children → .dataElement children size data ∈ state.heap ++ state.h2 →
        ptr < heapLength state.heap)
    (heapLengthEq : heapLength state.heap = conf.limit)
    (run : gcMoveList conf state roots = (roots1, middle))
    (majorRun : GenGc.gcMoveList (toGenConf conf) (toGenState conf state)
      (roots.map (toGenHeapAddress conf)) = (majorRoots, majorMiddle))
    (majorOk : majorMiddle.ok = true) :
    ∃ tail1, middle.h2 = .dataElement roots len payload :: tail1 ∧
      (majorRoots, majorMiddle) = (roots1.map (toGenHeapAddress conf), toGenState conf middle) ∧
      ∀ flag, let next := { middle with
        h1 := middle.h1 ++ [.dataElement roots1 len payload], h2 := tail1, ok := flag }
      simInv conf heap0 next ∧ heapLength next.heap = conf.limit ∧
      (∀ children size data ptr value,
        .pointer ptr value ∈ children → .dataElement children size data ∈ next.heap ++ next.h2 →
          ptr < heapLength next.heap) ∧
      toGenState conf next = { toGenState conf middle with
        h1 := (toGenState conf middle).h1 ++
          [.dataElement (roots1.map (toGenHeapAddress conf)) len payload],
        h2 := (toGenState conf middle).h2.drop 1, ok := flag } := by
  have rootBound : ∀ ptr value, .pointer ptr value ∈ roots → ptr < heapLength state.heap := by
    intro ptr value member
    apply bounded roots len payload ptr value member
    simp [pending]
  obtain ⟨middleInv, equal, oldRoots⟩ :=
    gcMoveList_simulation conf heap0 roots state middle roots1 majorRoots majorMiddle
      run invariant rootBound heapLengthEq majorRun majorOk
  obtain ⟨tail1, nextPending⟩ :=
    gcMoveList_preservesPendingHead conf state middle roots roots1 _ tail pending run
  refine ⟨tail1, nextPending, equal, ?_⟩
  intro flag
  dsimp only
  refine ⟨simInv_dataScanStep conf heap0 middle roots roots1 len payload tail1 flag middleInv nextPending oldRoots,
    ?_, ?_, toGenState_dataScanStep conf middle roots roots1 len payload tail1 flag nextPending⟩
  · exact (gcMoveList_heapLength roots roots1 conf state middle run).symm.trans heapLengthEq
  · have nextBound := gcMoveList_dataScanNextBound conf state middle roots roots1 run bounded
    simpa [nextPending] using nextBound

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

/-- Flapjack proof infrastructure: functional form of the partial copied-data
scan simulation. -/
theorem gcMoveData_simulationCore {α β : Type} (conf : Config β) (state : GcState α β) :
    ∀ (heap0 : List (HeapElement α β)),
      simInv conf heap0 state →
      (∀ children len data ptr value, .pointer ptr value ∈ children →
        .dataElement children len data ∈ state.heap ++ state.h2 → ptr < heapLength state.heap) →
      heapLength state.heap = conf.limit →
      (GenGc.gcMoveData (toGenConf conf) (toGenState conf state)).ok = true →
      simInv conf heap0 (gcMoveData conf state) ∧
      GenGc.gcMoveData (toGenConf conf) (toGenState conf state) = toGenState conf (gcMoveData conf state) := by
  classical
  induction state using gcMoveData.induct conf with
  | case1 state empty =>
    intro heap0 invariant bounded size success
    rw [gcMoveData]
    simp only [empty]
    have majorEmpty : (toGenState conf state).h2 = [] := by simp [toGenState, toGenHeapList, empty]
    rw [GenGc.gcMoveData]
    simp [majorEmpty, invariant]
  | case2 state head tail heap over =>
    intro heap0 invariant bounded size success
    have limits := (simInv_dataScanLimits conf heap0 state invariant).1
    rw [heap] at limits
    omega
  | case3 state tail roots len payload roots1 middle move heap scanBound flag ih =>
    intro heap0 invariant bounded size success
    have lengthEq : heapLength ((toGenState conf state).h1 ++ (toGenState conf state).h2) =
        heapLength (state.h1 ++ state.h2) := by
      simpa [toGenState, toGenHeapList, List.map_append] using
        heapLength_toGenHeapList conf (state.h1 ++ state.h2)
    have majorPending : (toGenState conf state).h2 =
        .dataElement (roots.map (toGenHeapAddress conf)) len payload :: toGenHeapList conf tail := by
      simp [toGenState, toGenHeapList, toGenHeapElement, heap]
    have majorBound : ¬ (toGenConf conf).limit <
        heapLength ((toGenState conf state).h1 ++
          .dataElement (roots.map (toGenHeapAddress conf)) len payload :: toGenHeapList conf tail) := by
      rw [← majorPending, lengthEq]
      exact Nat.not_lt.mpr (simInv_dataScanLimits conf heap0 state invariant).2
    cases majorRun : GenGc.gcMoveList (toGenConf conf) (toGenState conf state)
        (roots.map (toGenHeapAddress conf)) with
    | mk majorRoots majorMiddle =>
      rw [GenGc.gcMoveData] at success
      simp only [majorPending, majorBound, ↓reduceIte, majorRun] at success
      have middleOk := GenGc.gcMoveData_ok (toGenConf conf) _ success
      simp only [Bool.and_eq_true] at middleOk
      obtain ⟨tail1, middlePending, equal, step⟩ :=
        gcMoveData_simulationStep conf heap0 state middle roots roots1 len payload tail
          majorRoots majorMiddle heap invariant bounded size move majorRun middleOk.1.1
      obtain ⟨rootsEq, middleEq⟩ := Prod.mk.inj equal
      subst majorRoots
      subst majorMiddle
      have majorNext : (GenGc.gcMoveData (toGenConf conf)
          { toGenState conf middle with
            h1 := (toGenState conf middle).h1 ++
              [.dataElement (roots1.map (toGenHeapAddress conf)) len payload],
            h2 := (toGenState conf middle).h2.drop 1, ok := middle.ok }).ok = true := by
        simpa [toGenState, toGenHeapList, toGenHeapElement, middlePending] using success
      obtain ⟨nextInv, nextSize, nextBound, nextEq⟩ := step middle.ok
      have nextSuccess : (GenGc.gcMoveData (toGenConf conf)
          (toGenState conf { middle with
            h1 := middle.h1 ++ [.dataElement roots1 len payload], h2 := tail1, ok := middle.ok })).ok = true := by
        rw [nextEq]
        exact majorNext
      have majorEq : GenGc.gcMoveData (toGenConf conf) (toGenState conf state) =
          GenGc.gcMoveData (toGenConf conf)
            (toGenState conf { middle with
              h1 := middle.h1 ++ [.dataElement roots1 len payload], h2 := tail1, ok := middle.ok }) := by
        rw [GenGc.gcMoveData]
        simp only [majorPending, majorBound, ↓reduceIte, majorRun]
        rw [nextEq]
        simp [toGenState, toGenHeapList, toGenHeapElement, middlePending]
      dsimp only [flag] at ih
      simp only [middlePending, List.drop_succ_cons, List.drop_zero, List.head?_cons,
        ne_eq, List.cons_ne_nil, not_false_eq_true, decide_true, Bool.and_true] at ih
      have result := ih heap0 nextInv nextBound nextSize nextSuccess
      rw [gcMoveData]
      simp only [heap, scanBound, ↓reduceIte, move, middlePending, List.drop_succ_cons,
        List.drop_zero, List.head?_cons, ne_eq, List.cons_ne_nil, not_false_eq_true, decide_true, Bool.and_true]
      rw [majorEq]
      exact result
  | case4 state head tail heap scanBound notData =>
    intro heap0 invariant bounded size success
    have lengthEq : heapLength ((toGenState conf state).h1 ++ (toGenState conf state).h2) =
        heapLength (state.h1 ++ state.h2) := by
      simpa [toGenState, toGenHeapList, List.map_append] using
        heapLength_toGenHeapList conf (state.h1 ++ state.h2)
    have majorBound : ¬ (toGenConf conf).limit <
        heapLength ((toGenState conf state).h1 ++ (toGenState conf state).h2) := by
      rw [lengthEq]
      exact Nat.not_lt.mpr (simInv_dataScanLimits conf heap0 state invariant).2
    cases head with
    | unused n =>
      rw [GenGc.gcMoveData] at success
      simp [toGenState, toGenHeapList, toGenHeapElement, heap] at majorBound success
    | forwardPointer ptr value n =>
      rw [GenGc.gcMoveData] at success
      simp [toGenState, toGenHeapList, toGenHeapElement, heap] at majorBound success
    | dataElement children n data => exact False.elim (notData children n data rfl)

/-- Partial copied-data scanning simulates the major collector and preserves
the simulation invariant. The local HOL proof has not yet been replayed. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_data_simulation"]
theorem gcMoveData_simulation {α β : Type} (conf : Config β)
    (state state1 : GcState α β) (heap0 : List (HeapElement α β))
    (majorState : GcState (DataSort (HeapAddress α) α) β)
    (partialRun : gcMoveData conf state = state1)
    (invariant : simInv conf heap0 state)
    (bounded : ∀ children len data ptr value,
      .pointer ptr value ∈ children → .dataElement children len data ∈ state.h2 ++ state.heap →
        ptr < heapLength state.heap)
    (size : heapLength state.heap = conf.limit)
    (majorRun : GenGc.gcMoveData (toGenConf conf) (toGenState conf state) = majorState)
    (majorOk : majorState.ok = true) :
    simInv conf heap0 state1 ∧ majorState = toGenState conf state1 := by
  have bounded' : ∀ children len data ptr value,
      .pointer ptr value ∈ children → .dataElement children len data ∈ state.heap ++ state.h2 →
        ptr < heapLength state.heap := by
    intro children len data ptr value child member
    apply bounded children len data ptr value child
    simpa [List.mem_append, or_comm] using member
  have success : (GenGc.gcMoveData (toGenConf conf) (toGenState conf state)).ok = true := by
    rw [majorRun]
    exact majorOk
  have result := gcMoveData_simulationCore conf state heap0 invariant bounded' size success
  rw [partialRun, majorRun] at result
  exact result

/-- Flapjack proof infrastructure: the state created by partial collection
satisfies the simulation invariant before any roots are moved. -/
theorem partialGc_initialSimInv {α β : Type} (conf : Config β)
    (heap old current refs : List (HeapElement α β))
    (good : heapOk heap conf.limit) (generations : heapGenOk heap conf)
    (segment : heapSegment (conf.genStart, conf.refsStart) heap = some (old, current, refs)) :
    simInv conf heap { emptyGcState with
      heap := heap, old := old, r2 := refs, a := conf.genStart, n := heapLength current } := by
  have gen := heapGenOk_genInv conf heap good generations
  obtain ⟨_, oldLen, endLen, _⟩ :=
    heapSegment_imp heap conf.genStart conf.refsStart old current refs segment
  rw [heapLength_append, oldLen] at endLen
  have upper := gen.2.1
  have emptyLength : heapLength ([] : List (HeapElement α β)) = 0 := rfl
  simp only [simInv, emptyGcState, emptyLength, List.append_nil]
  refine ⟨gen, Nat.le_refl _, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro _; simp
  · intro ptr member
    exact member

/-- Flapjack proof infrastructure: translating the initial partial state gives
the major collector's initial state for the current generation. -/
theorem partialGc_initialTranslation {α β : Type} (conf : Config β)
    (heap old current refs : List (HeapElement α β))
    (generations : heapGenOk heap conf)
    (segment : heapSegment (conf.genStart, conf.refsStart) heap = some (old, current, refs)) :
    toGenState conf { emptyGcState with
      heap := heap, old := old, r2 := refs, a := conf.genStart, n := heapLength current } =
    ({ emptyGcState with
      heap := toGenHeapList conf current, n := (toGenConf conf).limit,
      ok := decide (heapLength (toGenHeapList conf current) = (toGenConf conf).limit) } :
      GcState (DataSort (HeapAddress α) α) β) := by
  obtain ⟨_, oldLen, endLen, _⟩ :=
    heapSegment_imp heap conf.genStart conf.refsStart old current refs segment
  rw [heapLength_append, oldLen] at endLen
  obtain ⟨_, _, _, lower, upper, _⟩ := generations
  have limit : (toGenConf conf).limit = heapLength current := by
    simp only [toGenConf]
    omega
  have translated : toGenHeap conf heap = toGenHeapList conf current := by
    simp [toGenHeap, heapRestrict, segment]
  have empty : toGenHeap conf ([] : List (HeapElement α β)) = [] := by
    by_cases a : conf.genStart = 0 <;> by_cases b : conf.refsStart = 0 <;>
      simp [toGenHeap, heapRestrict, heapSegment, heapSplit, toGenHeapList, heapLength, a, b]
  have length : heapLength (current.map (toGenHeapElement conf)) = heapLength current := by
    simpa [toGenHeapList] using heapLength_toGenHeapList conf current
  simp [toGenState, emptyGcState, translated, empty, limit, toGenHeapList, length]

/-- Flapjack proof infrastructure: installing references whose protected
pointers came from the original heap preserves the simulation invariant. -/
theorem simInv_installRefs {α β : Type} (conf : Config β)
    (heap0 : List (HeapElement α β)) (state : GcState α β)
    (refs : List (HeapElement α β)) (invariant : simInv conf heap0 state)
    (oldRefs : ∀ ptr, hasOldPtr conf refs ptr → hasOldPtr conf heap0 ptr) :
    simInv conf heap0 { state with r2 := [], r1 := refs } := by
  rcases invariant with ⟨gen, address, remaining, size, empty, old⟩
  refine ⟨gen, address, remaining, size, empty, ?_⟩
  intro ptr ⟨children, len, data, value, member, child, outside⟩
  simp only [List.mem_append] at member
  rcases member with ((inHeap | inPrefix) | inPending) | inRefs
  · exact old ptr ⟨children, len, data, value, by simp [inHeap], child, outside⟩
  · exact old ptr ⟨children, len, data, value, by simp [inPrefix], child, outside⟩
  · exact old ptr ⟨children, len, data, value, by simp [inPending], child, outside⟩
  · exact oldRefs ptr ⟨children, len, data, value, inRefs, child, outside⟩

/-- Flapjack proof infrastructure: under the partial simulation invariant, a
successful major loop on the translated state consists of the data scan alone. -/
theorem gcMoveData_majorLoopSimulation {α β : Type} (conf : Config β)
    (heap0 : List (HeapElement α β)) (state : GcState α β) (clock : Nat)
    (invariant : simInv conf heap0 state)
    (bounded : ∀ children len data ptr value,
      .pointer ptr value ∈ children → .dataElement children len data ∈ state.heap ++ state.h2 →
        ptr < heapLength state.heap)
    (size : heapLength state.heap = conf.limit)
    (success : (GenGc.gcMoveLoop (toGenConf conf) (toGenState conf state) clock).ok = true) :
    simInv conf heap0 (gcMoveData conf state) ∧
    GenGc.gcMoveLoop (toGenConf conf) (toGenState conf state) clock =
      toGenState conf (gcMoveData conf state) := by
  classical
  have noRefs : (toGenState conf state).r4 = [] := rfl
  cases pending : (toGenState conf state).h2 with
  | nil =>
    have sourceEmpty : state.h2 = [] := by
      cases h : state.h2 with
      | nil => rfl
      | cons head tail => simp [toGenState, toGenHeapList, h] at pending
    rw [gcMoveData]
    simp only [sourceEmpty]
    rw [GenGc.gcMoveLoop]
    simp [noRefs, pending, invariant]
  | cons head tail =>
    cases clock with
    | zero =>
      rw [GenGc.gcMoveLoop] at success
      simp [noRefs, pending] at success
    | succ clock =>
      have loopSuccess : (GenGc.gcMoveLoop (toGenConf conf)
          (GenGc.gcMoveData (toGenConf conf) (toGenState conf state)) clock).ok = true := by
        rw [GenGc.gcMoveLoop] at success
        simpa only [noRefs, pending, Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one] using success
      have dataOk := GenGc.gcMoveLoop_ok (toGenConf conf)
        (GenGc.gcMoveData (toGenConf conf) (toGenState conf state)) clock loopSuccess
      obtain ⟨resultInv, resultEq⟩ := gcMoveData_simulationCore conf state heap0 invariant bounded size dataOk
      have dataEmpty := GenGc.gcMoveData_h2 (toGenConf conf) (toGenState conf state) dataOk
      have dataNoRefs : (GenGc.gcMoveData (toGenConf conf) (toGenState conf state)).r4 = [] := by
        rw [resultEq]
        rfl
      have loopDone : GenGc.gcMoveLoop (toGenConf conf)
          (GenGc.gcMoveData (toGenConf conf) (toGenState conf state)) clock =
          GenGc.gcMoveData (toGenConf conf) (toGenState conf state) := by
        rw [GenGc.gcMoveLoop]
        simp only [dataNoRefs, dataEmpty]
      refine ⟨resultInv, ?_⟩
      rw [GenGc.gcMoveLoop]
      simp only [noRefs, pending, Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
      exact loopDone.trans resultEq

/-- Flapjack proof infrastructure: the successful major loop also establishes
success and an empty data queue for the simulated partial scan. -/
theorem gcMoveData_majorLoopComplete {α β : Type} (conf : Config β)
    (heap0 : List (HeapElement α β)) (state : GcState α β) (clock : Nat)
    (invariant : simInv conf heap0 state)
    (bounded : ∀ children len data ptr value,
      .pointer ptr value ∈ children → .dataElement children len data ∈ state.heap ++ state.h2 →
        ptr < heapLength state.heap)
    (size : heapLength state.heap = conf.limit)
    (success : (GenGc.gcMoveLoop (toGenConf conf) (toGenState conf state) clock).ok = true) :
    simInv conf heap0 (gcMoveData conf state) ∧
    GenGc.gcMoveLoop (toGenConf conf) (toGenState conf state) clock =
      toGenState conf (gcMoveData conf state) ∧
    (gcMoveData conf state).h2 = [] ∧ (gcMoveData conf state).ok = true := by
  obtain ⟨resultInv, resultEq⟩ :=
    gcMoveData_majorLoopSimulation conf heap0 state clock invariant bounded size success
  rw [resultEq] at success
  have partialOk : (gcMoveData conf state).ok = true := by simpa [toGenState] using success
  exact ⟨resultInv, resultEq, gcMoveData_h2 conf state partialOk, partialOk⟩

/-- Flapjack proof infrastructure: the final partial scan can start after the
processed references are installed, while the major loop continues from the
same translated state. -/
theorem gcMoveData_majorLoopAfterRefs {α β : Type} (conf : Config β)
    (heap0 : List (HeapElement α β)) (state : GcState α β)
    (refs : List (HeapElement α β)) (clock : Nat)
    (invariant : simInv conf heap0 state)
    (oldRefs : ∀ ptr, hasOldPtr conf refs ptr → hasOldPtr conf heap0 ptr)
    (bounded : ∀ children len data ptr value,
      .pointer ptr value ∈ children → .dataElement children len data ∈ state.heap ++ state.h2 →
        ptr < heapLength state.heap)
    (size : heapLength state.heap = conf.limit)
    (success : (GenGc.gcMoveLoop (toGenConf conf) (toGenState conf state) clock).ok = true) :
    let final := gcMoveData conf { state with r2 := [], r1 := refs }
    simInv conf heap0 final ∧
    GenGc.gcMoveLoop (toGenConf conf) (toGenState conf state) clock = toGenState conf final ∧
    final.h2 = [] ∧ final.ok = true ∧ final.r1 = refs := by
  have nextInv := simInv_installRefs conf heap0 state refs invariant oldRefs
  have translated : toGenState conf { state with r2 := [], r1 := refs } = toGenState conf state := rfl
  have nextSuccess : (GenGc.gcMoveLoop (toGenConf conf)
      (toGenState conf { state with r2 := [], r1 := refs }) clock).ok = true := by
    rw [translated]
    exact success
  obtain ⟨finalInv, finalEq, finalEmpty, finalOk⟩ :=
    gcMoveData_majorLoopComplete conf heap0 { state with r2 := [], r1 := refs } clock
      nextInv bounded size nextSuccess
  dsimp only
  rw [translated] at finalEq
  exact ⟨finalInv, finalEq, finalEmpty, finalOk, gcMoveData_r1 conf _⟩

/-- Partial collection simulates major collection on the current generation.
The local HOL proof and inferred types have not yet been replayed. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "partial_gc_simulation"]
theorem partialGc_simulation {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (heap old current refs : List (HeapElement α β))
    (state1 : GcState α β)
    (majorRoots : List (HeapAddress (DataSort (HeapAddress α) α)))
    (majorState : GcState (DataSort (HeapAddress α) α) β)
    (partialRun : partialGc conf (roots, heap) = (roots1, state1))
    (generations : heapGenOk heap conf)
    (_ordered : conf.genStart ≤ conf.refsStart ∧ conf.refsStart ≤ conf.limit)
    (segment : heapSegment (conf.genStart, conf.refsStart) heap = some (old, current, refs))
    (_nonrefs : List.Forall (fun e => heapElementIsRef conf e = false) (old ++ current))
    (refData : List.Forall isDataElement refs) (validRoots : rootsOk roots heap)
    (majorRun : GenGc.genGc (toGenConf conf)
      (toGenRoots conf roots ++ refsToRoots conf refs, toGenHeapList conf current) = (majorRoots, majorState))
    (validHeap : heapOk heap conf.limit) (majorOk : majorState.ok = true) :
    majorRoots = toGenRoots conf roots1 ++ refsToRoots conf state1.r1 ∧
    majorState = toGenState conf state1 ∧ simInv conf heap state1 ∧ state1.h2 = [] ∧ state1.ok = true := by
  classical
  let initial : GcState α β := { emptyGcState with
    heap := heap, old := old, r2 := refs, a := conf.genStart, n := heapLength current }
  have initialInv : simInv conf heap initial := partialGc_initialSimInv conf heap old current refs validHeap generations segment
  have initialEq : toGenState conf initial =
      ({ emptyGcState with
        heap := toGenHeapList conf current, n := (toGenConf conf).limit,
        ok := decide (heapLength (toGenHeapList conf current) = (toGenConf conf).limit) } :
        GcState (DataSort (HeapAddress α) α) β) :=
    partialGc_initialTranslation conf heap old current refs generations segment
  simp only [partialGc, segment] at partialRun
  change (let (roots', next) := gcMoveList conf initial roots
    let (refs', afterRefs) := gcMoveRefList conf next refs
    (roots', gcMoveData conf { afterRefs with r1 := refs', r2 := [] })) = (roots1, state1) at partialRun
  cases rootRun : gcMoveList conf initial roots with
  | mk movedRoots afterRoots =>
    cases refsRun : gcMoveRefList conf afterRoots refs with
    | mk movedRefs afterRefs =>
      simp only [rootRun, refsRun, Prod.mk.injEq] at partialRun
      obtain ⟨rfl, rfl⟩ := partialRun
      simp only [GenGc.genGc] at majorRun
      rw [← initialEq] at majorRun
      simp only [toGenRoots] at majorRun
      rw [majorMoveList_append] at majorRun
      cases majorRootRun : GenGc.gcMoveList (toGenConf conf) (toGenState conf initial)
          (roots.map (toGenHeapAddress conf)) with
      | mk majorMovedRoots majorAfterRoots =>
        cases majorRefsRun : GenGc.gcMoveList (toGenConf conf) majorAfterRoots (refsToRoots conf refs) with
        | mk majorMovedRefs majorAfterRefs =>
          simp only [majorRootRun, majorRefsRun, Prod.mk.injEq] at majorRun
          obtain ⟨rfl, rfl⟩ := majorRun
          have refsOk := GenGc.gcMoveLoop_ok (toGenConf conf) majorAfterRefs (toGenConf conf).limit majorOk
          have rootsOk := GenGc.gcMoveList_ok (toGenConf conf) (refsToRoots conf refs)
            majorMovedRefs majorAfterRoots majorAfterRefs majorRefsRun refsOk
          have rootsBound : ∀ ptr value, .pointer ptr value ∈ roots → ptr < heapLength initial.heap := by
            simpa [initial] using rootsOk_pointersBound heap roots validRoots
          have initialSize : heapLength initial.heap = conf.limit := by simpa [initial] using validHeap.1
          obtain ⟨rootsInv, rootsEq, _⟩ := gcMoveList_simulation conf heap roots initial afterRoots
            movedRoots majorMovedRoots majorAfterRoots rootRun initialInv rootsBound initialSize majorRootRun rootsOk
          obtain ⟨majorRootsEq, majorRootsStateEq⟩ := Prod.mk.inj rootsEq
          subst majorMovedRoots
          subst majorAfterRoots
          have rootsSize : heapLength afterRoots.heap = heapLength heap := by
            simpa [initial] using (gcMoveList_heapLength roots movedRoots conf initial afterRoots rootRun).symm
          have refsBound := heapOk_referenceSegmentBound conf heap old current refs afterRoots validHeap segment rootsSize
          have rootsLimit : heapLength afterRoots.heap = conf.limit := rootsSize.trans validHeap.1
          obtain ⟨refsInv, majorRefsEq, majorRefsStateEq, oldRefs⟩ :=
            gcMoveRefList_simulation conf afterRoots afterRefs refs movedRefs heap majorMovedRefs majorAfterRefs
              refsRun majorRefsRun refsOk rootsInv refsBound rootsLimit refData
          subst majorMovedRefs
          subst majorAfterRefs
          have originalRefs : ∀ ptr, hasOldPtr conf refs ptr → hasOldPtr conf heap ptr := by
            intro ptr ⟨children, len, data, value, member, child, outside⟩
            obtain ⟨whole, _, _, _⟩ := heapSegment_imp heap conf.genStart conf.refsStart old current refs segment
            refine ⟨children, len, data, value, ?_, child, outside⟩
            rw [← whole]
            simp [member]
          have movedOld : ∀ ptr, hasOldPtr conf movedRefs ptr → hasOldPtr conf heap ptr := by
            intro ptr member
            exact originalRefs ptr (oldRefs ptr member)
          have finalBound := gcMoveRootsRefs_dataPointersBound conf initial afterRoots afterRefs roots movedRoots
            refs movedRefs conf.limit (by simpa [initial] using validHeap) (by simp [initial, emptyGcState]) rootRun refsRun
          have finalSize : heapLength afterRefs.heap = conf.limit := by
            exact (gcMoveRefList_heapLength conf refs movedRefs afterRoots afterRefs refsRun).symm.trans rootsLimit
          obtain ⟨finalInv, finalEq, finalEmpty, finalOk, finalRefs⟩ :=
            gcMoveData_majorLoopAfterRefs conf heap afterRefs movedRefs (toGenConf conf).limit
              refsInv movedOld finalBound finalSize majorOk
          refine ⟨?_, finalEq, finalInv, finalEmpty, finalOk⟩
          simp [toGenRoots, finalRefs]

/-- Flapjack proof infrastructure: a translated pointer must come from a
pointer in the current generation. -/
theorem toGenHeapAddress_pointerInv {α β : Type} (conf : Config β) (root : HeapAddress α)
    (ptr : Nat) (value : DataSort (HeapAddress α) α)
    (translated : toGenHeapAddress conf root = .pointer ptr value) :
    ∃ original originalValue, root = .pointer original originalValue ∧
      ptr = original - conf.genStart ∧ value = .real originalValue ∧
      conf.genStart ≤ original ∧ original < conf.refsStart := by
  cases root with
  | data originalValue => simp [toGenHeapAddress] at translated
  | pointer original originalValue =>
    by_cases lower : original < conf.genStart
    · simp [toGenHeapAddress, lower] at translated
    · by_cases upper : conf.refsStart ≤ original
      · simp [toGenHeapAddress, lower, upper] at translated
      · simp [toGenHeapAddress, lower, upper] at translated
        obtain ⟨rfl, rfl⟩ := translated
        exact ⟨original, originalValue, rfl, rfl, rfl, Nat.le_of_not_gt lower, Nat.lt_of_not_ge upper⟩

/-- Every pointer in translated roots comes from a current-generation pointer.
The local HOL proof has not yet been replayed. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "MEM_to_gen_roots_IMP_MEM"]
theorem mem_toGenRoots_pointerInv {α β : Type} (conf : Config β) (roots : List (HeapAddress α))
    (ptr : Nat) (value : DataSort (HeapAddress α) α)
    (member : .pointer ptr value ∈ toGenRoots conf roots) :
    ∃ original originalValue, .pointer original originalValue ∈ roots ∧
      ptr = original - conf.genStart ∧ value = .real originalValue ∧
      conf.genStart ≤ original ∧ original < conf.refsStart := by
  obtain ⟨root, member, translated⟩ := List.mem_map.mp member
  obtain ⟨original, originalValue, eq, ptrEq, valueEq, lower, upper⟩ :=
    toGenHeapAddress_pointerInv conf root ptr value translated
  subst root
  exact ⟨original, originalValue, member, ptrEq, valueEq, lower, upper⟩

/-- Every pointer extracted from translated reference objects comes from a
current-generation child. The local HOL proof has not yet been replayed. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "MEM_refs_to_roots_IMP_MEM"]
theorem mem_refsToRoots_pointerInv {α β γ : Type} (conf : Config β)
    (refs : List (HeapElement α γ)) (ptr : Nat) (value : DataSort (HeapAddress α) α)
    (member : .pointer ptr value ∈ refsToRoots conf refs) :
    ∃ children len data original originalValue,
      .dataElement children len data ∈ refs ∧ .pointer original originalValue ∈ children ∧
      ptr = original - conf.genStart ∧ value = .real originalValue ∧
      conf.genStart ≤ original ∧ original < conf.refsStart := by
  induction refs with
  | nil => simp [refsToRoots] at member
  | cons head tail ih =>
    cases head with
    | unused len =>
      simp only [refsToRoots] at member
      obtain ⟨children, size, data, original, originalValue, object, child, ptrEq, valueEq, lower, upper⟩ := ih member
      exact ⟨children, size, data, original, originalValue, by simp [object], child, ptrEq, valueEq, lower, upper⟩
    | forwardPointer dest old len =>
      simp only [refsToRoots] at member
      obtain ⟨children, size, data, original, originalValue, object, child, ptrEq, valueEq, lower, upper⟩ := ih member
      exact ⟨children, size, data, original, originalValue, by simp [object], child, ptrEq, valueEq, lower, upper⟩
    | dataElement children len data =>
      simp only [refsToRoots, List.mem_append] at member
      rcases member with child | rest
      · obtain ⟨original, originalValue, child, ptrEq, valueEq, lower, upper⟩ :=
          mem_toGenRoots_pointerInv conf children ptr value child
        exact ⟨children, len, data, original, originalValue, by simp, child, ptrEq, valueEq, lower, upper⟩
      · obtain ⟨children, size, payload, original, originalValue, object, child, ptrEq, valueEq, lower, upper⟩ := ih rest
        exact ⟨children, size, payload, original, originalValue, by simp [object], child, ptrEq, valueEq, lower, upper⟩

/-- Translating a heap preserves whether a lookup finds a data element. The
local HOL proof has not yet been replayed. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "isSomeDataElement_to_gen_heap_list"]
theorem isSomeDataElement_toGenHeapList {α β γ : Type} (conf : Config γ)
    (heap : List (HeapElement α β)) (ptr : Nat) :
    isSomeDataElement (heapLookup ptr (toGenHeapList conf heap)) ↔
      isSomeDataElement (heapLookup ptr heap) := by
  rw [heapLookup_toGenHeapList]
  cases found : heapLookup ptr heap with
  | none => simp [isSomeDataElement]
  | some element => cases element <;> simp [isSomeDataElement, toGenHeapElement]

/-- Valid roots and reference children remain valid in the translated current
generation. The local HOL proof has not yet been replayed. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "roots_ok_simulation"]
theorem rootsOk_simulation {α β : Type} (conf : Config β) (roots : List (HeapAddress α))
    (heap old current refs : List (HeapElement α β)) (validRoots : rootsOk roots heap)
    (validHeap : heapOk heap conf.limit)
    (segment : heapSegment (conf.genStart, conf.refsStart) heap = some (old, current, refs))
    (_ordered : conf.genStart ≤ conf.refsStart) :
    rootsOk (toGenRoots conf roots ++ refsToRoots conf refs) (toGenHeapList conf current) := by
  obtain ⟨whole, oldLen, endLen, _⟩ := heapSegment_imp heap conf.genStart conf.refsStart old current refs segment
  have lookupCurrent : ∀ ptr, conf.genStart ≤ ptr → ptr < conf.refsStart →
      isSomeDataElement (heapLookup ptr heap) →
      isSomeDataElement (heapLookup (ptr - conf.genStart) (toGenHeapList conf current)) := by
    intro ptr lower upper found
    have inside : ptr - conf.genStart < heapLength current := by
      rw [heapLength_append, oldLen] at endLen
      omega
    have lookup : heapLookup ptr heap = heapLookup (ptr - conf.genStart) current := by
      rw [← whole, List.append_assoc, GenGc.heapLookup_append, oldLen,
        if_neg (Nat.not_lt.mpr lower), GenGc.heapLookup_append, if_pos inside]
    apply (isSomeDataElement_toGenHeapList conf current (ptr - conf.genStart)).mpr
    simpa [lookup] using found
  intro ptr value member
  rcases List.mem_append.mp member with root | reference
  · obtain ⟨original, originalValue, originalMember, ptrEq, _, lower, upper⟩ :=
      mem_toGenRoots_pointerInv conf roots ptr value root
    subst ptr
    exact lookupCurrent original lower upper (validRoots original originalValue originalMember)
  · obtain ⟨children, len, data, original, originalValue, object, child, ptrEq, _, lower, upper⟩ :=
      mem_refsToRoots_pointerInv conf refs ptr value reference
    have inHeap : .dataElement children len data ∈ heap := by
      rw [← whole]
      simp [object]
    subst ptr
    exact lookupCurrent original lower upper (validHeap.2.2 children len data original originalValue ⟨inHeap, child⟩)

/-- A valid heap's current-generation segment remains valid after translation.
The local HOL proof has not yet been replayed. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "heap_ok_simulation"]
theorem heapOk_simulation {α β : Type} (conf : Config β)
    (heap old current refs : List (HeapElement α β)) (validHeap : heapOk heap conf.limit)
    (segment : heapSegment (conf.genStart, conf.refsStart) heap = some (old, current, refs))
    (lower : conf.genStart ≤ conf.refsStart) (upper : conf.refsStart ≤ conf.limit) :
    heapOk (toGenHeapList conf current) (toGenConf conf).limit := by
  obtain ⟨whole, oldLen, endLen, _⟩ := heapSegment_imp heap conf.genStart conf.refsStart old current refs segment
  have currentMember : ∀ element ∈ current, element ∈ heap := by
    intro element member
    rw [← whole]
    simp [member]
  have noForward : ∀ element ∈ heap, isForwardPointer element = false := by
    intro element member
    cases flag : isForwardPointer element with
    | false => rfl
    | true =>
      have inFilter : element ∈ heap.filter isForwardPointer := by simp [member, flag]
      rw [validHeap.2.1] at inFilter
      simp at inFilter
  refine ⟨?_, ?_, ?_⟩
  · rw [heapLength_append, oldLen] at endLen
    rw [heapLength_toGenHeapList]
    simp only [toGenConf]
    omega
  · apply List.filter_eq_nil_iff.mpr
    intro element member
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
    have original := noForward source (currentMember source sourceMember)
    cases source <;> simp [toGenHeapElement, isForwardPointer] at original ⊢
  · intro children len data ptr value ⟨object, child⟩
    obtain ⟨source, sourceMember, eq⟩ := List.mem_map.mp object
    cases source with
    | unused size => simp [toGenHeapElement] at eq
    | forwardPointer dest old size => simp [toGenHeapElement] at eq
    | dataElement original size payload =>
      simp only [toGenHeapElement, HeapElement.dataElement.injEq] at eq
      obtain ⟨rfl, rfl, rfl⟩ := eq
      have originalRoots : rootsOk original heap := by
        intro originalPtr originalValue member
        exact validHeap.2.2 original size payload originalPtr originalValue
          ⟨currentMember _ sourceMember, member⟩
      have translatedRoots := rootsOk_simulation conf original heap old current refs
        originalRoots validHeap segment lower
      apply translatedRoots ptr value
      exact List.mem_append.mpr (Or.inl child)

/-- Flapjack proof infrastructure: valid partial-collection input has a
successful partial result satisfying the simulation invariant. -/
theorem partialGc_success {α β : Type} (conf : Config β)
    (roots : List (HeapAddress α)) (heap : List (HeapElement α β))
    (validRoots : rootsOk roots heap) (validHeap : heapOk heap conf.limit)
    (generations : heapGenOk heap conf) :
    ∃ roots1 state1, partialGc conf (roots, heap) = (roots1, state1) ∧
      simInv conf heap state1 ∧ state1.h2 = [] ∧ state1.ok = true := by
  have gen := heapGenOk_genInv conf heap validHeap generations
  obtain ⟨lower, upper, old, current, refs, segment, oldNonrefs, currentNonrefs, refData, _⟩ := gen
  have nonrefs : List.Forall (fun e => heapElementIsRef conf e = false) (old ++ current) :=
    List.forall_append.mpr ⟨oldNonrefs, currentNonrefs⟩
  have translatedRoots := rootsOk_simulation conf roots heap old current refs validRoots validHeap segment lower
  have translatedHeap := heapOk_simulation conf heap old current refs validHeap segment lower upper
  obtain ⟨majorState, majorRun, _, majorInv, _⟩ :=
    GenGc.genGc_invariant (toGenConf conf) (toGenRoots conf roots ++ refsToRoots conf refs)
      (toGenHeapList conf current) translatedRoots translatedHeap
  have majorOk : majorState.ok = true := majorInv.2.2.2.2.1
  cases partialRun : partialGc conf (roots, heap) with
  | mk roots1 state1 =>
    obtain ⟨_, _, invariant, empty, ok⟩ := partialGc_simulation conf roots roots1 heap old current refs
      state1 _ majorState partialRun generations ⟨lower, upper⟩ segment nonrefs refData validRoots majorRun validHeap majorOk
    exact ⟨roots1, state1, rfl, invariant, empty, ok⟩

/-- Data-object addresses outside the generation being collected. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "f_old_ptrs_def"]
def fOldPtrs {α β γ : Type} (conf : Config γ) (heap : List (HeapElement α β)) : Set Nat :=
  { ptr | isSomeDataElement (heapLookup ptr heap) ∧ (ptr < conf.genStart ∨ conf.refsStart ≤ ptr) }

/-- The set of unchanged data-object addresses is finite. The original HOL
proof has not yet been replayed. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "f_old_ptrs_finite"]
theorem fOldPtrs_finite {α β γ : Type} (heap : List (HeapElement α β)) (conf : Config γ) :
    (fOldPtrs conf heap).Finite := by
  apply (Set.finite_lt_nat (heapLength heap)).subset
  intro ptr member
  obtain ⟨children, len, data, found⟩ := member.1
  exact heapLookup_less heap ptr (.dataElement children len data) found

open Classical in
/-- Raw lookup used by Flapjack's finite forwarding-map construction. -/
noncomputable def newForwardLookup {α β γ : Type} (f : Nat → Option Nat)
    (conf : Config γ) (heap : List (HeapElement α β)) (ptr : Nat) : Option Nat :=
  if ptr ∈ fOldPtrs conf heap then some ptr
  else if conf.genStart ≤ ptr then (f (ptr - conf.genStart)).map (conf.genStart + ·)
  else none

/-- The partial collector's combined forwarding map, using canonical
finite-support maps for the HOL input and result. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "new_f_def"
  (fmap_as_finite_support_result)]
noncomputable def newForwardMap {α β γ : Type} (f : HolFiniteMapExact Nat Nat)
    (conf : Config γ) (heap : List (HeapElement α β)) : HolFiniteMapExact Nat Nat := by
  classical
  refine ⟨newForwardLookup f.lookup conf heap, ?_⟩
  obtain ⟨keys, supported⟩ := f.finiteSupport
  refine ⟨List.range (heapLength heap) ++ keys.map (conf.genStart + ·), ?_⟩
  intro ptr present
  unfold newForwardLookup at present
  split at present
  · rename_i old
    apply List.mem_append.mpr
    left
    apply List.mem_range.mpr
    obtain ⟨children, len, data, found⟩ := old.1
    exact heapLookup_less heap ptr (.dataElement children len data) found
  · split at present
    · rename_i lower
      apply List.mem_append.mpr
      right
      apply List.mem_map.mpr
      refine ⟨ptr - conf.genStart, ?_, ?_⟩
      · apply supported
        intro absent
        simp [absent] at present
      · omega
    · contradiction

/-- The finite-map translation agrees with the independent raw lookup. -/
theorem holFmapAsFiniteSupportResultWitness_newForwardMap {α β γ : Type}
    (f : HolFiniteMapExact Nat Nat) (conf : Config γ) (heap : List (HeapElement α β)) (ptr : Nat) :
    (newForwardMap f conf heap).lookup ptr = newForwardLookup f.lookup conf heap ptr := rfl

/-- Flapjack infrastructure: valid pointers outside the current generation
are mapped to themselves. -/
theorem newForwardMap_old {α β γ : Type} (f : HolFiniteMapExact Nat Nat)
    (conf : Config γ) (heap : List (HeapElement α β)) (ptr : Nat)
    (old : ptr ∈ fOldPtrs conf heap) : (newForwardMap f conf heap).lookup ptr = some ptr := by
  simp [newForwardMap, newForwardLookup, old]

/-- Flapjack infrastructure: a current-generation pointer is forwarded by
the translated major-collector map. -/
theorem newForwardMap_current {α β γ : Type} (f : HolFiniteMapExact Nat Nat)
    (conf : Config γ) (heap : List (HeapElement α β)) (ptr : Nat)
    (lower : conf.genStart ≤ ptr) (upper : ptr < conf.refsStart) :
    (newForwardMap f conf heap).lookup ptr =
      (f.lookup (ptr - conf.genStart)).map (conf.genStart + ·) := by
  have notOld : ptr ∉ fOldPtrs conf heap := by
    simp [fOldPtrs, Nat.not_lt.mpr lower, Nat.not_le.mpr upper]
  simp [newForwardMap, newForwardLookup, notOld, lower]

open Classical in
/-- Flapjack infrastructure: characterization of the combined forwarding-map
domain. The finite-map representation has not yet been classified for HOL. -/
theorem newForwardMap_domain {α β γ : Type} (f : HolFiniteMapExact Nat Nat)
    (conf : Config γ) (heap : List (HeapElement α β)) (ptr : Nat)
    (valid : ∀ i, f.lookup i ≠ none → isSomeDataElement (heapLookup (i + conf.genStart) heap)) :
    ((newForwardMap f conf heap).lookup ptr ≠ none) ↔
      if ptr < conf.genStart ∨ conf.refsStart ≤ ptr then
        isSomeDataElement (heapLookup ptr heap)
      else ∃ i, f.lookup i ≠ none ∧ ptr = conf.genStart + i := by
  by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
  · simp only [outside, ↓reduceIte]
    by_cases data : isSomeDataElement (heapLookup ptr heap)
    · have old : ptr ∈ fOldPtrs conf heap := ⟨data, outside⟩
      simp [newForwardMap_old f conf heap ptr old, data]
    · have absent : conf.genStart ≤ ptr → f.lookup (ptr - conf.genStart) = none := by
        intro lower
        by_contra found
        have isData := valid (ptr - conf.genStart) found
        have address : ptr - conf.genStart + conf.genStart = ptr := by omega
        rw [address] at isData
        exact data isData
      simpa [newForwardMap, newForwardLookup, fOldPtrs, outside, data] using absent
  · have lower : conf.genStart ≤ ptr := by omega
    have upper : ptr < conf.refsStart := by omega
    have mapDomain : (f.lookup (ptr - conf.genStart)).map (conf.genStart + ·) ≠ none ↔
        f.lookup (ptr - conf.genStart) ≠ none := by
      cases f.lookup (ptr - conf.genStart) <;> simp
    simp only [outside, ↓reduceIte, newForwardMap_current f conf heap ptr lower upper, mapDomain]
    constructor
    · intro found
      exact ⟨ptr - conf.genStart, found, by omega⟩
    · rintro ⟨i, found, eq⟩
      have : ptr - conf.genStart = i := by omega
      simpa [this] using found

open Classical in
/-- Flapjack infrastructure: applying the combined forwarding map at a
defined key agrees with the appropriate source-region rule. -/
theorem newForwardMap_apply {α β γ : Type} (f : HolFiniteMapExact Nat Nat)
    (conf : Config γ) (heap : List (HeapElement α β)) (ptr : Nat)
    (present : (newForwardMap f conf heap).lookup ptr ≠ none)
    (valid : ∀ i, f.lookup i ≠ none → isSomeDataElement (heapLookup (i + conf.genStart) heap)) :
    holFapply (newForwardMap f conf heap) ptr =
      if ptr < conf.genStart ∨ conf.refsStart ≤ ptr then ptr
      else conf.genStart + holFapply f (ptr - conf.genStart) := by
  by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
  · simp only [outside, ↓reduceIte]
    have data : isSomeDataElement (heapLookup ptr heap) := by
      simpa only [outside, ↓reduceIte] using (newForwardMap_domain f conf heap ptr valid).mp present
    exact holFapply_of_lookup (newForwardMap_old f conf heap ptr ⟨data, outside⟩)
  · simp only [outside, ↓reduceIte]
    have lower : conf.genStart ≤ ptr := by omega
    have upper : ptr < conf.refsStart := by omega
    have current := newForwardMap_current f conf heap ptr lower upper
    cases found : f.lookup (ptr - conf.genStart) with
    | none => simp [found] at current; exact False.elim (present current)
    | some value =>
      rw [holFapply_of_lookup found]
      apply holFapply_of_lookup
      simpa [found] using current

/-- Flapjack infrastructure: when similar reference heads have equal child
counts, equality of their flattened renamed roots splits at that head. -/
theorem similarData_refRootsSplit {α β γ : Type} (conf : Config γ)
    (xs ys : List (HeapAddress α)) (len : Nat) (payload : β)
    (left right : List (HeapElement α β)) (rename : Nat → Nat)
    (similar : List.Forall₂ (similarPtr conf) xs ys)
    (equal : addrMap rename (refsToRoots conf (.dataElement xs len payload :: left)) =
      refsToRoots conf (.dataElement ys len payload :: right)) :
    addrMap rename (xs.map (toGenHeapAddress conf)) = ys.map (toGenHeapAddress conf) ∧
      addrMap rename (refsToRoots conf left) = refsToRoots conf right := by
  simp only [refsToRoots, addrMap_append] at equal
  apply List.append_inj equal
  simp [← addrMap_length, similar.length_eq]

/-- Flapjack infrastructure: flattening similar reference lists preserves
the boundary between a head object and the remaining objects. -/
theorem similarData_refRootsTail {α β γ : Type} (conf : Config γ)
    (head1 head2 : HeapElement α β) (left right : List (HeapElement α β)) (rename : Nat → Nat)
    (similar : similarData conf head1 head2)
    (equal : addrMap rename (refsToRoots conf (head1 :: left)) = refsToRoots conf (head2 :: right)) :
    addrMap rename (refsToRoots conf left) = refsToRoots conf right := by
  cases head1 with
  | unused len =>
    cases head2 <;> simp_all [similarData, refsToRoots]
  | forwardPointer ptr value len =>
    cases head2 <;> simp_all [similarData, refsToRoots]
  | dataElement xs len payload =>
    cases head2 with
    | unused n => simp [similarData] at similar
    | forwardPointer ptr value n => simp [similarData] at similar
    | dataElement ys n data =>
      simp only [similarData] at similar
      obtain ⟨rfl, rfl, children⟩ := similar
      exact (similarData_refRootsSplit conf xs ys n data left right rename children equal).2

/-- Flapjack infrastructure: related heap elements have equal encoded lengths. -/
theorem similarData_elLength {α β γ : Type} (conf : Config γ)
    (left right : HeapElement α β) (similar : similarData conf left right) :
    elLength left = elLength right := by
  cases left <;> cases right <;> simp_all [similarData, elLength]

/-- Flapjack proof infrastructure: lookup in similar reference lists retains
the object's payload and its segment of the renamed flattened roots. -/
theorem heapLookup_similarData_raw {α β γ : Type} (conf : Config γ)
    (left right : List (HeapElement α β)) (n : Nat) (xs : List (HeapAddress α))
    (len : Nat) (payload : β) (rename : Nat → Nat)
    (related : List.Forall₂ (similarData conf) left right)
    (found : heapLookup n left = some (.dataElement xs len payload))
    (rootsEq : addrMap rename (refsToRoots conf left) = refsToRoots conf right) :
    ∃ ys, heapLookup n right = some (.dataElement ys len payload) ∧
      addrMap rename (xs.map (toGenHeapAddress conf)) = ys.map (toGenHeapAddress conf) := by
  induction related generalizing n with
  | nil => simp [heapLookup] at found
  | @cons head1 head2 left right head tail ih =>
    by_cases zero : n = 0
    · subst n
      simp [heapLookup] at found
      subst head1
      cases head2 with
      | unused size => simp [similarData] at head
      | forwardPointer ptr value size => simp [similarData] at head
      | dataElement ys size data =>
        simp only [similarData] at head
        obtain ⟨rfl, rfl, children⟩ := head
        exact ⟨ys, by simp [heapLookup],
          (similarData_refRootsSplit conf xs ys size data left right rename children rootsEq).1⟩
    · by_cases inside : n < elLength head1
      · simp [heapLookup, zero, inside] at found
      · have equalLength := similarData_elLength conf head1 head2 head
        have targetInside : ¬ n < elLength head2 := by simpa [← equalLength] using inside
        have foundTail : heapLookup (n - elLength head1) left = some (.dataElement xs len payload) := by
          simpa [heapLookup, zero, inside] using found
        have rootsTail := similarData_refRootsTail conf head1 head2 left right rename head rootsEq
        obtain ⟨ys, targetFound, targetRoots⟩ := ih (n - elLength head1) foundTail rootsTail
        refine ⟨ys, ?_, targetRoots⟩
        simpa [heapLookup, zero, targetInside, ← equalLength, inside] using targetFound

/-- Related reference heaps preserve lookup results and their renamed child
roots. The local HOL proof has not yet been replayed.

Intended HOL counterpart, pending statement and finite-map carrier source review.
Former reference: @[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "heap_lookup_similar_data_IMP" (fmap_as_finite_support_parameters := [f])] -/
theorem heapLookup_similarData {α β γ : Type} (conf : Config γ)
    (left right : List (HeapElement α β)) (n : Nat) (xs : List (HeapAddress α))
    (len : Nat) (payload : β) (f : HolFiniteMapExact Nat Nat)
    (related : List.Forall₂ (similarData conf) left right)
    (found : heapLookup n left = some (.dataElement xs len payload))
    (rootsEq : addrMap (holFapply f) (refsToRoots conf left) = refsToRoots conf right) :
    ∃ ys, heapLookup n right = some (.dataElement ys len payload) ∧
      addrMap (holFapply f) (xs.map (toGenHeapAddress conf)) = ys.map (toGenHeapAddress conf) :=
  heapLookup_similarData_raw conf left right n xs len payload (holFapply f) related found rootsEq

/-- Canonical finite-map parameter codec for the related-heap lookup result. -/
theorem holFmapAsFiniteSupportParamWitness_heapLookup_similarData_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (GcMapBroad.ofBroad (GcMapBroad.toBroad f)).lookup key = f.lookup key ∧
    (GcMapBroad.ofBroad (GcMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    GcMapBroad.ofBroad (GcMapBroad.toBroad f) = f :=
  holFmapAsFiniteSupportParamWitness_gcRelated_f f key

/-- Flapjack proof infrastructure: a segmented partial collection keeps the
old region and produces a reference list similar to the original one. -/
theorem partialGc_regions {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (heap old current refs : List (HeapElement α β))
    (state : GcState α β)
    (segment : heapSegment (conf.genStart, conf.refsStart) heap = some (old, current, refs))
    (run : partialGc conf (roots, heap) = (roots1, state)) :
    state.old = old ∧ List.Forall₂ (similarData conf) refs state.r1 := by
  classical
  simp only [partialGc, segment] at run
  generalize rootRun : gcMoveList conf
    { emptyGcState with heap := heap, old := old, r2 := refs, a := conf.genStart, n := heapLength current }
    roots = result at run
  obtain ⟨movedRoots, middle⟩ := result
  generalize refRun : gcMoveRefList conf middle refs = result at run
  obtain ⟨movedRefs, afterRefs⟩ := result
  simp only [Prod.mk.injEq] at run
  obtain ⟨_, rfl⟩ := run
  have rootFixed := DataToWord.Proofs.Gc.partialMoveList_fixedFields conf roots movedRoots _ middle rootRun
  have refFixed := DataToWord.Proofs.Gc.partialFull_refListFixed conf refs movedRefs middle afterRefs refRun
  have dataFixed := DataToWord.Proofs.Gc.partialFull_dataFixed conf { afterRefs with r1 := movedRefs, r2 := [] }
  have refSimilar := gcMoveRefList_similar conf refs movedRefs middle afterRefs refRun
  simp only at dataFixed
  refine ⟨?_, ?_⟩
  · exact dataFixed.2.2.2.2.1.trans (refFixed.2.2.2.2.2.trans rootFixed.2.2.2.2.2)
  · simpa only [gcMoveData_r1] using refSimilar

/-- Flapjack proof infrastructure: lookup in similar heap lists preserves an
object's encoded size and payload. -/
theorem heapLookup_similarShape {α β γ : Type} (conf : Config γ)
    (left right : List (HeapElement α β)) (n : Nat) (xs : List (HeapAddress α))
    (len : Nat) (payload : β) (related : List.Forall₂ (similarData conf) left right)
    (found : heapLookup n left = some (.dataElement xs len payload)) :
    ∃ ys, heapLookup n right = some (.dataElement ys len payload) := by
  induction related generalizing n with
  | nil => simp [heapLookup] at found
  | @cons head1 head2 left right head tail ih =>
    by_cases zero : n = 0
    · subst n
      simp [heapLookup] at found
      subst head1
      cases head2 with
      | unused size => simp [similarData] at head
      | forwardPointer ptr value size => simp [similarData] at head
      | dataElement ys size data =>
        simp only [similarData] at head
        obtain ⟨rfl, rfl, _⟩ := head
        exact ⟨ys, by simp [heapLookup]⟩
    · by_cases inside : n < elLength head1
      · simp [heapLookup, zero, inside] at found
      · have equalLength := similarData_elLength conf head1 head2 head
        have targetInside : ¬ n < elLength head2 := by simpa [← equalLength] using inside
        have foundTail : heapLookup (n - elLength head1) left = some (.dataElement xs len payload) := by
          simpa [heapLookup, zero, inside] using found
        obtain ⟨ys, targetFound⟩ := ih (n - elLength head1) foundTail
        refine ⟨ys, ?_⟩
        simpa [heapLookup, zero, targetInside, ← equalLength, inside] using targetFound

/-- Lookup of an old-generation object is unchanged by partial collection.
The local HOL proof has not yet been replayed. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "heap_lookup_old_IMP"]
theorem heapLookup_old {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (heap : List (HeapElement α β)) (state : GcState α β)
    (ptr : Nat) (tail : List (HeapElement α β)) (children : List (HeapAddress α)) (len : Nat) (data : β)
    (run : partialGc conf (roots, heap) = (roots1, state)) (invariant : genInv conf heap)
    (found : heapLookup ptr heap = some (.dataElement children len data)) (before : ptr < conf.genStart) :
    heapLookup ptr (state.old ++ tail) = some (.dataElement children len data) := by
  obtain ⟨_, _, old, current, refs, segment, _⟩ := invariant
  have oldEq := (partialGc_regions conf roots roots1 heap old current refs state segment run).1
  obtain ⟨whole, oldLen, _, _⟩ := heapSegment_imp heap conf.genStart conf.refsStart old current refs segment
  rw [← whole, List.append_assoc, GenGc.heapLookup_append, oldLen, if_pos before] at found
  rw [oldEq, GenGc.heapLookup_append, oldLen, if_pos before]
  exact found

/-- Lookup of a reference-region object after partial collection preserves its
size and payload. The local HOL proof has not yet been replayed. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "heap_lookup_refs_IMP"]
theorem heapLookup_refs {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (heap : List (HeapElement α β)) (state : GcState α β)
    (ptr : Nat) (children : List (HeapAddress α)) (len : Nat) (data : β)
    (run : partialGc conf (roots, heap) = (roots1, state)) (invariant : genInv conf heap)
    (found : heapLookup ptr heap = some (.dataElement children len data))
    (prefixSize : heapLength (state.old ++ state.h1 ++ heapExpand state.n) = conf.refsStart)
    (after : conf.refsStart ≤ ptr) :
    ∃ children1, heapLookup ptr (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1) =
      some (.dataElement children1 len data) := by
  obtain ⟨_, _, old, current, refs, segment, _⟩ := invariant
  have refsSimilar := (partialGc_regions conf roots roots1 heap old current refs state segment run).2
  obtain ⟨whole, _, endLen, _⟩ := heapSegment_imp heap conf.genStart conf.refsStart old current refs segment
  rw [← whole, GenGc.heapLookup_append, endLen, if_neg (Nat.not_lt.mpr after)] at found
  obtain ⟨children1, refFound⟩ :=
    heapLookup_similarShape conf refs state.r1 (ptr - conf.refsStart) children len data refsSimilar found
  refine ⟨children1, ?_⟩
  rw [GenGc.heapLookup_append, prefixSize, if_neg (Nat.not_lt.mpr after)]
  exact refFound

/-- Flapjack proof infrastructure: after a successful partial scan, the
copied generation and its free space end at the reference-region boundary. -/
theorem partialGc_outputPrefixLength {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (heap : List (HeapElement α β)) (state : GcState α β)
    (run : partialGc conf (roots, heap) = (roots1, state)) (original : genInv conf heap)
    (invariant : simInv conf heap state) (empty : state.h2 = []) :
    heapLength (state.old ++ state.h1 ++ heapExpand state.n) = conf.refsStart := by
  obtain ⟨_, _, old, current, refs, segment, _⟩ := original
  have oldEq := (partialGc_regions conf roots roots1 heap old current refs state segment run).1
  obtain ⟨_, oldLen, _, _⟩ := heapSegment_imp heap conf.genStart conf.refsStart old current refs segment
  have balance := invariant.2.2.2.1
  simp only [empty, List.append_nil] at balance
  simp only [heapLength_append, heapLength_heapExpand, oldEq, oldLen]
  exact balance

/-- Flapjack proof infrastructure: protected pointers in copied objects and
scanned references still point to data in the final partial-collection heap. -/
theorem partialGc_protectedPointersValid {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (heap : List (HeapElement α β)) (state : GcState α β)
    (run : partialGc conf (roots, heap) = (roots1, state)) (original : genInv conf heap)
    (valid : heapOk heap conf.limit) (invariant : simInv conf heap state) (empty : state.h2 = [])
    (ptr : Nat) (member : hasOldPtr conf (state.h1 ++ state.r1) ptr) :
    isSomeDataElement (heapLookup ptr (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1)) := by
  obtain ⟨children, len, data, value, object, child, outside⟩ := member
  have tracked : hasOldPtr conf (state.heap ++ state.h1 ++ state.h2 ++ state.r1) ptr := by
    refine ⟨children, len, data, value, ?_, child, outside⟩
    simp only [List.mem_append] at object ⊢
    tauto
  have originalPtr := invariant.2.2.2.2.2 ptr tracked
  obtain ⟨oldChildren, oldLen, oldData, oldValue, oldObject, oldChild, oldOutside⟩ := originalPtr
  have found := valid.2.2 oldChildren oldLen oldData ptr oldValue ⟨oldObject, oldChild⟩
  obtain ⟨targetChildren, targetLen, targetData, targetFound⟩ := found
  rcases oldOutside with before | after
  · have output := heapLookup_old conf roots roots1 heap state ptr
      (state.h1 ++ heapExpand state.n ++ state.r1) targetChildren targetLen targetData run original targetFound before
    exact ⟨targetChildren, targetLen, targetData, by simpa [List.append_assoc] using output⟩
  · have boundary := partialGc_outputPrefixLength conf roots roots1 heap state run original invariant empty
    obtain ⟨resultChildren, resultFound⟩ :=
      heapLookup_refs conf roots roots1 heap state ptr targetChildren targetLen targetData run original targetFound boundary after
    exact ⟨resultChildren, targetLen, targetData, resultFound⟩

/-- The final partial-collector prefix ends at the reference-generation
boundary when the corresponding major collection is valid. The local HOL
proof has not yet been replayed. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "partial_gc_heap_length_lemma"]
theorem partialGc_heapLength {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (heap old current refs : List (HeapElement α β))
    (state : GcState α β) (majorRoots majorRoots1 : List (HeapAddress (DataSort (HeapAddress α) α)))
    (majorHeap : List (HeapElement (DataSort (HeapAddress α) α) β))
    (partialRun : partialGc conf (roots, heap) = (roots1, state))
    (majorRun : GenGc.genGc (toGenConf conf) (majorRoots, majorHeap) = (majorRoots1, toGenState conf state))
    (segment : heapSegment (conf.genStart, conf.refsStart) heap = some (old, current, refs))
    (lower : conf.genStart ≤ conf.refsStart) (upper : conf.refsStart ≤ conf.limit)
    (validRoots : rootsOk majorRoots majorHeap) (validHeap : heapOk majorHeap (toGenConf conf).limit) :
    heapLength (state.old ++ state.h1 ++ heapExpand state.n) = conf.refsStart := by
  have oldEq := (partialGc_regions conf roots roots1 heap old current refs state segment partialRun).1
  obtain ⟨_, oldLen, _, _⟩ := heapSegment_imp heap conf.genStart conf.refsStart old current refs segment
  obtain ⟨majorState, invariantRun, _, majorInv, majorEmpty, _⟩ :=
    GenGc.genGc_invariant (toGenConf conf) majorRoots majorHeap validRoots validHeap
  rw [majorRun] at invariantRun
  have stateEq := (Prod.mk.inj invariantRun).2
  subst majorState
  have sourceEmpty : state.h2 = [] := by
    simpa [toGenState, toGenHeapList] using majorEmpty
  have allocated := majorInv.1
  have balance := majorInv.2.1
  simp only [toGenState, emptyGcState, sourceEmpty, toGenHeapList, List.map_nil, List.append_nil] at allocated balance
  have emptyLen : heapLength ([] : List (HeapElement (DataSort (HeapAddress α) α) β)) = 0 := rfl
  simp only [emptyLen, Nat.add_zero] at balance
  have lengthEq := heapLength_toGenHeapList conf state.h1
  simp only [toGenHeapList] at lengthEq
  rw [lengthEq] at allocated
  simp only [toGenConf] at balance
  simp only [heapLength_append, heapLength_heapExpand, oldEq, oldLen]
  omega

/-- Equal flattened root and reference traversals split at the original
root-list boundary. The local HOL proof has not yet been replayed.

Intended HOL counterpart, pending statement and finite-map carrier source review.
Former reference: @[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "ADDR_MAP_APPEND_LENGTH_IMP" (fmap_as_finite_support_parameters := [f])] -/
theorem addrMap_appendLength {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (refs refs1 : List (HeapElement α β))
    (f : HolFiniteMapExact Nat Nat)
    (mapped : addrMap (holFapply f) (toGenRoots conf roots ++ refsToRoots conf refs) =
      toGenRoots conf roots1 ++ refsToRoots conf refs1)
    (sameLength : roots.length = roots1.length) :
    addrMap (holFapply f) (toGenRoots conf roots) = toGenRoots conf roots1 ∧
      addrMap (holFapply f) (refsToRoots conf refs) = refsToRoots conf refs1 := by
  rw [addrMap_append] at mapped
  apply List.append_inj mapped
  simpa [toGenRoots, ← addrMap_length] using sameLength

/-- Canonical finite-map parameter codec for splitting mapped roots. -/
theorem holFmapAsFiniteSupportParamWitness_addrMap_appendLength_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (GcMapBroad.ofBroad (GcMapBroad.toBroad f)).lookup key = f.lookup key ∧
    (GcMapBroad.ofBroad (GcMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    GcMapBroad.ofBroad (GcMapBroad.toBroad f) = f :=
  holFmapAsFiniteSupportParamWitness_gcRelated_f f key

/-- Flapjack proof infrastructure: one translated root correspondence gives
the matching combined forwarding-map result and its domain membership. -/
theorem translatedRoot_forwarding {α β γ : Type} (conf : Config γ)
    (heap : List (HeapElement α β)) (f : HolFiniteMapExact Nat Nat)
    (root target : HeapAddress α)
    (valid : ∀ ptr value, root = .pointer ptr value → isSomeDataElement (heapLookup ptr heap))
    (domain : ∀ ptr value, toGenHeapAddress conf root = .pointer ptr value → f.lookup ptr ≠ none)
    (related : addrApply (holFapply f) (toGenHeapAddress conf root) = toGenHeapAddress conf target) :
    target = addrApply (holFapply (newForwardMap f conf heap)) root ∧
      ∀ ptr value, root = .pointer ptr value → (newForwardMap f conf heap).lookup ptr ≠ none := by
  cases root with
  | data value =>
    cases target with
    | data targetValue => simp [toGenHeapAddress, addrApply] at related ⊢; exact related.symm
    | pointer ptr targetValue =>
      by_cases lower : ptr < conf.genStart <;> by_cases upper : conf.refsStart ≤ ptr <;>
        simp [toGenHeapAddress, addrApply, lower, upper] at related
  | pointer ptr value =>
    by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
    · have old : ptr ∈ fOldPtrs conf heap := ⟨valid ptr value rfl, outside⟩
      have mapped := newForwardMap_old f conf heap ptr old
      have mapValue : holFapply (newForwardMap f conf heap) ptr = ptr := holFapply_of_lookup mapped
      have protectedSource : toGenHeapAddress conf (.pointer ptr value) =
          .data (.protectedValue (.pointer ptr value)) := by
        rcases outside with lower | upper
        · simp [toGenHeapAddress, lower]
        · by_cases lower : ptr < conf.genStart <;> simp [toGenHeapAddress, lower, upper]
      rw [protectedSource] at related
      simp only [addrApply] at related
      have targetEq : target = .pointer ptr value := by
        cases target with
        | data targetValue => simp [toGenHeapAddress] at related
        | pointer targetPtr targetValue =>
          by_cases lower : targetPtr < conf.genStart <;> by_cases upper : conf.refsStart ≤ targetPtr <;>
            simp_all [toGenHeapAddress]
      subst target
      simp [addrApply, mapValue, mapped]
    · have lower : conf.genStart ≤ ptr := by omega
      have upper : ptr < conf.refsStart := by omega
      have nonlower : ¬ ptr < conf.genStart := Nat.not_lt.mpr lower
      have nonupper : ¬ conf.refsStart ≤ ptr := Nat.not_le.mpr upper
      have source : toGenHeapAddress conf (.pointer ptr value) =
          .pointer (ptr - conf.genStart) (.real value) := by
        simp [toGenHeapAddress, nonlower, nonupper]
      have present := domain (ptr - conf.genStart) (.real value) source
      cases found : f.lookup (ptr - conf.genStart) with
      | none => exact False.elim (present found)
      | some dest =>
        have mapped : (newForwardMap f conf heap).lookup ptr = some (conf.genStart + dest) := by
          rw [newForwardMap_current f conf heap ptr lower upper, found]
          rfl
        have mapValue := holFapply_of_lookup mapped
        rw [source] at related
        simp only [addrApply, holFapply_of_lookup found] at related
        cases target with
        | data targetValue => simp [toGenHeapAddress] at related
        | pointer targetPtr targetValue =>
          by_cases targetLower : targetPtr < conf.genStart
          · simp [toGenHeapAddress, targetLower] at related
          · by_cases targetUpper : conf.refsStart ≤ targetPtr
            · simp [toGenHeapAddress, targetLower, targetUpper] at related
            · simp [toGenHeapAddress, targetLower, targetUpper] at related
              obtain ⟨offsetEq, rfl⟩ := related
              have targetEq : targetPtr = conf.genStart + dest := by omega
              subst targetPtr
              simp [addrApply, mapValue, mapped]

/-- Flapjack infrastructure: address mapping is pointwise address application. -/
theorem addrMap_eq_mapApply {α : Type} (rename : Nat → Nat) (roots : List (HeapAddress α)) :
    addrMap rename roots = roots.map (addrApply rename) := by
  induction roots with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [addrMap, addrApply, ih]

/-- Flapjack proof infrastructure: translated root correspondence determines
the complete partial-collector forwarding map on the original roots. -/
theorem translatedRoots_forwarding {α β γ : Type} (conf : Config γ)
    (heap : List (HeapElement α β)) (f : HolFiniteMapExact Nat Nat)
    (roots roots1 : List (HeapAddress α)) (valid : rootsOk roots heap)
    (domain : ∀ ptr value, .pointer ptr value ∈ toGenRoots conf roots → f.lookup ptr ≠ none)
    (mapped : addrMap (holFapply f) (toGenRoots conf roots) = toGenRoots conf roots1)
    (sameLength : roots.length = roots1.length) :
    roots1 = addrMap (holFapply (newForwardMap f conf heap)) roots ∧
      ∀ ptr value, .pointer ptr value ∈ roots → (newForwardMap f conf heap).lookup ptr ≠ none := by
  induction roots generalizing roots1 with
  | nil =>
    cases roots1 with
    | nil => simp [addrMap]
    | cons head tail => simp at sameLength
  | cons root roots ih =>
    cases roots1 with
    | nil => simp at sameLength
    | cons root1 roots1 =>
      have mapped' : (root :: roots).map (fun value =>
          addrApply (holFapply f) (toGenHeapAddress conf value)) =
          (root1 :: roots1).map (toGenHeapAddress conf) := by
        simpa [toGenRoots, addrMap_eq_mapApply, List.map_map, Function.comp_def] using mapped
      simp only [List.map_cons, List.cons.injEq] at mapped'
      have rootValid : ∀ ptr value, root = .pointer ptr value → isSomeDataElement (heapLookup ptr heap) := by
        intro ptr value eq
        apply valid ptr value
        simp [← eq]
      have rootDomain : ∀ ptr value, toGenHeapAddress conf root = .pointer ptr value → f.lookup ptr ≠ none := by
        intro ptr value eq
        apply domain ptr value
        simp only [toGenRoots, List.map_cons, List.mem_cons]
        exact Or.inl eq.symm
      obtain ⟨headEq, headDomain⟩ := translatedRoot_forwarding conf heap f root root1 rootValid rootDomain mapped'.1
      have tailValid : rootsOk roots heap := by
        intro ptr value member
        exact valid ptr value (by simp [member])
      have tailDomain : ∀ ptr value, .pointer ptr value ∈ toGenRoots conf roots → f.lookup ptr ≠ none := by
        intro ptr value member
        apply domain ptr value
        simp only [toGenRoots, List.map_cons, List.mem_cons]
        exact Or.inr member
      have tailMapped : addrMap (holFapply f) (toGenRoots conf roots) = toGenRoots conf roots1 := by
        simpa [toGenRoots, addrMap_eq_mapApply, List.map_map, Function.comp_def] using mapped'.2
      have tailLength : roots.length = roots1.length := by simpa using sameLength
      obtain ⟨tailEq, tailDefined⟩ := ih roots1 tailValid tailDomain tailMapped tailLength
      refine ⟨?_, ?_⟩
      · simpa [addrMap_eq_mapApply] using congrArg₂ List.cons headEq tailEq
      · intro ptr value member
        simp only [List.mem_cons] at member
        rcases member with equal | member
        · exact headDomain ptr value equal.symm
        · exact tailDefined ptr value member

/-- Flapjack proof infrastructure: on valid input, the successful partial
collector's roots are exactly the original roots renamed by its combined
forwarding map, which is defined on every original root pointer. -/
theorem partialGc_rootsForwarded {α β : Type} (conf : Config β)
    (roots : List (HeapAddress α)) (heap : List (HeapElement α β))
    (validRoots : rootsOk roots heap) (validHeap : heapOk heap conf.limit)
    (generations : heapGenOk heap conf) :
    ∃ (roots1 : List (HeapAddress α)) (state1 : GcState α β) (f : HolFiniteMapExact Nat Nat),
      partialGc conf (roots, heap) = (roots1, state1) ∧
      roots1 = addrMap (holFapply (newForwardMap f conf heap)) roots ∧
      (∀ ptr value, .pointer ptr value ∈ roots → (newForwardMap f conf heap).lookup ptr ≠ none) ∧
      simInv conf heap state1 ∧ state1.h2 = [] ∧ state1.ok = true := by
  have gen := heapGenOk_genInv conf heap validHeap generations
  obtain ⟨lower, upper, old, current, refs, segment, oldNonrefs, currentNonrefs, refData, _⟩ := gen
  have nonrefs : List.Forall (fun e => heapElementIsRef conf e = false) (old ++ current) :=
    List.forall_append.mpr ⟨oldNonrefs, currentNonrefs⟩
  have translatedRoots := rootsOk_simulation conf roots heap old current refs validRoots validHeap segment lower
  have translatedHeap := heapOk_simulation conf heap old current refs validHeap segment lower upper
  obtain ⟨majorState, majorRun, majorDomain, majorInv, _⟩ :=
    GenGc.genGc_invariant (toGenConf conf) (toGenRoots conf roots ++ refsToRoots conf refs)
      (toGenHeapList conf current) translatedRoots translatedHeap
  have majorOk : majorState.ok = true := majorInv.2.2.2.2.1
  let f := heapMap 0 majorState.heap
  have majorRun' : GenGc.genGc (toGenConf conf)
      (toGenRoots conf roots ++ refsToRoots conf refs, toGenHeapList conf current) =
      (addrMap (holFapply f) (toGenRoots conf roots ++ refsToRoots conf refs), majorState) := by
    change GenGc.genGc (toGenConf conf)
      (toGenRoots conf roots ++ refsToRoots conf refs, toGenHeapList conf current) =
      (addrMap (holFapply (heapMap 0 majorState.heap)) (toGenRoots conf roots ++ refsToRoots conf refs), majorState) at majorRun
    exact majorRun
  cases partialRun : partialGc conf (roots, heap) with
  | mk roots1 state1 =>
    obtain ⟨rootsEq, _, invariant, empty, ok⟩ := partialGc_simulation conf roots roots1 heap old current refs
      state1 _ majorState partialRun generations ⟨lower, upper⟩ segment nonrefs refData validRoots majorRun' validHeap majorOk
    have length := partialGc_length conf roots roots1 heap state1 partialRun
    have split := addrMap_appendLength conf roots roots1 refs state1.r1 f rootsEq length.symm
    have rootsDomain : ∀ ptr value, .pointer ptr value ∈ toGenRoots conf roots → f.lookup ptr ≠ none := by
      intro ptr value member
      exact majorDomain ptr value (List.mem_append.mpr (Or.inl member))
    obtain ⟨mapped, domain⟩ := translatedRoots_forwarding conf heap f roots roots1 validRoots rootsDomain split.1 length.symm
    exact ⟨roots1, state1, f, rfl, mapped, domain, invariant, empty, ok⟩

/-- An expanded free region contains no data object at any offset. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "isSomeDataElement_heap_lookup_heap_expand"]
theorem heapLookup_heapExpand_notData {α β : Type} (ptr len : Nat) :
    ¬ isSomeDataElement (heapLookup ptr (heapExpand len : List (HeapElement α β))) := by
  cases len with
  | zero => simp [heapExpand, heapLookup, isSomeDataElement]
  | succ len =>
    by_cases zero : ptr = 0
    · simp [heapExpand, heapLookup, zero, isSomeDataElement]
    · simp [heapExpand, heapLookup, zero, isSomeDataElement]

/-- Flapjack proof infrastructure: translating free space leaves it unchanged. -/
theorem toGenHeapList_heapExpand {α β γ : Type} (conf : Config γ) (len : Nat) :
    toGenHeapList conf (heapExpand len : List (HeapElement α β)) =
      (heapExpand len : List (HeapElement (DataSort (HeapAddress α) α) β)) := by
  cases len <;> simp [toGenHeapList, toGenHeapElement, heapExpand]

/-- Flapjack proof infrastructure: a translated data lookup comes from a
data object with the same size and payload in the source heap. -/
theorem heapLookup_toGenData {α β γ : Type} (conf : Config γ)
    (heap : List (HeapElement α β)) (ptr : Nat)
    (children : List (HeapAddress (DataSort (HeapAddress α) α))) (len : Nat) (payload : β)
    (found : heapLookup ptr (toGenHeapList conf heap) = some (.dataElement children len payload)) :
    ∃ original, heapLookup ptr heap = some (.dataElement original len payload) ∧
      original.map (toGenHeapAddress conf) = children := by
  rw [heapLookup_toGenHeapList] at found
  cases source : heapLookup ptr heap with
  | none => simp [source] at found
  | some element =>
    cases element with
    | unused size => simp [source, toGenHeapElement] at found
    | forwardPointer dest value size => simp [source, toGenHeapElement] at found
    | dataElement original size data =>
      simp only [source, Option.map_some, toGenHeapElement, Option.some.injEq, HeapElement.dataElement.injEq] at found
      obtain ⟨childrenEq, rfl, rfl⟩ := found
      exact ⟨original, rfl, childrenEq⟩

/-- Flapjack proof infrastructure: a translated copied-object lookup with
renamed children yields the corresponding object in the partial output heap. -/
theorem heapLookup_forwardedData {α β γ : Type} (conf : Config γ)
    (sourceHeap copied refs : List (HeapElement α β)) (free ptr : Nat)
    (children : List (HeapAddress α)) (len : Nat) (payload : β) (f : HolFiniteMapExact Nat Nat)
    (found : heapLookup ptr (toGenHeapList conf copied ++ heapExpand free) =
      some (.dataElement (addrMap (holFapply f) (children.map (toGenHeapAddress conf))) len payload))
    (valid : ∀ p value, .pointer p value ∈ children → isSomeDataElement (heapLookup p sourceHeap))
    (domain : ∀ p value, .pointer p value ∈ children.map (toGenHeapAddress conf) → f.lookup p ≠ none) :
    heapLookup ptr (copied ++ heapExpand free ++ refs) =
      some (.dataElement (addrMap (holFapply (newForwardMap f conf sourceHeap)) children) len payload) := by
  have translated : toGenHeapList conf (copied ++ heapExpand free) =
      toGenHeapList conf copied ++ heapExpand free := by
    simp only [toGenHeapList, List.map_append]
    change _ ++ toGenHeapList conf (heapExpand free : List (HeapElement α β)) = _
    rw [toGenHeapList_heapExpand]
  rw [← translated] at found
  obtain ⟨original, sourceFound, originalRoots⟩ :=
    heapLookup_toGenData conf (copied ++ heapExpand free) ptr _ len payload found
  have rootsEq : addrMap (holFapply f) (toGenRoots conf children) = toGenRoots conf original := by
    simpa [toGenRoots] using originalRoots.symm
  have sameLength : children.length = original.length := by
    have equalLength := congrArg List.length rootsEq
    simpa [toGenRoots, ← addrMap_length] using equalLength
  have originalValid : rootsOk children sourceHeap := valid
  have originalDomain : ∀ p value, .pointer p value ∈ toGenRoots conf children → f.lookup p ≠ none := domain
  obtain ⟨mapped, _⟩ := translatedRoots_forwarding conf sourceHeap f children original
    originalValid originalDomain rootsEq sameLength
  have inBounds := heapLookup_less (copied ++ heapExpand free) ptr _ sourceFound
  rw [GenGc.heapLookup_append, if_pos inBounds]
  simpa [mapped] using sourceFound

/-- Flapjack proof infrastructure: the reconstructed partial-collector heap
has the same encoded length as the original valid heap. -/
theorem partialGc_outputLength {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (heap : List (HeapElement α β)) (state : GcState α β)
    (run : partialGc conf (roots, heap) = (roots1, state)) (original : genInv conf heap)
    (valid : heapOk heap conf.limit) (invariant : simInv conf heap state) (empty : state.h2 = []) :
    heapLength (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1) = conf.limit := by
  have boundary := partialGc_outputPrefixLength conf roots roots1 heap state run original invariant empty
  obtain ⟨_, _, old, current, refs, segment, _⟩ := original
  have refsSimilar := (partialGc_regions conf roots roots1 heap old current refs state segment run).2
  have refsLength := (similarData_lengths conf refs state.r1 refsSimilar).1
  obtain ⟨whole, _, _, tailLen⟩ := heapSegment_imp heap conf.genStart conf.refsStart old current refs segment
  have heapLen := valid.1
  rw [heapLength_append, boundary, ← refsLength, tailLen, heapLen]
  have ordered := invariant.1.2.1
  omega

/-- Flapjack proof infrastructure: if the translated final state satisfies the
major collector invariant, the reconstructed partial heap has no forwarding
pointers. -/
theorem partialGc_outputNoForward {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (heap : List (HeapElement α β)) (state : GcState α β)
    (majorHeap : List (HeapElement (DataSort (HeapAddress α) α) β))
    (majorRoots : List (HeapAddress (DataSort (HeapAddress α) α)))
    (run : partialGc conf (roots, heap) = (roots1, state)) (original : genInv conf heap)
    (valid : heapOk heap conf.limit)
    (majorInv : GenGc.gcInv (toGenConf conf) (toGenState conf state) majorHeap majorRoots) :
    (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1).filter isForwardPointer = [] := by
  obtain ⟨_, _, old, current, refs, segment, _⟩ := original
  obtain ⟨oldEq, refsSimilar⟩ := partialGc_regions conf roots roots1 heap old current refs state segment run
  obtain ⟨whole, _, _, _⟩ := heapSegment_imp heap conf.genStart conf.refsStart old current refs segment
  have noForward : ∀ element ∈ heap, isForwardPointer element = false := by
    intro element member
    cases flag : isForwardPointer element with
    | false => rfl
    | true =>
      have inFilter : element ∈ heap.filter isForwardPointer := by simp [member, flag]
      rw [valid.2.1] at inFilter
      simp at inFilter
  have oldClean : old.filter isForwardPointer = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro element member
    have inHeap : element ∈ heap := by rw [← whole]; simp [member]
    simp [noForward element inHeap]
  have refsClean : refs.filter isForwardPointer = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro element member
    have inHeap : element ∈ heap := by rw [← whole]; simp [member]
    simp [noForward element inHeap]
  have outputRefsClean := similarData_noForward conf refs state.r1 refsSimilar refsClean
  have copiedData := majorInv.2.2.2.2.2.2.2.1
  have copiedClean : state.h1.filter isForwardPointer = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro element member
    have translatedMember : toGenHeapElement conf element ∈ (toGenState conf state).h1 := by
      change toGenHeapElement conf element ∈ state.h1.map (toGenHeapElement conf)
      exact List.mem_map.mpr ⟨element, member, rfl⟩
    have data := copiedData _ translatedMember
    cases element <;> simp [toGenHeapElement, isDataElement, isForwardPointer] at data ⊢
  have freeClean : (heapExpand state.n : List (HeapElement α β)).filter isForwardPointer = [] := by
    cases state.n <;> simp [heapExpand, isForwardPointer]
  simp [List.filter_append, oldEq, oldClean, copiedClean, freeClean, outputRefsClean]

/-- Flapjack proof infrastructure: every pointer in an unchanged old-region
object still points to data in the reconstructed output heap. -/
theorem partialGc_oldPointersValid {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (heap : List (HeapElement α β)) (state : GcState α β)
    (run : partialGc conf (roots, heap) = (roots1, state)) (original : genInv conf heap)
    (valid : heapOk heap conf.limit) (invariant : simInv conf heap state) (empty : state.h2 = [])
    (children : List (HeapAddress α)) (len : Nat) (data : β) (ptr : Nat) (value : α)
    (object : .dataElement children len data ∈ state.old) (child : .pointer ptr value ∈ children) :
    isSomeDataElement (heapLookup ptr (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1)) := by
  have originalCopy := original
  obtain ⟨_, _, old, current, refs, segment, _, _, _, _, _, oldPointers⟩ := originalCopy
  have oldEq := (partialGc_regions conf roots roots1 heap old current refs state segment run).1
  have oldObject : .dataElement children len data ∈ old := by simpa [oldEq] using object
  have outside := oldPointers children len data ptr value ⟨oldObject, child⟩
  obtain ⟨whole, _, _, _⟩ := heapSegment_imp heap conf.genStart conf.refsStart old current refs segment
  have inHeap : .dataElement children len data ∈ heap := by rw [← whole]; simp [oldObject]
  obtain ⟨targetChildren, targetLen, targetData, targetFound⟩ := valid.2.2 children len data ptr value ⟨inHeap, child⟩
  rcases outside with before | after
  · have output := heapLookup_old conf roots roots1 heap state ptr
      (state.h1 ++ heapExpand state.n ++ state.r1) targetChildren targetLen targetData run original targetFound before
    exact ⟨targetChildren, targetLen, targetData, by simpa [List.append_assoc] using output⟩
  · have boundary := partialGc_outputPrefixLength conf roots roots1 heap state run original invariant empty
    obtain ⟨resultChildren, resultFound⟩ :=
      heapLookup_refs conf roots roots1 heap state ptr targetChildren targetLen targetData run original targetFound boundary after
    exact ⟨resultChildren, targetLen, targetData, resultFound⟩

/-- Flapjack proof infrastructure: a data lookup in the translated copied
region gives a data lookup at the corresponding offset in the full output. -/
theorem translatedCopiedData_inOutput {α β γ : Type} (conf : Config γ)
    (old copied refs : List (HeapElement α β)) (free ptr : Nat)
    (oldLength : heapLength old = conf.genStart)
    (found : isSomeDataElement (heapLookup ptr (toGenHeapList conf copied ++ heapExpand free))) :
    isSomeDataElement (heapLookup (conf.genStart + ptr) (old ++ copied ++ heapExpand free ++ refs)) := by
  have translated : toGenHeapList conf (copied ++ heapExpand free) =
      toGenHeapList conf copied ++ heapExpand free := by
    simp only [toGenHeapList, List.map_append]
    change _ ++ toGenHeapList conf (heapExpand free : List (HeapElement α β)) = _
    rw [toGenHeapList_heapExpand]
  rw [← translated] at found
  have source := (isSomeDataElement_toGenHeapList conf (copied ++ heapExpand free) ptr).mp found
  obtain ⟨children, len, payload, sourceFound⟩ := source
  have bound := heapLookup_less (copied ++ heapExpand free) ptr _ sourceFound
  refine ⟨children, len, payload, ?_⟩
  rw [List.append_assoc, List.append_assoc, GenGc.heapLookup_append, oldLength]
  simp only [Nat.not_lt.mpr (by omega : conf.genStart ≤ conf.genStart + ptr), if_false, Nat.add_sub_cancel_left]
  rw [← List.append_assoc copied (heapExpand free) refs]
  rw [GenGc.heapLookup_append, if_pos bound]
  exact sourceFound

/-- Flapjack proof infrastructure: copied objects have valid child pointers
when the corresponding major-collector output heap is valid. -/
theorem partialGc_copiedPointersValid {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (heap : List (HeapElement α β)) (state : GcState α β)
    (run : partialGc conf (roots, heap) = (roots1, state)) (original : genInv conf heap)
    (valid : heapOk heap conf.limit) (invariant : simInv conf heap state) (empty : state.h2 = [])
    (majorValid : heapOk (toGenHeapList conf state.h1 ++ heapExpand state.n) (toGenConf conf).limit)
    (children : List (HeapAddress α)) (len : Nat) (data : β) (ptr : Nat) (value : α)
    (object : .dataElement children len data ∈ state.h1) (child : .pointer ptr value ∈ children) :
    isSomeDataElement (heapLookup ptr (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1)) := by
  by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
  · apply partialGc_protectedPointersValid conf roots roots1 heap state run original valid invariant empty ptr
    exact ⟨children, len, data, value, by simp [object], child, outside⟩
  · have lower : conf.genStart ≤ ptr := by omega
    have upper : ptr < conf.refsStart := by omega
    have translatedObject : .dataElement (children.map (toGenHeapAddress conf)) len data ∈
        toGenHeapList conf state.h1 ++ heapExpand state.n := by
      apply List.mem_append.mpr
      left
      change .dataElement (children.map (toGenHeapAddress conf)) len data ∈
        state.h1.map (toGenHeapElement conf)
      exact List.mem_map.mpr ⟨.dataElement children len data, object, rfl⟩
    have translatedChild : .pointer (ptr - conf.genStart) (.real value) ∈ children.map (toGenHeapAddress conf) := by
      apply List.mem_map.mpr
      refine ⟨.pointer ptr value, child, ?_⟩
      simp [toGenHeapAddress, Nat.not_lt.mpr lower, Nat.not_le.mpr upper]
    have target := majorValid.2.2 (children.map (toGenHeapAddress conf)) len data
      (ptr - conf.genStart) (.real value) ⟨translatedObject, translatedChild⟩
    have originalCopy := original
    obtain ⟨_, _, old, current, refs, segment, _⟩ := originalCopy
    have oldEq := (partialGc_regions conf roots roots1 heap old current refs state segment run).1
    have oldLen := (heapSegment_imp heap conf.genStart conf.refsStart old current refs segment).2.1
    have result := translatedCopiedData_inOutput conf state.old state.h1 state.r1 state.n
      (ptr - conf.genStart) ((congrArg heapLength oldEq).trans oldLen) target
    simpa [Nat.add_sub_of_le lower] using result

/-- Flapjack proof infrastructure: children of a reference object occur in
the flattened translated roots. -/
theorem refsToRoots_child {α β γ : Type} (conf : Config γ)
    (refs : List (HeapElement α β)) (children : List (HeapAddress α)) (len : Nat) (data : β)
    (root : HeapAddress α) (object : .dataElement children len data ∈ refs) (child : root ∈ children) :
    toGenHeapAddress conf root ∈ refsToRoots conf refs := by
  induction refs with
  | nil => simp at object
  | cons head tail ih =>
    simp only [List.mem_cons] at object
    rcases object with equal | member
    · subst head
      simp only [refsToRoots, List.mem_append]
      left
      exact List.mem_map.mpr ⟨root, child, rfl⟩
    · have tailMember := ih member
      cases head <;> simp [refsToRoots, tailMember]

/-- Flapjack proof infrastructure: remembered reference objects have valid
children when the translated reference roots are valid. -/
theorem partialGc_referencePointersValid {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (heap : List (HeapElement α β)) (state : GcState α β)
    (run : partialGc conf (roots, heap) = (roots1, state)) (original : genInv conf heap)
    (valid : heapOk heap conf.limit) (invariant : simInv conf heap state) (empty : state.h2 = [])
    (majorRootsValid : rootsOk (refsToRoots conf state.r1) (toGenHeapList conf state.h1 ++ heapExpand state.n))
    (children : List (HeapAddress α)) (len : Nat) (data : β) (ptr : Nat) (value : α)
    (object : .dataElement children len data ∈ state.r1) (child : .pointer ptr value ∈ children) :
    isSomeDataElement (heapLookup ptr (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1)) := by
  by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
  · apply partialGc_protectedPointersValid conf roots roots1 heap state run original valid invariant empty ptr
    exact ⟨children, len, data, value, by simp [object], child, outside⟩
  · have lower : conf.genStart ≤ ptr := by omega
    have upper : ptr < conf.refsStart := by omega
    have translatedChild := refsToRoots_child conf state.r1 children len data (.pointer ptr value) object child
    have translatedPointer : .pointer (ptr - conf.genStart) (.real value) ∈ refsToRoots conf state.r1 := by
      simpa [toGenHeapAddress, Nat.not_lt.mpr lower, Nat.not_le.mpr upper] using translatedChild
    have target := majorRootsValid (ptr - conf.genStart) (.real value) translatedPointer
    have originalCopy := original
    obtain ⟨_, _, old, current, refs, segment, _⟩ := originalCopy
    have oldEq := (partialGc_regions conf roots roots1 heap old current refs state segment run).1
    have oldLen := (heapSegment_imp heap conf.genStart conf.refsStart old current refs segment).2.1
    have result := translatedCopiedData_inOutput conf state.old state.h1 state.r1 state.n
      (ptr - conf.genStart) ((congrArg heapLength oldEq).trans oldLen) target
    simpa [Nat.add_sub_of_le lower] using result

/-- Flapjack proof infrastructure: the major collector's final heap and roots
establish validity of the complete reconstructed partial-collector heap. -/
theorem partialGc_outputHeapOk {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (heap : List (HeapElement α β)) (state : GcState α β)
    (majorHeap : List (HeapElement (DataSort (HeapAddress α) α) β))
    (majorRoots : List (HeapAddress (DataSort (HeapAddress α) α)))
    (run : partialGc conf (roots, heap) = (roots1, state)) (original : genInv conf heap)
    (valid : heapOk heap conf.limit) (invariant : simInv conf heap state) (empty : state.h2 = [])
    (majorInv : GenGc.gcInv (toGenConf conf) (toGenState conf state) majorHeap majorRoots)
    (majorValid : heapOk (toGenHeapList conf state.h1 ++ heapExpand state.n) (toGenConf conf).limit)
    (majorRootsValid : rootsOk (refsToRoots conf state.r1) (toGenHeapList conf state.h1 ++ heapExpand state.n)) :
    heapOk (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1) conf.limit := by
  refine ⟨partialGc_outputLength conf roots roots1 heap state run original valid invariant empty,
    partialGc_outputNoForward conf roots roots1 heap state majorHeap majorRoots run original valid majorInv, ?_⟩
  intro children len data ptr value ⟨object, child⟩
  simp only [List.mem_append] at object
  rcases object with ((inOld | inCopied) | inFree) | inRefs
  · exact partialGc_oldPointersValid conf roots roots1 heap state run original valid invariant empty
      children len data ptr value inOld child
  · exact partialGc_copiedPointersValid conf roots roots1 heap state run original valid invariant empty
      majorValid children len data ptr value inCopied child
  · cases freeEq : state.n <;> simp [heapExpand, freeEq] at inFree
  · exact partialGc_referencePointersValid conf roots roots1 heap state run original valid invariant empty
      majorRootsValid children len data ptr value inRefs child

/-- Flapjack proof infrastructure: partial collection of valid input produces
a successful result whose reconstructed heap is valid. -/
theorem partialGc_outputWellFormed {α β : Type} (conf : Config β)
    (roots : List (HeapAddress α)) (heap : List (HeapElement α β))
    (validRoots : rootsOk roots heap) (validHeap : heapOk heap conf.limit)
    (generations : heapGenOk heap conf) :
    ∃ (roots1 : List (HeapAddress α)) (state : GcState α β),
      partialGc conf (roots, heap) = (roots1, state) ∧ state.ok = true ∧
      heapOk (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1) conf.limit := by
  have original := heapGenOk_genInv conf heap validHeap generations
  have originalCopy := original
  obtain ⟨lower, upper, old, current, refs, segment, oldNonrefs, currentNonrefs, refData, _⟩ := originalCopy
  have nonrefs : List.Forall (fun e => heapElementIsRef conf e = false) (old ++ current) :=
    List.forall_append.mpr ⟨oldNonrefs, currentNonrefs⟩
  have translatedRoots := rootsOk_simulation conf roots heap old current refs validRoots validHeap segment lower
  have translatedHeap := heapOk_simulation conf heap old current refs validHeap segment lower upper
  obtain ⟨majorRoots1, majorState, majorRun, majorOk, _, finalRoots, finalHeap, _⟩ :=
    GenGc.genGc_abstract_structure (toGenConf conf) (toGenRoots conf roots ++ refsToRoots conf refs)
      (toGenHeapList conf current) translatedRoots translatedHeap
  obtain ⟨majorState1, invariantRun, _, majorInv, _⟩ :=
    GenGc.genGc_invariant (toGenConf conf) (toGenRoots conf roots ++ refsToRoots conf refs)
      (toGenHeapList conf current) translatedRoots translatedHeap
  rw [majorRun] at invariantRun
  have stateEq := (Prod.mk.inj invariantRun).2
  subst majorState1
  cases partialRun : partialGc conf (roots, heap) with
  | mk roots1 state =>
    obtain ⟨rootsEq, majorStateEq, invariant, empty, ok⟩ :=
      partialGc_simulation conf roots roots1 heap old current refs state majorRoots1 majorState
        partialRun generations ⟨lower, upper⟩ segment nonrefs refData validRoots majorRun validHeap majorOk
    subst majorState
    have majorValid : heapOk (toGenHeapList conf state.h1 ++ heapExpand state.n) (toGenConf conf).limit := by
      simpa [toGenState, emptyGcState] using finalHeap
    have refsValid : rootsOk (refsToRoots conf state.r1) (toGenHeapList conf state.h1 ++ heapExpand state.n) := by
      intro ptr value member
      have inRoots : .pointer ptr value ∈ majorRoots1 := by
        rw [rootsEq]
        exact List.mem_append.mpr (Or.inr member)
      simpa [toGenState, emptyGcState] using finalRoots ptr value inRoots
    have output := partialGc_outputHeapOk conf roots roots1 heap state (toGenHeapList conf current)
      (toGenRoots conf roots ++ refsToRoots conf refs) partialRun original validHeap invariant empty majorInv majorValid refsValid
    exact ⟨roots1, state, rfl, ok, output⟩

/-- Flapjack proof infrastructure: a major-collector source-map entry denotes
a data object at the corresponding address in the original full heap. -/
theorem majorMap_sourceData {α β γ : Type} (conf : Config γ)
    (heap old current refs : List (HeapElement α β)) (f : HolFiniteMapExact Nat Nat)
    (segment : heapSegment (conf.genStart, conf.refsStart) heap = some (old, current, refs))
    (majorSource : ∀ i, f.lookup i ≠ none →
      isSomeDataElement (heapLookup i (toGenHeapList conf current))) :
    ∀ i, f.lookup i ≠ none → isSomeDataElement (heapLookup (i + conf.genStart) heap) := by
  obtain ⟨whole, oldLen, _, _⟩ := heapSegment_imp heap conf.genStart conf.refsStart old current refs segment
  intro i defined
  have translated := majorSource i defined
  obtain ⟨children, len, payload, found⟩ := (isSomeDataElement_toGenHeapList conf current i).mp translated
  have bound := heapLookup_less current i _ found
  refine ⟨children, len, payload, ?_⟩
  rw [← whole, List.append_assoc, GenGc.heapLookup_append, oldLen]
  simp only [Nat.not_lt.mpr (by omega : conf.genStart ≤ i + conf.genStart), if_false,
    Nat.add_sub_cancel_right]
  rw [GenGc.heapLookup_append, if_pos bound]
  exact found

/-- Flapjack proof infrastructure: every defined combined-map source is a
data object in the original heap. -/
theorem newForwardMap_sourceData {α β γ : Type} (conf : Config γ)
    (heap : List (HeapElement α β)) (f : HolFiniteMapExact Nat Nat)
    (valid : ∀ i, f.lookup i ≠ none → isSomeDataElement (heapLookup (i + conf.genStart) heap)) :
    ∀ ptr, (newForwardMap f conf heap).lookup ptr ≠ none → isSomeDataElement (heapLookup ptr heap) := by
  intro ptr defined
  have domain := (newForwardMap_domain f conf heap ptr valid).mp defined
  by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
  · simpa [outside] using domain
  · simp only [outside, ↓reduceIte] at domain
    obtain ⟨i, member, rfl⟩ := domain
    simpa [Nat.add_comm] using valid i member

/-- Flapjack proof infrastructure: current-generation entries in the
combined map use a defined major-map entry and remain in the generation. -/
theorem newForwardMap_currentBounds {α β γ : Type} (conf : Config γ)
    (heap : List (HeapElement α β)) (f : HolFiniteMapExact Nat Nat) (ptr : Nat)
    (lower : conf.genStart ≤ ptr) (upper : ptr < conf.refsStart)
    (defined : (newForwardMap f conf heap).lookup ptr ≠ none)
    (targetBounds : ∀ i, f.lookup i ≠ none → holFapply f i < conf.refsStart - conf.genStart) :
    f.lookup (ptr - conf.genStart) ≠ none ∧
      conf.genStart ≤ holFapply (newForwardMap f conf heap) ptr ∧
      holFapply (newForwardMap f conf heap) ptr < conf.refsStart := by
  have lookup := newForwardMap_current f conf heap ptr lower upper
  cases found : f.lookup (ptr - conf.genStart) with
  | none => simp [found] at lookup; exact False.elim (defined lookup)
  | some value =>
    have majorDefined : f.lookup (ptr - conf.genStart) ≠ none := by simp [found]
    have target := targetBounds (ptr - conf.genStart) majorDefined
    have mapEq : (newForwardMap f conf heap).lookup ptr = some (conf.genStart + value) := by
      simpa [found] using lookup
    have majorEq := holFapply_of_lookup found
    have partialEq := holFapply_of_lookup mapEq
    rw [majorEq] at target
    refine ⟨by simp, ?_, ?_⟩ <;> rw [partialEq] <;> omega

/-- Flapjack proof infrastructure: combining an injective major forwarding
map with identity outside the generation yields an injective map. -/
theorem newForwardMap_injective {α β γ : Type} (conf : Config γ)
    (heap : List (HeapElement α β)) (f : HolFiniteMapExact Nat Nat)
    (valid : ∀ i, f.lookup i ≠ none → isSomeDataElement (heapLookup (i + conf.genStart) heap))
    (targetBounds : ∀ i, f.lookup i ≠ none → holFapply f i < conf.refsStart - conf.genStart)
    (injective : ∀ i j, f.lookup i ≠ none → f.lookup j ≠ none → holFapply f i = holFapply f j → i = j) :
    ∀ i j, (newForwardMap f conf heap).lookup i ≠ none → (newForwardMap f conf heap).lookup j ≠ none →
      holFapply (newForwardMap f conf heap) i = holFapply (newForwardMap f conf heap) j → i = j := by
  intro i j iDefined jDefined equal
  have iApply := newForwardMap_apply f conf heap i iDefined valid
  have jApply := newForwardMap_apply f conf heap j jDefined valid
  by_cases iOutside : i < conf.genStart ∨ conf.refsStart ≤ i
  · simp only [iOutside, ↓reduceIte] at iApply
    by_cases jOutside : j < conf.genStart ∨ conf.refsStart ≤ j
    · simp only [jOutside, ↓reduceIte] at jApply
      omega
    · have jLower : conf.genStart ≤ j := by omega
      have jUpper : j < conf.refsStart := by omega
      obtain ⟨_, lo, hi⟩ := newForwardMap_currentBounds conf heap f j jLower jUpper jDefined targetBounds
      omega
  · have iLower : conf.genStart ≤ i := by omega
    have iUpper : i < conf.refsStart := by omega
    obtain ⟨iMajor, ilo, ihi⟩ := newForwardMap_currentBounds conf heap f i iLower iUpper iDefined targetBounds
    by_cases jOutside : j < conf.genStart ∨ conf.refsStart ≤ j
    · simp only [jOutside, ↓reduceIte] at jApply
      omega
    · have jLower : conf.genStart ≤ j := by omega
      have jUpper : j < conf.refsStart := by omega
      obtain ⟨jMajor, _, _⟩ := newForwardMap_currentBounds conf heap f j jLower jUpper jDefined targetBounds
      simp only [iOutside, ↓reduceIte] at iApply
      simp only [jOutside, ↓reduceIte] at jApply
      have fEqual : holFapply f (i - conf.genStart) = holFapply f (j - conf.genStart) := by omega
      have indices := injective (i - conf.genStart) (j - conf.genStart) iMajor jMajor fEqual
      omega

/-- Flapjack proof infrastructure: major forwarding-map targets lie within
the current generation of the reconstructed partial-collector heap. -/
theorem majorMap_targetBounds {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (heap : List (HeapElement α β)) (state : GcState α β)
    (majorHeap : List (HeapElement (DataSort (HeapAddress α) α) β)) (f : HolFiniteMapExact Nat Nat)
    (run : partialGc conf (roots, heap) = (roots1, state)) (original : genInv conf heap)
    (invariant : simInv conf heap state) (empty : state.h2 = [])
    (related : gcRelated f majorHeap (toGenHeapList conf state.h1 ++ heapExpand state.n)) :
    ∀ i, f.lookup i ≠ none → holFapply f i < conf.refsStart - conf.genStart := by
  have boundary := partialGc_outputPrefixLength conf roots roots1 heap state run original invariant empty
  have originalCopy := original
  obtain ⟨lower, _, old, current, refs, segment, _⟩ := originalCopy
  have oldEq := (partialGc_regions conf roots roots1 heap old current refs state segment run).1
  have oldLen := (heapSegment_imp heap conf.genStart conf.refsStart old current refs segment).2.1
  have translatedLength : heapLength (toGenHeapList conf state.h1 ++ heapExpand state.n) =
      conf.refsStart - conf.genStart := by
    simp only [heapLength_append, heapLength_toGenHeapList, heapLength_heapExpand, oldEq, oldLen] at boundary ⊢
    omega
  intro i defined
  obtain ⟨children, len, data, found⟩ := related.1 i defined
  have bound := heapLookup_less (toGenHeapList conf state.h1 ++ heapExpand state.n) (holFapply f i) _ found
  simpa [translatedLength] using bound

/-- Flapjack proof infrastructure: the combined map derived from a valid
major relation is injective and is defined only on original data objects. -/
theorem partialGc_combinedMapProperties {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (heap old current refs : List (HeapElement α β))
    (state : GcState α β) (f : HolFiniteMapExact Nat Nat)
    (run : partialGc conf (roots, heap) = (roots1, state)) (original : genInv conf heap)
    (invariant : simInv conf heap state) (empty : state.h2 = [])
    (segment : heapSegment (conf.genStart, conf.refsStart) heap = some (old, current, refs))
    (related : gcRelated f (toGenHeapList conf current) (toGenHeapList conf state.h1 ++ heapExpand state.n)) :
    (∀ i j, (newForwardMap f conf heap).lookup i ≠ none → (newForwardMap f conf heap).lookup j ≠ none →
      holFapply (newForwardMap f conf heap) i = holFapply (newForwardMap f conf heap) j → i = j) ∧
    (∀ i, (newForwardMap f conf heap).lookup i ≠ none → isSomeDataElement (heapLookup i heap)) := by
  have source := majorMap_sourceData conf heap old current refs f segment related.2.2.1
  have targets := majorMap_targetBounds conf roots roots1 heap state (toGenHeapList conf current) f
    run original invariant empty related
  exact ⟨newForwardMap_injective conf heap f source targets related.2.1,
    newForwardMap_sourceData conf heap f source⟩

/-- Flapjack proof infrastructure: each defined combined-map entry points to
a data object in the reconstructed partial-collector output heap. -/
theorem partialGc_combinedMapTargetData {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (heap old current refs : List (HeapElement α β))
    (state : GcState α β) (f : HolFiniteMapExact Nat Nat)
    (run : partialGc conf (roots, heap) = (roots1, state)) (original : genInv conf heap)
    (invariant : simInv conf heap state) (empty : state.h2 = [])
    (segment : heapSegment (conf.genStart, conf.refsStart) heap = some (old, current, refs))
    (related : gcRelated f (toGenHeapList conf current) (toGenHeapList conf state.h1 ++ heapExpand state.n)) :
    ∀ i, (newForwardMap f conf heap).lookup i ≠ none →
      isSomeDataElement (heapLookup (holFapply (newForwardMap f conf heap) i)
        (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1)) := by
  have source := majorMap_sourceData conf heap old current refs f segment related.2.2.1
  have targets := majorMap_targetBounds conf roots roots1 heap state (toGenHeapList conf current) f
    run original invariant empty related
  have boundary := partialGc_outputPrefixLength conf roots roots1 heap state run original invariant empty
  have oldEq := (partialGc_regions conf roots roots1 heap old current refs state segment run).1
  have oldLen := (heapSegment_imp heap conf.genStart conf.refsStart old current refs segment).2.1
  intro i defined
  have mapEq := newForwardMap_apply f conf heap i defined source
  by_cases outside : i < conf.genStart ∨ conf.refsStart ≤ i
  · simp only [outside, ↓reduceIte] at mapEq
    rw [mapEq]
    obtain ⟨children, len, data, found⟩ := newForwardMap_sourceData conf heap f source i defined
    rcases outside with before | after
    · have output := heapLookup_old conf roots roots1 heap state i (state.h1 ++ heapExpand state.n ++ state.r1)
        children len data run original found before
      exact ⟨children, len, data, by simpa [List.append_assoc] using output⟩
    · obtain ⟨children1, result⟩ :=
        heapLookup_refs conf roots roots1 heap state i children len data run original found boundary after
      exact ⟨children1, len, data, result⟩
  · have lower : conf.genStart ≤ i := by omega
    have upper : i < conf.refsStart := by omega
    simp only [outside, ↓reduceIte] at mapEq
    obtain ⟨majorDefined, _, _⟩ := newForwardMap_currentBounds conf heap f i lower upper defined targets
    have majorTarget := related.1 (i - conf.genStart) majorDefined
    have output := translatedCopiedData_inOutput conf state.old state.h1 state.r1 state.n
      (holFapply f (i - conf.genStart)) ((congrArg heapLength oldEq).trans oldLen) majorTarget
    simpa [mapEq] using output

/-- Flapjack proof infrastructure: valid child pointers are defined in the
combined map when their current-generation translations are in the major map. -/
theorem newForwardMap_childrenDefined {α β γ : Type} (conf : Config γ)
    (heap : List (HeapElement α β)) (children : List (HeapAddress α)) (f : HolFiniteMapExact Nat Nat)
    (valid : rootsOk children heap)
    (majorDomain : ∀ ptr value, .pointer ptr value ∈ toGenRoots conf children → f.lookup ptr ≠ none) :
    ∀ ptr value, .pointer ptr value ∈ children → (newForwardMap f conf heap).lookup ptr ≠ none := by
  intro ptr value child
  by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
  · have old : ptr ∈ fOldPtrs conf heap := ⟨valid ptr value child, outside⟩
    simp [newForwardMap_old f conf heap ptr old]
  · have lower : conf.genStart ≤ ptr := by omega
    have upper : ptr < conf.refsStart := by omega
    have translated : .pointer (ptr - conf.genStart) (.real value) ∈ toGenRoots conf children := by
      apply List.mem_map.mpr
      refine ⟨.pointer ptr value, child, ?_⟩
      simp [toGenHeapAddress, Nat.not_lt.mpr lower, Nat.not_le.mpr upper]
    have defined := majorDomain (ptr - conf.genStart) (.real value) translated
    rw [newForwardMap_current f conf heap ptr lower upper]
    cases lookup : f.lookup (ptr - conf.genStart) with
    | none => exact False.elim (defined lookup)
    | some value => simp

/-- Flapjack proof infrastructure: the object-and-children clause of the
combined heap relation holds for an original current-generation object. -/
theorem partialGc_currentObjectRelated {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (heap old current refs : List (HeapElement α β))
    (state : GcState α β) (f : HolFiniteMapExact Nat Nat)
    (run : partialGc conf (roots, heap) = (roots1, state)) (original : genInv conf heap)
    (valid : heapOk heap conf.limit) (invariant : simInv conf heap state) (empty : state.h2 = [])
    (segment : heapSegment (conf.genStart, conf.refsStart) heap = some (old, current, refs))
    (related : gcRelated f (toGenHeapList conf current) (toGenHeapList conf state.h1 ++ heapExpand state.n))
    (ptr : Nat) (children : List (HeapAddress α)) (len : Nat) (data : β)
    (defined : (newForwardMap f conf heap).lookup ptr ≠ none)
    (found : heapLookup ptr heap = some (.dataElement children len data))
    (lower : conf.genStart ≤ ptr) (upper : ptr < conf.refsStart) :
    heapLookup (holFapply (newForwardMap f conf heap) ptr)
        (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1) =
      some (.dataElement (addrMap (holFapply (newForwardMap f conf heap)) children) len data) ∧
    ∀ p value, .pointer p value ∈ children → (newForwardMap f conf heap).lookup p ≠ none := by
  have source := majorMap_sourceData conf heap old current refs f segment related.2.2.1
  have targets := majorMap_targetBounds conf roots roots1 heap state (toGenHeapList conf current) f
    run original invariant empty related
  obtain ⟨majorDefined, _, _⟩ := newForwardMap_currentBounds conf heap f ptr lower upper defined targets
  have translatedLookup := heapLookup_toGenHeap conf heap old current refs ptr segment lower upper
  have majorFound : heapLookup (ptr - conf.genStart) (toGenHeapList conf current) =
      some (.dataElement (children.map (toGenHeapAddress conf)) len data) := by
    simpa [toGenHeap, heapRestrict, segment, found, toGenHeapElement] using translatedLookup
  obtain ⟨majorTarget, majorChildren⟩ := related.2.2.2 (ptr - conf.genStart)
    (children.map (toGenHeapAddress conf)) len data majorDefined majorFound
  have childrenValid : rootsOk children heap := by
    intro p value child
    exact valid.2.2 children len data p value ⟨heapLookup_mem heap ptr _ found, child⟩
  have childrenDomain : ∀ p value, .pointer p value ∈ toGenRoots conf children → f.lookup p ≠ none := majorChildren
  have target := heapLookup_forwardedData conf heap state.h1 state.r1 state.n
    (holFapply f (ptr - conf.genStart)) children len data f majorTarget childrenValid childrenDomain
  have oldEq := (partialGc_regions conf roots roots1 heap old current refs state segment run).1
  have oldLen := (heapSegment_imp heap conf.genStart conf.refsStart old current refs segment).2.1
  have mapping := newForwardMap_apply f conf heap ptr defined source
  simp only [Nat.not_lt.mpr lower, Nat.not_le.mpr upper, or_self, ↓reduceIte] at mapping
  refine ⟨?_, newForwardMap_childrenDefined conf heap children f childrenValid childrenDomain⟩
  rw [mapping, List.append_assoc, List.append_assoc, GenGc.heapLookup_append, oldEq, oldLen]
  simp only [Nat.not_lt.mpr (by omega : conf.genStart ≤ conf.genStart + holFapply f (ptr - conf.genStart)),
    if_false, Nat.add_sub_cancel_left]
  simpa [List.append_assoc] using target

/-- Flapjack proof infrastructure: an address map that fixes every pointer
in a root list leaves that list unchanged. -/
theorem addrMap_eq_self {α : Type} (rename : Nat → Nat) (roots : List (HeapAddress α))
    (fixed : ∀ ptr value, .pointer ptr value ∈ roots → rename ptr = ptr) : addrMap rename roots = roots := by
  induction roots with
  | nil => rfl
  | cons head tail ih =>
    have tailFixed : ∀ ptr value, .pointer ptr value ∈ tail → rename ptr = ptr := by
      intro ptr value member
      exact fixed ptr value (by simp [member])
    cases head with
    | data value => simp [addrMap, ih tailFixed]
    | pointer ptr value =>
      have headFixed := fixed ptr value (by simp)
      simp [addrMap, headFixed, ih tailFixed]

/-- Flapjack proof infrastructure: the object-and-children clause of the
combined heap relation holds for an original old-generation object. -/
theorem partialGc_oldObjectRelated {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (heap : List (HeapElement α β)) (state : GcState α β)
    (f : HolFiniteMapExact Nat Nat)
    (run : partialGc conf (roots, heap) = (roots1, state)) (original : genInv conf heap)
    (valid : heapOk heap conf.limit)
    (ptr : Nat) (children : List (HeapAddress α)) (len : Nat) (data : β)
    (found : heapLookup ptr heap = some (.dataElement children len data)) (before : ptr < conf.genStart) :
    heapLookup (holFapply (newForwardMap f conf heap) ptr)
        (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1) =
      some (.dataElement (addrMap (holFapply (newForwardMap f conf heap)) children) len data) ∧
    ∀ p value, .pointer p value ∈ children → (newForwardMap f conf heap).lookup p ≠ none := by
  have originalCopy := original
  obtain ⟨_, _, old, current, refs, segment, _, _, _, _, _, oldPointers⟩ := originalCopy
  obtain ⟨whole, oldLen, _, _⟩ := heapSegment_imp heap conf.genStart conf.refsStart old current refs segment
  have foundOld : heapLookup ptr old = some (.dataElement children len data) := by
    rw [← whole, List.append_assoc, GenGc.heapLookup_append, oldLen, if_pos before] at found
    exact found
  have object := heapLookup_mem old ptr _ foundOld
  have each : ∀ p value, .pointer p value ∈ children →
      (newForwardMap f conf heap).lookup p = some p := by
    intro p value child
    have outside := oldPointers children len data p value ⟨object, child⟩
    have inHeap : .dataElement children len data ∈ heap := by rw [← whole]; simp [object]
    have pointerData := valid.2.2 children len data p value ⟨inHeap, child⟩
    exact newForwardMap_old f conf heap p ⟨pointerData, outside⟩
  have rootMap := newForwardMap_old f conf heap ptr ⟨⟨children, len, data, found⟩, Or.inl before⟩
  have childrenEq : addrMap (holFapply (newForwardMap f conf heap)) children = children := by
    apply addrMap_eq_self
    intro p value child
    exact holFapply_of_lookup (each p value child)
  refine ⟨?_, ?_⟩
  · rw [holFapply_of_lookup rootMap, childrenEq]
    have output := heapLookup_old conf roots roots1 heap state ptr (state.h1 ++ heapExpand state.n ++ state.r1)
      children len data run original found before
    simpa [List.append_assoc] using output
  · intro p value child
    rw [each p value child]
    simp

/-- Flapjack proof infrastructure: the object-and-children clause holds for
an original reference-region object when the major reference roots match. -/
theorem partialGc_refObjectRelated {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (heap old current refs : List (HeapElement α β))
    (state : GcState α β) (f : HolFiniteMapExact Nat Nat)
    (run : partialGc conf (roots, heap) = (roots1, state)) (original : genInv conf heap)
    (valid : heapOk heap conf.limit) (invariant : simInv conf heap state) (empty : state.h2 = [])
    (segment : heapSegment (conf.genStart, conf.refsStart) heap = some (old, current, refs))
    (mappedRefs : addrMap (holFapply f) (refsToRoots conf refs) = refsToRoots conf state.r1)
    (majorDomain : ∀ p value, .pointer p value ∈ refsToRoots conf refs → f.lookup p ≠ none)
    (ptr : Nat) (children : List (HeapAddress α)) (len : Nat) (data : β)
    (found : heapLookup ptr heap = some (.dataElement children len data)) (after : conf.refsStart ≤ ptr) :
    heapLookup (holFapply (newForwardMap f conf heap) ptr)
        (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1) =
      some (.dataElement (addrMap (holFapply (newForwardMap f conf heap)) children) len data) ∧
    ∀ p value, .pointer p value ∈ children → (newForwardMap f conf heap).lookup p ≠ none := by
  obtain ⟨whole, _, endLen, _⟩ := heapSegment_imp heap conf.genStart conf.refsStart old current refs segment
  have refFound : heapLookup (ptr - conf.refsStart) refs = some (.dataElement children len data) := by
    rw [← whole, GenGc.heapLookup_append, endLen, if_neg (Nat.not_lt.mpr after)] at found
    exact found
  have refsSimilar := (partialGc_regions conf roots roots1 heap old current refs state segment run).2
  obtain ⟨children1, targetFound, mappedChildren⟩ :=
    heapLookup_similarData conf refs state.r1 (ptr - conf.refsStart) children len data f refsSimilar refFound mappedRefs
  have childrenValid : rootsOk children heap := by
    intro p value child
    have object : .dataElement children len data ∈ heap := by
      rw [← whole]
      simp [heapLookup_mem refs (ptr - conf.refsStart) _ refFound]
    exact valid.2.2 children len data p value ⟨object, child⟩
  have refObject := heapLookup_mem refs (ptr - conf.refsStart) _ refFound
  have childrenDomain : ∀ p value, .pointer p value ∈ toGenRoots conf children → f.lookup p ≠ none := by
    intro p value member
    obtain ⟨root, child, eq⟩ := List.mem_map.mp member
    have inRefs := refsToRoots_child conf refs children len data root refObject child
    rw [eq] at inRefs
    exact majorDomain p value inRefs
  have sameLength : children.length = children1.length := by
    have eq := congrArg List.length mappedChildren
    simpa [← addrMap_length] using eq
  have mapped : addrMap (holFapply f) (toGenRoots conf children) = toGenRoots conf children1 := mappedChildren
  obtain ⟨childrenEq, childrenDefined⟩ :=
    translatedRoots_forwarding conf heap f children children1 childrenValid childrenDomain mapped sameLength
  have rootMap := newForwardMap_old f conf heap ptr ⟨⟨children, len, data, found⟩, Or.inr after⟩
  have boundary := partialGc_outputPrefixLength conf roots roots1 heap state run original invariant empty
  refine ⟨?_, childrenDefined⟩
  rw [holFapply_of_lookup rootMap, GenGc.heapLookup_append, boundary, if_neg (Nat.not_lt.mpr after), ← childrenEq]
  exact targetFound

/-- Flapjack proof infrastructure: the major collector's heap relation and
reference-root correspondence induce the full partial-collector heap relation. -/
theorem partialGc_combinedMapRelated {α β : Type} (conf : Config β)
    (roots roots1 : List (HeapAddress α)) (heap old current refs : List (HeapElement α β))
    (state : GcState α β) (f : HolFiniteMapExact Nat Nat)
    (run : partialGc conf (roots, heap) = (roots1, state)) (original : genInv conf heap)
    (valid : heapOk heap conf.limit) (invariant : simInv conf heap state) (empty : state.h2 = [])
    (segment : heapSegment (conf.genStart, conf.refsStart) heap = some (old, current, refs))
    (related : gcRelated f (toGenHeapList conf current) (toGenHeapList conf state.h1 ++ heapExpand state.n))
    (mappedRefs : addrMap (holFapply f) (refsToRoots conf refs) = refsToRoots conf state.r1)
    (majorDomain : ∀ p value, .pointer p value ∈ refsToRoots conf refs → f.lookup p ≠ none) :
    gcRelated (newForwardMap f conf heap) heap (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1) := by
  obtain ⟨injective, source⟩ := partialGc_combinedMapProperties conf roots roots1 heap old current refs state f
    run original invariant empty segment related
  refine ⟨partialGc_combinedMapTargetData conf roots roots1 heap old current refs state f
    run original invariant empty segment related, injective, source, ?_⟩
  intro ptr children len data defined found
  by_cases before : ptr < conf.genStart
  · exact partialGc_oldObjectRelated conf roots roots1 heap state f run original valid ptr children len data found before
  · by_cases after : conf.refsStart ≤ ptr
    · exact partialGc_refObjectRelated conf roots roots1 heap old current refs state f run original valid invariant empty
        segment mappedRefs majorDomain ptr children len data found after
    · have lower : conf.genStart ≤ ptr := by omega
      have upper : ptr < conf.refsStart := by omega
      exact partialGc_currentObjectRelated conf roots roots1 heap old current refs state f run original valid invariant empty
        segment related ptr children len data defined found lower upper

/-- Partial collection preserves roots and heap through an existential
canonical finite-support forwarding map. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "partial_gc_related"
  (fmap_as_finite_support_relation := [f])]
theorem partialGc_related {α β : Type} (conf : Config β)
    (roots : List (HeapAddress α)) (heap : List (HeapElement α β))
    (validRoots : rootsOk roots heap) (validHeap : heapOk heap conf.limit)
    (generations : heapGenOk heap conf) :
    ∃ (state : GcState α β) (f : HolFiniteMapExact Nat Nat),
      partialGc conf (roots, heap) = (addrMap (holFapply f) roots, state) ∧
      (∀ ptr value, .pointer ptr value ∈ roots → f.lookup ptr ≠ none) ∧
      heapOk (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1) conf.limit ∧
      gcRelated f heap (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1) ∧ state.ok = true := by
  have original := heapGenOk_genInv conf heap validHeap generations
  have originalCopy := original
  obtain ⟨lower, upper, old, current, refs, segment, oldNonrefs, currentNonrefs, refData, _⟩ := originalCopy
  have nonrefs : List.Forall (fun e => heapElementIsRef conf e = false) (old ++ current) :=
    List.forall_append.mpr ⟨oldNonrefs, currentNonrefs⟩
  have translatedRoots := rootsOk_simulation conf roots heap old current refs validRoots validHeap segment lower
  have translatedHeap := heapOk_simulation conf heap old current refs validHeap segment lower upper
  obtain ⟨majorState, majorRun, majorDomain, majorInv, majorEmpty, majorR4, majorR3, majorR2⟩ :=
    GenGc.genGc_invariant (toGenConf conf) (toGenRoots conf roots ++ refsToRoots conf refs)
      (toGenHeapList conf current) translatedRoots translatedHeap
  have majorOk : majorState.ok = true := majorInv.2.2.2.2.1
  let f := heapMap 0 majorState.heap
  have majorRun' : GenGc.genGc (toGenConf conf)
      (toGenRoots conf roots ++ refsToRoots conf refs, toGenHeapList conf current) =
      (addrMap (holFapply f) (toGenRoots conf roots ++ refsToRoots conf refs), majorState) := by
    change GenGc.genGc (toGenConf conf)
      (toGenRoots conf roots ++ refsToRoots conf refs, toGenHeapList conf current) =
      (addrMap (holFapply (heapMap 0 majorState.heap)) (toGenRoots conf roots ++ refsToRoots conf refs), majorState) at majorRun
    exact majorRun
  cases partialRun : partialGc conf (roots, heap) with
  | mk roots1 state =>
    obtain ⟨rootsEq, majorStateEq, invariant, empty, ok⟩ :=
      partialGc_simulation conf roots roots1 heap old current refs state _ majorState partialRun generations
        ⟨lower, upper⟩ segment nonrefs refData validRoots majorRun' validHeap majorOk
    have length := partialGc_length conf roots roots1 heap state partialRun
    have split := addrMap_appendLength conf roots roots1 refs state.r1 f rootsEq length.symm
    have rootDomain : ∀ ptr value, .pointer ptr value ∈ toGenRoots conf roots → f.lookup ptr ≠ none := by
      intro ptr value member
      exact majorDomain ptr value (List.mem_append.mpr (Or.inl member))
    have refsDomain : ∀ ptr value, .pointer ptr value ∈ refsToRoots conf refs → f.lookup ptr ≠ none := by
      intro ptr value member
      exact majorDomain ptr value (List.mem_append.mpr (Or.inr member))
    obtain ⟨rootMapped, rootDefined⟩ :=
      translatedRoots_forwarding conf heap f roots roots1 validRoots rootDomain split.1 length.symm
    have majorRelated := GenGc.gcInv_final_related (toGenConf conf) majorState (toGenHeapList conf current)
      (toGenRoots conf roots ++ refsToRoots conf refs) majorInv majorEmpty majorR4 majorR3 majorR2
    have relation : gcRelated f (toGenHeapList conf current) (toGenHeapList conf state.h1 ++ heapExpand state.n) := by
      simpa [f, majorStateEq, toGenState, emptyGcState] using majorRelated
    have outputRelated := partialGc_combinedMapRelated conf roots roots1 heap old current refs state f
      partialRun original validHeap invariant empty segment relation split.2 refsDomain
    obtain ⟨wellRoots, wellState, wellRun, _, wellHeap⟩ :=
      partialGc_outputWellFormed conf roots heap validRoots validHeap generations
    rw [partialRun] at wellRun
    obtain ⟨_, stateEq⟩ := Prod.mk.inj wellRun
    subst wellState
    refine ⟨state, newForwardMap f conf heap, ?_, rootDefined, wellHeap, outputRelated, ok⟩
    simp [← rootMapped]

end Flapjack.Compiler.Backend.GenGcPartial
