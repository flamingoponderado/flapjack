import Flapjack.Compiler.Backend.GenGcPartial
import Flapjack.Compiler.Backend.GenGc
import Mathlib.Data.List.Basic
import Flapjack.Compiler.Backend.GcShared.Slice
import Flapjack.Compiler.Backend.GenGc.Proofs.HeapLookup
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

end Flapjack.Compiler.Backend.GenGcPartial
