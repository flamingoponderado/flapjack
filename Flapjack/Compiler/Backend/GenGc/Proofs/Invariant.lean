import Flapjack.Compiler.Backend.GenGc
import Flapjack.Compiler.Backend.GcShared.HeapSimilarity
import Flapjack.Compiler.Backend.GcShared.Reachability
import Flapjack.Compiler.Backend.GcShared.Related

/-! Abstract invariant for the major generational collector. -/
namespace Flapjack.Compiler.Backend.GenGc

/-- A copied location is final when it lies in the scanned data, scanned
reference, or completed reference region. -/
@[hol "cakeml/compiler/backend/gc/gen_gcScript.sml" "is_final_def"]
def isFinal {α β γ : Type} (_conf : γ) (state : GcState α β) (ptr : Nat) : Prop :=
  let dataEnd := heapLength state.h1
  let scannedStart := state.a + state.n + heapLength state.r4
  let scannedEnd := scannedStart + heapLength state.r3
  let finalStart := scannedEnd + heapLength state.r2
  ptr < dataEnd ∨ finalStart ≤ ptr ∨ (scannedStart ≤ ptr ∧ ptr < scannedEnd)

open Classical in
/-- Source-shaped major-collection invariant. Its internal forwarding map
uses the canonical finite-support representation; the declaration remains
untagged until that internal representation can be recorded and reviewed. -/
def gcInv {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α)) : Prop :=
  let copied := state.h1 ++ state.h2
  let references := state.r4 ++ state.r3 ++ state.r2 ++ state.r1
  let fullHeap := copied ++ heapExpand state.n ++ references
  let f := heapMap 0 state.heap
  let target := fun ptr => heapAddresses 0 copied ptr ∨ heapAddresses (state.a + state.n) references ptr
  heapLength copied = state.a ∧
  state.a + state.n + heapLength references = conf.limit ∧
  heapLength (state.heap.filter (fun h => !(isForwardPointer h))) = state.n ∧
  heapLength state.heap = conf.limit ∧ state.ok = true ∧
  heapOk heap0 conf.limit ∧ heapsSimilar heap0 state.heap ∧
  (∀ h ∈ state.h1, isDataElement h) ∧ (∀ h ∈ state.h2, isDataElement h) ∧
  (∀ h ∈ state.r1, isDataElement h) ∧ (∀ h ∈ state.r2, isDataElement h) ∧
  (∀ h ∈ state.r3, isDataElement h) ∧ (∀ h ∈ state.r4, isDataElement h) ∧
  (∀ xs len payload, .dataElement xs len payload ∈ references → conf.isRef payload = true) ∧
  (∀ i, f.lookup i ≠ none → target (heapMap1 state.heap i)) ∧
  (∀ i j, f.lookup i ≠ none → f.lookup j ≠ none → heapMap1 state.heap i = heapMap1 state.heap j → i = j) ∧
  (∀ j, target j → ∃ i, f.lookup i ≠ none ∧ heapMap1 state.heap i = j) ∧
  ∀ i j, f.lookup i = some j →
    ∃ xs len payload, heapLookup i heap0 = some (.dataElement xs len payload) ∧
      heapLookup j fullHeap = some (.dataElement
        (if isFinal conf state j then addrMap (heapMap1 state.heap) xs else xs) len payload) ∧
      reachableAddresses roots0 heap0 i ∧
      ∀ ptr value, .pointer ptr value ∈ xs → isFinal conf state j → f.lookup ptr ≠ none

/-- A well-formed input heap initializes the major collector invariant. This
Flapjack result concerns the untagged invariant above. -/
theorem gcInv_init {α β : Type} (conf : Config β) (heap : List (HeapElement α β))
    (roots : List (HeapAddress α)) (good : heapOk heap conf.limit) :
    gcInv conf { emptyGcState with heap := heap, n := conf.limit, ok := decide (heapLength heap = conf.limit) } heap roots := by
  have noForward := good.2.1
  have emptyMap : ∀ key, (heapMap 0 heap).lookup key = none := by
    intro key
    have domainEq := congrFun (heapMap_empty heap 0 noForward) key
    by_cases lookup : (heapMap 0 heap).lookup key = none
    · exact lookup
    · exact False.elim (domainEq.mp lookup)
  have filtered := filter_notForward heap noForward
  have similar := heapsSimilar_refl heap noForward
  have lengthEq : (heap.map elLength).sum = conf.limit := good.1
  simp [gcInv, emptyGcState, heapAddresses, heapLength, filtered, similar, emptyMap, good, lengthEq]

/-- Moving an immediate root leaves the major collector invariant unchanged.
This is a Flapjack case helper for the source move theorem. -/
theorem gcInv_move_data {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α)) (value : α)
    (invariant : gcInv conf state heap0 roots0) :
    gcMove conf state (.data value) = (addrApply (heapMap1 state.heap) (.data value), state) ∧
    gcInv conf state heap0 roots0 := by
  simp [gcMove, addrApply, invariant]

/-- Moving an already-forwarded root preserves the major collector state
and uses the forwarding map's existing destination. -/
theorem gcInv_move_forward {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α))
    (ptr target len : Nat) (value forwardedValue : α)
    (invariant : gcInv conf state heap0 roots0)
    (found : heapLookup ptr state.heap = some (.forwardPointer target forwardedValue len)) :
    gcMove conf state (.pointer ptr value) = (addrApply (heapMap1 state.heap) (.pointer ptr value), state) ∧
    (heapMap 0 state.heap).lookup ptr ≠ none ∧ gcInv conf state heap0 roots0 := by
  have lookup := heapLookup_flookup state.heap ptr target len forwardedValue found
  have applyEq : heapMap1 state.heap ptr = target := holFapply_of_lookup lookup
  simp [gcMove, found, addrApply, applyEq, lookup, invariant]

end Flapjack.Compiler.Backend.GenGc
