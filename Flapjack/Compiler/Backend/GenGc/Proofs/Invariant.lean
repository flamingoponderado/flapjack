import Flapjack.Compiler.Backend.GenGc
import Flapjack.Compiler.Backend.GcShared.HeapSimilarity
import Flapjack.Compiler.Backend.GcShared.Reachability
import Flapjack.Compiler.Backend.GcShared.Related
import Flapjack.Compiler.Backend.CopyingGc.Proofs.Invariant

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

/-- A fresh major-collection move has enough remaining space, installs the
correct forwarding pointer in either heap segment, and retains all existing
forwarding-map entries. This is a case helper; the full post-invariant still
requires the destination bijection and lookup clauses. -/
theorem gcInv_move_fresh_core {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α))
    (ptr len : Nat) (value : α) (addresses : List (HeapAddress α)) (payload : β)
    (invariant : gcInv conf state heap0 roots0)
    (found : heapLookup ptr state.heap = some (.dataElement addresses len payload)) :
    ∃ before after,
      state.heap = before ++ .dataElement addresses len payload :: after ∧
      ptr = heapLength before ∧ len + 1 ≤ state.n ∧
      let target := if conf.isRef payload then state.a + (state.n - (len + 1)) else state.a
      let forwarded := before ++ .forwardPointer target value len :: after
      gcMove conf state (.pointer ptr value) =
        (.pointer target value,
          if conf.isRef payload then
            { state with r4 := .dataElement addresses len payload :: state.r4, n := state.n - (len + 1), heap := forwarded, ok := true }
          else
            { state with h2 := state.h2 ++ [.dataElement addresses len payload], n := state.n - (len + 1), a := state.a + len + 1, heap := forwarded, ok := true }) ∧
      (∀ p, isSomeDataOrForward (heapLookup p state.heap) ↔
        isSomeDataOrForward (heapLookup p forwarded)) ∧
      (∀ i j, (heapMap 0 state.heap).lookup i = some j → (heapMap 0 forwarded).lookup i = some j) := by
  obtain ⟨before, after, heapEq, ptrEq⟩ := heapLookup_split state.heap ptr _ found
  have spaceEq := invariant.2.2.1
  have okEq := invariant.2.2.2.2.1
  rw [heapEq] at spaceEq
  have enough : len + 1 ≤ state.n := by
    simp [List.filter_append, isForwardPointer, heapLength, elLength,
      List.map_append, List.sum_append] at spaceEq
    omega
  refine ⟨before, after, heapEq, ptrEq, enough, ?_, ?_, ?_⟩
  · have atData : heapLookup (heapLength before) (before ++ .dataElement addresses len payload :: after) =
        some (.dataElement addresses len payload) := by simpa [heapEq, ptrEq] using found
    cases ref : conf.isRef payload <;>
      simp [gcMove, atData, ref, enough, okEq, heapEq, ptrEq, gcForwardPtr_thm]
  · intro p
    rw [heapEq]
    simpa using isSomeDataOrForward_replace before after p _ len addresses payload value
  · intro i j old
    rw [heapEq] at old
    exact CopyingGc.heapMap_forward_submap before after addresses len _ payload value i j old

/-- Replacing a copied cell with its forwarding pointer preserves heap
similarity and size while consuming exactly that cell's free-space length.
The destination is arbitrary, so the same facts apply to both placement
branches of the major collector. -/
theorem gcInv_fresh_forward_structure {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α))
    (ptr len target : Nat) (value : α) (addresses : List (HeapAddress α)) (payload : β)
    (invariant : gcInv conf state heap0 roots0)
    (found : heapLookup ptr state.heap = some (.dataElement addresses len payload)) :
    ∃ before after,
      state.heap = before ++ .dataElement addresses len payload :: after ∧
      ptr = heapLength before ∧ len + 1 ≤ state.n ∧
      heapLength (before ++ .forwardPointer target value len :: after) = conf.limit ∧
      heapLength ((before ++ .forwardPointer target value len :: after).filter
        (fun h => !(isForwardPointer h))) = state.n - (len + 1) ∧
      heapsSimilar heap0 (before ++ .forwardPointer target value len :: after) := by
  obtain ⟨before, after, heapEq, ptrEq⟩ := heapLookup_split state.heap ptr _ found
  have free := invariant.2.2.1
  have size := invariant.2.2.2.1
  have similar := invariant.2.2.2.2.2.2.1
  rw [heapEq] at free size similar
  have enough : len + 1 ≤ state.n := by
    simp [List.filter_append, isForwardPointer, heapLength, elLength,
      List.map_append, List.sum_append] at free
    omega
  refine ⟨before, after, heapEq, ptrEq, enough, ?_, ?_, ?_⟩
  · simpa [heapLength, List.map_append, List.sum_append, elLength] using size
  · simp [List.filter_append, isForwardPointer, heapLength, elLength,
      List.map_append, List.sum_append] at free ⊢
    omega
  · have same := heapsSimilar_forward before heap0 after (heapExpand target : List (HeapElement α β))
      [] addresses len payload value similar
    simpa [heapLength_heapExpand] using same

/-- The fresh object's destination lies between the old copied-data and
reference address sets. This supplies the freshness premise for extending the
collector's forwarding-map bijection. -/
theorem gcInv_fresh_target_fresh {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α))
    (ptr len : Nat) (value : α) (addresses : List (HeapAddress α)) (payload : β)
    (invariant : gcInv conf state heap0 roots0)
    (found : heapLookup ptr state.heap = some (.dataElement addresses len payload)) :
    let target := if conf.isRef payload then state.a + (state.n - (len + 1)) else state.a
    ¬ (heapAddresses 0 (state.h1 ++ state.h2) target ∨
      heapAddresses (state.a + state.n) (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) target) := by
  obtain ⟨_, _, _, _, enough, _, _, _⟩ :=
    gcInv_fresh_forward_structure conf state heap0 roots0 ptr len state.a value addresses payload invariant found
  have allocated := invariant.1
  dsimp only
  cases ref : conf.isRef payload <;> simp only [Bool.false_eq_true, ↓reduceIte, not_or]
  all_goals constructor
  all_goals intro member
  all_goals first
    | have bound := heapAddresses_less_heapLength _ 0 _ member; omega
    | have bound := heapAddresses_base_le _ (state.a + state.n) _ member; omega

/-- Both placement choices extend the collector's destination set by the
new object's address and retain the previous destination addresses. -/
theorem gcInv_fresh_target_set {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α))
    (ptr len : Nat) (value : α) (addresses : List (HeapAddress α)) (payload : β)
    (invariant : gcInv conf state heap0 roots0)
    (found : heapLookup ptr state.heap = some (.dataElement addresses len payload)) :
    let target := if conf.isRef payload then state.a + (state.n - (len + 1)) else state.a
    let next := if conf.isRef payload then
      { state with r4 := .dataElement addresses len payload :: state.r4, n := state.n - (len + 1) }
    else
      { state with h2 := state.h2 ++ [.dataElement addresses len payload], n := state.n - (len + 1), a := state.a + len + 1 }
    ∀ p, (heapAddresses 0 (next.h1 ++ next.h2) p ∨
      heapAddresses (next.a + next.n) (next.r4 ++ next.r3 ++ next.r2 ++ next.r1) p) ↔
      (heapAddresses 0 (state.h1 ++ state.h2) p ∨
       heapAddresses (state.a + state.n) (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) p ∨ p = target) := by
  obtain ⟨_, _, _, _, enough, _, _, _⟩ :=
    gcInv_fresh_forward_structure conf state heap0 roots0 ptr len state.a value addresses payload invariant found
  have allocated := invariant.1
  have balance : state.a + (state.n - (len + 1)) + (len + 1) = state.a + state.n := by omega
  dsimp only
  intro p
  cases ref : conf.isRef payload with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← List.append_assoc, CopyingGc.heapAddresses_snoc]
    simp only [Nat.add_zero, allocated]
    have bound : state.a + len + 1 + (state.n - (len + 1)) = state.a + state.n := by omega
    rw [bound]
    tauto
  | true =>
    simp only [↓reduceIte]
    simp only [List.cons_append, heapAddresses, elLength]
    rw [balance]
    tauto

/-- A fresh move extends the major collector's forwarding bijection to the
new destination set, for both data and reference placement. -/
theorem gcInv_fresh_bijection {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α))
    (ptr len : Nat) (value : α) (addresses : List (HeapAddress α)) (payload : β)
    (invariant : gcInv conf state heap0 roots0)
    (found : heapLookup ptr state.heap = some (.dataElement addresses len payload)) :
    ∃ before after,
      state.heap = before ++ .dataElement addresses len payload :: after ∧
      ptr = heapLength before ∧
      let target := if conf.isRef payload then state.a + (state.n - (len + 1)) else state.a
      let forwarded := before ++ .forwardPointer target value len :: after
      let next := if conf.isRef payload then
        { state with r4 := .dataElement addresses len payload :: state.r4, n := state.n - (len + 1) }
      else
        { state with h2 := state.h2 ++ [.dataElement addresses len payload], n := state.n - (len + 1), a := state.a + len + 1 }
      let targets := fun p => heapAddresses 0 (next.h1 ++ next.h2) p ∨
        heapAddresses (next.a + next.n) (next.r4 ++ next.r3 ++ next.r2 ++ next.r1) p
      (∀ i, (heapMap 0 forwarded).lookup i ≠ none → targets (heapMap1 forwarded i)) ∧
      (∀ i j, (heapMap 0 forwarded).lookup i ≠ none → (heapMap 0 forwarded).lookup j ≠ none →
        heapMap1 forwarded i = heapMap1 forwarded j → i = j) ∧
      (∀ j, targets j → ∃ i, (heapMap 0 forwarded).lookup i ≠ none ∧ heapMap1 forwarded i = j) := by
  obtain ⟨before, after, heapEq, ptrEq⟩ := heapLookup_split state.heap ptr _ found
  refine ⟨before, after, heapEq, ptrEq, ?_⟩
  dsimp only
  let target := if conf.isRef payload then state.a + (state.n - (len + 1)) else state.a
  let oldTargets := fun p => heapAddresses 0 (state.h1 ++ state.h2) p ∨
    heapAddresses (state.a + state.n) (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) p
  have sourceFresh := not_in_heapMap before after addresses len payload
  have targetFresh : ¬ oldTargets target :=
    gcInv_fresh_target_fresh conf state heap0 roots0 ptr len value addresses payload invariant found
  have targetSet := gcInv_fresh_target_set conf state heap0 roots0 ptr len value addresses payload invariant found
  dsimp only at targetSet
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, mapsInto, injective, surjective, _⟩ := invariant
  rw [heapEq] at mapsInto injective surjective
  have bij := CopyingGc.finiteMap_bij_insert (heapMap 0 (before ++ .dataElement addresses len payload :: after))
    oldTargets (heapLength before) target sourceFresh targetFresh mapsInto injective surjective
  have newMap := heapMap_replace_data before after target len addresses payload value
  rw [← newMap] at bij
  obtain ⟨newInto, newInjective, newSurjective⟩ := bij
  refine ⟨?_, ?_, ?_⟩
  · intro i defined
    have mapped := newInto i defined
    apply (targetSet _).mpr
    simpa only [oldTargets, target, heapMap1, or_assoc] using mapped
  · simpa only [heapMap1] using newInjective
  · intro j member
    have oldOrNew := (targetSet j).mp member
    apply newSurjective j
    simpa only [oldTargets, target, or_assoc] using oldOrNew

/-- A newly copied object is pending rather than final, regardless of which
side of the major collector heap receives it. -/
theorem gcInv_fresh_notFinal {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α))
    (ptr len : Nat) (value : α) (addresses : List (HeapAddress α)) (payload : β)
    (invariant : gcInv conf state heap0 roots0)
    (found : heapLookup ptr state.heap = some (.dataElement addresses len payload)) :
    let target := if conf.isRef payload then state.a + (state.n - (len + 1)) else state.a
    let next := if conf.isRef payload then
      { state with r4 := .dataElement addresses len payload :: state.r4, n := state.n - (len + 1) }
    else
      { state with h2 := state.h2 ++ [.dataElement addresses len payload], n := state.n - (len + 1), a := state.a + len + 1 }
    ¬ isFinal conf next target := by
  obtain ⟨_, _, _, _, enough, _, _, _⟩ :=
    gcInv_fresh_forward_structure conf state heap0 roots0 ptr len state.a value addresses payload invariant found
  have allocated := invariant.1
  rw [heapLength_append] at allocated
  simp only [heapLength] at allocated
  dsimp only
  cases ref : conf.isRef payload <;> simp only [Bool.false_eq_true, ↓reduceIte, isFinal,
    heapLength, List.map_cons, List.sum_cons, elLength, not_or, not_and, not_lt, not_le]
  all_goals omega

/-- A fresh move's original and destination lookups contain the same object,
and the installed forwarding entry names its destination. -/
theorem gcInv_fresh_new_lookup {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α))
    (ptr len : Nat) (value : α) (addresses : List (HeapAddress α)) (payload : β)
    (invariant : gcInv conf state heap0 roots0)
    (found : heapLookup ptr state.heap = some (.dataElement addresses len payload)) :
    ∃ before after,
      state.heap = before ++ .dataElement addresses len payload :: after ∧ ptr = heapLength before ∧
      let target := if conf.isRef payload then state.a + (state.n - (len + 1)) else state.a
      let forwarded := before ++ .forwardPointer target value len :: after
      let next := if conf.isRef payload then
        { state with r4 := .dataElement addresses len payload :: state.r4, n := state.n - (len + 1) }
      else
        { state with h2 := state.h2 ++ [.dataElement addresses len payload], n := state.n - (len + 1), a := state.a + len + 1 }
      (heapMap 0 forwarded).lookup ptr = some target ∧
      heapLookup ptr heap0 = some (.dataElement addresses len payload) ∧
      heapLookup target (next.h1 ++ next.h2 ++ heapExpand next.n ++ next.r4 ++ next.r3 ++ next.r2 ++ next.r1) =
        some (.dataElement addresses len payload) := by
  obtain ⟨before, after, heapEq, ptrEq⟩ := heapLookup_split state.heap ptr _ found
  have similar := invariant.2.2.2.2.2.2.1
  rw [heapEq] at similar
  obtain ⟨before0, after0, heap0Eq, lengthEq⟩ :=
    heapSimilar_data_imp heap0 before after addresses len payload similar
  have original : heapLookup ptr heap0 = some (.dataElement addresses len payload) := by
    rw [ptrEq, heap0Eq, lengthEq]
    exact heapLookup_prefix before0 after0 _
  have allocated := invariant.1
  refine ⟨before, after, heapEq, ptrEq, ?_, original, ?_⟩
  · rw [ptrEq, heapMap_replace_data before after _ len addresses payload value]
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  · cases ref : conf.isRef payload with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have copied := heapLookup_prefix (state.h1 ++ state.h2)
        (heapExpand (state.n - (len + 1)) ++ state.r4 ++ state.r3 ++ state.r2 ++ state.r1)
        (.dataElement addresses len payload)
      simpa [List.append_assoc, allocated] using copied
    | true =>
      simp only [↓reduceIte]
      have copied := heapLookup_prefix ((state.h1 ++ state.h2) ++ heapExpand (state.n - (len + 1)))
        (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) (.dataElement addresses len payload)
      have allocated' : heapLength state.h1 + heapLength state.h2 = state.a := by
        simpa [heapLength_append] using allocated
      simpa [List.append_assoc, heapLength_append, heapLength_heapExpand, ← Nat.add_assoc, allocated'] using copied

end Flapjack.Compiler.Backend.GenGc
