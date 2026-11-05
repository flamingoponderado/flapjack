import Flapjack.Compiler.Backend.GenGc
import Flapjack.Compiler.Backend.GcShared.HeapSimilarity
import Flapjack.Compiler.Backend.GcShared.Reachability
import Flapjack.Compiler.Backend.GcShared.Related
import Flapjack.Compiler.Backend.CopyingGc.Proofs.Invariant
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialSplit
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalAccumulator
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.GenerationalSplit

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
        { state with r4 := HeapElement.dataElement addresses len payload :: state.r4, n := state.n - (len + 1) }
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

/-- Filling the end of a free region leaves every existing data-element
lookup unchanged. This is a Flapjack heap lemma for reference-side copying. -/
theorem heapLookup_fillEnd_preserves_data {α β : Type}
    (before after : List (HeapElement α β)) (free len index : Nat)
    (newRoots oldRoots : List (HeapAddress α)) (newData oldData : β) (oldLen : Nat)
    (enough : len + 1 ≤ free)
    (found : heapLookup index (before ++ heapExpand free ++ after) = some (.dataElement oldRoots oldLen oldData)) :
    heapLookup index (before ++ heapExpand (free - (len + 1)) ++
      .dataElement newRoots len newData :: after) = some (.dataElement oldRoots oldLen oldData) := by
  have equalLength : heapLength (before ++ heapExpand free) =
      heapLength (before ++ heapExpand (free - (len + 1)) ++ [.dataElement newRoots len newData]) := by
    simp only [heapLength_append, heapLength_heapExpand]
    simp only [heapLength, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, elLength]
    omega
  by_cases below : index < heapLength (before ++ heapExpand free)
  · have oldPrefix : heapLookup index (before ++ heapExpand free) = some (.dataElement oldRoots oldLen oldData) := by
      have prior := found
      rw [heapLookup_append] at prior
      simpa [below] using prior
    have original := (DataToWord.Proofs.Memory.heapLookup_expand_eq_some index before free oldRoots oldLen oldData).mp oldPrefix
    have extended := heapLookup_extend before (heapExpand (free - (len + 1)) ++
      .dataElement newRoots len newData :: after) index _ original
    simpa [List.append_assoc] using extended
  · have prior := found
    rw [heapLookup_append] at prior
    have afterStart : heapLookup (index - heapLength (before ++ heapExpand free)) after =
        some (.dataElement oldRoots oldLen oldData) := by simpa [below] using prior
    have nextBelow : ¬ index < heapLength (before ++ heapExpand (free - (len + 1)) ++
        [.dataElement newRoots len newData]) := by rw [← equalLength]; exact below
    have restored := heapLookup_append index (before ++ heapExpand (free - (len + 1)) ++
      [.dataElement newRoots len newData]) after
    simp only [nextBelow, if_false] at restored
    rw [← equalLength, afterStart] at restored
    simpa [List.append_assoc] using restored

/-- Filling the beginning of a free region also preserves every existing
data-element lookup. This is the data-side companion to the reference-side
heap lemma above. -/
theorem heapLookup_fillStart_preserves_data {α β : Type}
    (before after : List (HeapElement α β)) (free len index : Nat)
    (newRoots oldRoots : List (HeapAddress α)) (newData oldData : β) (oldLen : Nat)
    (enough : len + 1 ≤ free)
    (found : heapLookup index (before ++ heapExpand free ++ after) = some (.dataElement oldRoots oldLen oldData)) :
    heapLookup index (before ++ [.dataElement newRoots len newData] ++
      heapExpand (free - (len + 1)) ++ after) = some (.dataElement oldRoots oldLen oldData) := by
  have equalLength : heapLength (before ++ heapExpand free) =
      heapLength (before ++ [.dataElement newRoots len newData] ++ heapExpand (free - (len + 1))) := by
    simp only [heapLength_append, heapLength_heapExpand]
    simp only [heapLength, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, elLength]
    omega
  by_cases below : index < heapLength (before ++ heapExpand free)
  · have oldPrefix : heapLookup index (before ++ heapExpand free) = some (.dataElement oldRoots oldLen oldData) := by
      have prior := found
      rw [heapLookup_append] at prior
      simpa [below] using prior
    have original := (DataToWord.Proofs.Memory.heapLookup_expand_eq_some index before free oldRoots oldLen oldData).mp oldPrefix
    have extended := heapLookup_extend before ([.dataElement newRoots len newData] ++
      heapExpand (free - (len + 1)) ++ after) index _ original
    simpa [List.append_assoc] using extended
  · have prior := found
    rw [heapLookup_append] at prior
    have afterStart : heapLookup (index - heapLength (before ++ heapExpand free)) after =
        some (.dataElement oldRoots oldLen oldData) := by simpa [below] using prior
    have nextBelow : ¬ index < heapLength (before ++ [.dataElement newRoots len newData] ++
        heapExpand (free - (len + 1))) := by rw [← equalLength]; exact below
    have restored := heapLookup_append index (before ++ [.dataElement newRoots len newData] ++
      heapExpand (free - (len + 1))) after
    simp only [nextBelow, if_false] at restored
    rw [← equalLength, afterStart] at restored
    simpa [List.append_assoc] using restored

/-- Moving a fresh object leaves the collector's final-region predicate
unchanged at every address, even though the free region shrinks. -/
theorem gcInv_fresh_isFinal {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α))
    (ptr len : Nat) (value : α) (addresses : List (HeapAddress α)) (payload : β)
    (invariant : gcInv conf state heap0 roots0)
    (found : heapLookup ptr state.heap = some (.dataElement addresses len payload)) :
    let next := if conf.isRef payload then
      { state with r4 := .dataElement addresses len payload :: state.r4, n := state.n - (len + 1) }
    else
      { state with h2 := state.h2 ++ [.dataElement addresses len payload], n := state.n - (len + 1), a := state.a + len + 1 }
    ∀ p, isFinal conf next p ↔ isFinal conf state p := by
  obtain ⟨_, _, _, _, enough, _, _, _⟩ :=
    gcInv_fresh_forward_structure conf state heap0 roots0 ptr len state.a value addresses payload invariant found
  dsimp only
  intro p
  cases ref : conf.isRef payload <;> simp only [Bool.false_eq_true, ↓reduceIte, isFinal,
    heapLength, List.map_cons, List.sum_cons, elLength]
  all_goals omega

open Classical in
/-- A previously forwarded object's heap lookup and reachability witness
survive the fresh move. This is the old-entry case of the major collector's
move invariant. -/
theorem gcInv_fresh_old_lookup {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α))
    (before after : List (HeapElement α β)) (len i j : Nat) (value : α)
    (addresses : List (HeapAddress α)) (payload : β)
    (invariant : gcInv conf state heap0 roots0)
    (heapEq : state.heap = before ++ .dataElement addresses len payload :: after)
    (oldLookup : (heapMap 0 state.heap).lookup i = some j) :
    let target := if conf.isRef payload then state.a + (state.n - (len + 1)) else state.a
    let forwarded := before ++ .forwardPointer target value len :: after
    let next := if conf.isRef payload then
      { state with r4 := .dataElement addresses len payload :: state.r4, n := state.n - (len + 1) }
    else
      { state with h2 := state.h2 ++ [.dataElement addresses len payload], n := state.n - (len + 1), a := state.a + len + 1 }
    ∃ xs size data,
      heapLookup i heap0 = some (.dataElement xs size data) ∧
      heapLookup j (next.h1 ++ next.h2 ++ heapExpand next.n ++ next.r4 ++ next.r3 ++ next.r2 ++ next.r1) =
        some (.dataElement (if isFinal conf next j then addrMap (heapMap1 forwarded) xs else xs) size data) ∧
      reachableAddresses roots0 heap0 i ∧
      ∀ ptr u, .pointer ptr u ∈ xs → isFinal conf next j → (heapMap 0 forwarded).lookup ptr ≠ none := by
  have found : heapLookup (heapLength before) state.heap = some (.dataElement addresses len payload) := by
    rw [heapEq]
    exact heapLookup_prefix before after _
  obtain ⟨_, _, _, _, enough, _, _, _⟩ :=
    gcInv_fresh_forward_structure conf state heap0 roots0 (heapLength before) len state.a value addresses payload invariant found
  have finalEq := gcInv_fresh_isFinal conf state heap0 roots0 (heapLength before) len value addresses payload invariant found
  dsimp only at finalEq ⊢
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, entries⟩ := invariant
  obtain ⟨xs, size, data, oldOriginal, oldCopied, reach, children⟩ := entries i j oldLookup
  have renamed : isFinal conf state j →
      addrMap (heapMap1 (before ++ .forwardPointer (if conf.isRef payload then state.a + (state.n - (len + 1)) else state.a) value len :: after)) xs =
      addrMap (heapMap1 state.heap) xs := by
    intro final
    apply addrMap_eq
    intro p u member
    have present := children p u member final
    rw [heapEq] at present ⊢
    exact CopyingGc.heapMap1_forward_old before after addresses len _ payload value p present
  have copied : heapLookup j
      ((if conf.isRef payload then
        { state with r4 := .dataElement addresses len payload :: state.r4, n := state.n - (len + 1) }
      else
        { state with h2 := state.h2 ++ [HeapElement.dataElement addresses len payload], n := state.n - (len + 1), a := state.a + len + 1 }).h1 ++
       (if conf.isRef payload then
        { state with r4 := .dataElement addresses len payload :: state.r4, n := state.n - (len + 1) }
      else
        { state with h2 := state.h2 ++ [HeapElement.dataElement addresses len payload], n := state.n - (len + 1), a := state.a + len + 1 }).h2 ++
       heapExpand (state.n - (len + 1)) ++
       (if conf.isRef payload then .dataElement addresses len payload :: state.r4 else state.r4) ++
       state.r3 ++ state.r2 ++ state.r1) =
      some (.dataElement (if isFinal conf state j then addrMap (heapMap1 state.heap) xs else xs) size data) := by
    cases ref : conf.isRef payload with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have retained := heapLookup_fillStart_preserves_data (state.h1 ++ state.h2)
        (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) state.n len j addresses _ payload data size enough
        (by simpa [List.append_assoc] using oldCopied)
      simpa [List.append_assoc] using retained
    | true =>
      simp only [↓reduceIte]
      have retained := heapLookup_fillEnd_preserves_data (state.h1 ++ state.h2)
        (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) state.n len j addresses _ payload data size enough
        (by simpa [List.append_assoc] using oldCopied)
      simpa [List.append_assoc] using retained
  refine ⟨xs, size, data, oldOriginal, ?_, reach, ?_⟩
  · rw [finalEq j]
    by_cases final : isFinal conf state j
    · have renamed' := renamed final
      cases ref : conf.isRef payload <;> simp only [ref, Bool.false_eq_true, ↓reduceIte] at renamed'
      all_goals simpa [ref, final, renamed'] using copied
    · cases ref : conf.isRef payload <;> simpa [ref, final] using copied
  · intro p u member final
    have oldDefined := children p u member ((finalEq j).mp final)
    rw [heapEq] at oldDefined
    cases lookup : (heapMap 0 (before ++ .dataElement addresses len payload :: after)).lookup p with
    | none => exact False.elim (oldDefined lookup)
    | some destination =>
      have next := CopyingGc.heapMap_forward_submap before after addresses len
        (if conf.isRef payload then state.a + (state.n - (len + 1)) else state.a) payload value p destination lookup
      rw [next]
      simp

/-- Structural fields of the major-collection invariant, excluding the
forwarding-map bijection and per-entry simulation. This is Flapjack proof
infrastructure for assembling a move. -/
def gcInvStructure {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) : Prop :=
  heapLength (state.h1 ++ state.h2) = state.a ∧
  state.a + state.n + heapLength (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) = conf.limit ∧
  heapLength (state.heap.filter (fun h => !(isForwardPointer h))) = state.n ∧
  heapLength state.heap = conf.limit ∧ state.ok = true ∧
  heapOk heap0 conf.limit ∧ heapsSimilar heap0 state.heap ∧
  (∀ h ∈ state.h1, isDataElement h) ∧ (∀ h ∈ state.h2, isDataElement h) ∧
  (∀ h ∈ state.r1, isDataElement h) ∧ (∀ h ∈ state.r2, isDataElement h) ∧
  (∀ h ∈ state.r3, isDataElement h) ∧ (∀ h ∈ state.r4, isDataElement h) ∧
  ∀ xs len payload, .dataElement xs len payload ∈ state.r4 ++ state.r3 ++ state.r2 ++ state.r1 →
    conf.isRef payload = true

/-- The major invariant implies its structural fields. -/
theorem gcInv_structure {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α))
    (invariant : gcInv conf state heap0 roots0) : gcInvStructure conf state heap0 := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, _⟩ := invariant
  exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n⟩

/-- Fresh copying re-establishes the major invariant's size, similarity,
segment and reference-classification fields in both placement branches. -/
theorem gcInv_fresh_structure {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α))
    (before after : List (HeapElement α β)) (len : Nat) (value : α)
    (addresses : List (HeapAddress α)) (payload : β)
    (invariant : gcInv conf state heap0 roots0)
    (heapEq : state.heap = before ++ .dataElement addresses len payload :: after) :
    let target := if conf.isRef payload then state.a + (state.n - (len + 1)) else state.a
    let forwarded := before ++ .forwardPointer target value len :: after
    let next := if conf.isRef payload then
      { state with r4 := .dataElement addresses len payload :: state.r4, n := state.n - (len + 1), heap := forwarded, ok := true }
    else
      { state with h2 := state.h2 ++ [.dataElement addresses len payload], n := state.n - (len + 1), a := state.a + len + 1, heap := forwarded, ok := true }
    gcInvStructure conf next heap0 := by
  have originalFree := invariant.2.2.1
  have originalSize := invariant.2.2.2.1
  have originalSimilar := invariant.2.2.2.2.2.2.1
  rw [heapEq] at originalFree originalSize originalSimilar
  have enough : len + 1 ≤ state.n := by
    simp [List.filter_append, isForwardPointer, heapLength, elLength,
      List.map_append, List.sum_append] at originalFree
    omega
  let target := if conf.isRef payload then state.a + (state.n - (len + 1)) else state.a
  have size : heapLength (before ++ .forwardPointer target value len :: after) = conf.limit := by
    simpa [heapLength, List.map_append, List.sum_append, elLength] using originalSize
  have free : heapLength ((before ++ .forwardPointer target value len :: after).filter
      (fun h => !(isForwardPointer h))) = state.n - (len + 1) := by
    simp [List.filter_append, isForwardPointer, heapLength, elLength,
      List.map_append, List.sum_append] at originalFree ⊢
    omega
  have similar : heapsSimilar heap0 (before ++ .forwardPointer target value len :: after) := by
    have h := heapsSimilar_forward before heap0 after (heapExpand target : List (HeapElement α β))
      [] addresses len payload value originalSimilar
    simpa [heapLength_heapExpand] using h
  obtain ⟨allocated, balance, _, _, _, good, _, h1Data, h2Data, r1Data, r2Data, r3Data, r4Data, refs⟩ :=
    gcInv_structure conf state heap0 roots0 invariant
  dsimp only [target] at size free similar
  dsimp only
  cases ref : conf.isRef payload with
  | false =>
    simp only [ref, Bool.false_eq_true, ↓reduceIte] at size free similar ⊢
    unfold gcInvStructure
    dsimp only
    refine ⟨?_, ?_, free, size, rfl, good, similar, h1Data, ?_, r1Data, r2Data, r3Data, r4Data, refs⟩
    · simp [heapLength, elLength] at allocated ⊢
      omega
    · omega
    · intro element member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with member | rfl
      · exact h2Data element member
      · exact ⟨addresses, len, payload, rfl⟩
  | true =>
    simp only [ref, ↓reduceIte] at size free similar ⊢
    unfold gcInvStructure
    dsimp only
    refine ⟨allocated, ?_, free, size, rfl, good, similar, h1Data, h2Data, r1Data, r2Data, r3Data, ?_, ?_⟩
    · simp [heapLength, elLength] at balance ⊢
      omega
    · intro element member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨addresses, len, payload, rfl⟩
      · exact r4Data element member
    · intro xs n data member
      simp only [List.cons_append, List.mem_cons] at member
      rcases member with same | member
      · cases same
        exact ref
      · exact refs xs n data member

/-- Two decompositions at the same heap offset have the same prefix and
suffix. This is Flapjack infrastructure for joining collector case proofs. -/
theorem heapSplit_same_prefix {α β : Type} (before after before1 after1 : List (HeapElement α β))
    (sameHeap : before ++ after = before1 ++ after1)
    (sameLength : heapLength before = heapLength before1) : before = before1 ∧ after = after1 := by
  have first := DataToWord.Proofs.Gc.heapSplit_append before after
  have second := DataToWord.Proofs.Gc.heapSplit_append before1 after1
  rw [sameHeap, sameLength] at first
  exact Prod.mk.inj (Option.some.inj (first.symm.trans second))

open Classical in
/-- A fresh root move re-establishes the complete major-collector invariant.
The invariant's internal map representation remains separately unreviewed. -/
theorem gcInv_fresh_post {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α))
    (before after : List (HeapElement α β)) (len : Nat) (value : α)
    (addresses : List (HeapAddress α)) (payload : β)
    (invariant : gcInv conf state heap0 roots0)
    (heapEq : state.heap = before ++ .dataElement addresses len payload :: after)
    (reachable : reachableAddresses roots0 heap0 (heapLength before)) :
    let target := if conf.isRef payload then state.a + (state.n - (len + 1)) else state.a
    let forwarded := before ++ .forwardPointer target value len :: after
    let next := if conf.isRef payload then
      { state with r4 := .dataElement addresses len payload :: state.r4, n := state.n - (len + 1), heap := forwarded, ok := true }
    else
      { state with h2 := state.h2 ++ [.dataElement addresses len payload], n := state.n - (len + 1), a := state.a + len + 1, heap := forwarded, ok := true }
    gcInv conf next heap0 roots0 := by
  have found : heapLookup (heapLength before) state.heap = some (.dataElement addresses len payload) := by
    rw [heapEq]
    exact heapLookup_prefix before after _
  have structural := gcInv_fresh_structure conf state heap0 roots0 before after len value addresses payload invariant heapEq
  have notFinal := gcInv_fresh_notFinal conf state heap0 roots0 (heapLength before) len value addresses payload invariant found
  obtain ⟨b, c, eq, ptrEq, bij⟩ :=
    gcInv_fresh_bijection conf state heap0 roots0 (heapLength before) len value addresses payload invariant found
  obtain ⟨prefixEq, suffix⟩ := heapSplit_same_prefix b (.dataElement addresses len payload :: c)
    before (.dataElement addresses len payload :: after) (eq.symm.trans heapEq) ptrEq.symm
  subst b
  have suffixEq : c = after := (List.cons.inj suffix).2
  subst c
  obtain ⟨b, c, eq, ptrEq, newEntry⟩ :=
    gcInv_fresh_new_lookup conf state heap0 roots0 (heapLength before) len value addresses payload invariant found
  obtain ⟨prefixEq, suffix⟩ := heapSplit_same_prefix b (.dataElement addresses len payload :: c)
    before (.dataElement addresses len payload :: after) (eq.symm.trans heapEq) ptrEq.symm
  subst b
  have suffixEq : c = after := (List.cons.inj suffix).2
  subst c
  dsimp only at structural notFinal bij newEntry ⊢
  have entries : ∀ i j, (heapMap 0 (before ++ .forwardPointer
      (if conf.isRef payload then state.a + (state.n - (len + 1)) else state.a) value len :: after)).lookup i = some j →
      ∃ xs size data, heapLookup i heap0 = some (.dataElement xs size data) ∧
        heapLookup j ((if conf.isRef payload then
          { state with r4 := .dataElement addresses len payload :: state.r4, n := state.n - (len + 1) }
        else
          { state with h2 := state.h2 ++ [HeapElement.dataElement addresses len payload], n := state.n - (len + 1), a := state.a + len + 1 }).h1 ++
          (if conf.isRef payload then
          { state with r4 := .dataElement addresses len payload :: state.r4, n := state.n - (len + 1) }
        else
          { state with h2 := state.h2 ++ [HeapElement.dataElement addresses len payload], n := state.n - (len + 1), a := state.a + len + 1 }).h2 ++
          heapExpand (state.n - (len + 1)) ++
          (if conf.isRef payload then .dataElement addresses len payload :: state.r4 else state.r4) ++ state.r3 ++ state.r2 ++ state.r1) =
          some (.dataElement (if isFinal conf (if conf.isRef payload then
            { state with r4 := .dataElement addresses len payload :: state.r4, n := state.n - (len + 1) }
          else
            { state with h2 := state.h2 ++ [.dataElement addresses len payload], n := state.n - (len + 1), a := state.a + len + 1 }) j
            then addrMap (heapMap1 (before ++ .forwardPointer
              (if conf.isRef payload then state.a + (state.n - (len + 1)) else state.a) value len :: after)) xs else xs) size data) ∧
        reachableAddresses roots0 heap0 i ∧
        ∀ p u, .pointer p u ∈ xs → isFinal conf (if conf.isRef payload then
          { state with r4 := .dataElement addresses len payload :: state.r4, n := state.n - (len + 1) }
        else
          { state with h2 := state.h2 ++ [.dataElement addresses len payload], n := state.n - (len + 1), a := state.a + len + 1 }) j →
          (heapMap 0 (before ++ .forwardPointer
            (if conf.isRef payload then state.a + (state.n - (len + 1)) else state.a) value len :: after)).lookup p ≠ none := by
    intro i j lookup
    by_cases same : i = heapLength before
    · subst i
      have targetEq := Option.some.inj (lookup.symm.trans newEntry.1)
      subst j
      refine ⟨addresses, len, payload, newEntry.2.1, ?_, reachable, ?_⟩
      · cases ref : conf.isRef payload <;> simp only [ref, Bool.false_eq_true, ↓reduceIte] at notFinal newEntry ⊢
        all_goals simpa [notFinal] using newEntry.2.2
      · intro p u member final
        exact False.elim (notFinal final)
    · have oldLookup : (heapMap 0 state.heap).lookup i = some j := by
        rw [heapEq]
        rw [heapMap_replace_data before after _ len addresses payload value] at lookup
        simpa [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm same] using lookup
      have prior := gcInv_fresh_old_lookup conf state heap0 roots0 before after len i j value addresses payload invariant heapEq oldLookup
      cases ref : conf.isRef payload <;> simpa [ref, List.append_assoc] using prior
  cases ref : conf.isRef payload <;>
    simp only [ref, Bool.false_eq_true, ↓reduceIte, gcInv, gcInvStructure] at structural bij entries ⊢
  all_goals refine ⟨structural.1, structural.2.1, structural.2.2.1, structural.2.2.2.1, structural.2.2.2.2.1,
    structural.2.2.2.2.2.1, structural.2.2.2.2.2.2.1, structural.2.2.2.2.2.2.2.1,
    structural.2.2.2.2.2.2.2.2.1, structural.2.2.2.2.2.2.2.2.2.1,
    structural.2.2.2.2.2.2.2.2.2.2.1, structural.2.2.2.2.2.2.2.2.2.2.2.1,
    structural.2.2.2.2.2.2.2.2.2.2.2.2.1, structural.2.2.2.2.2.2.2.2.2.2.2.2.2,
    bij.1, bij.2.1, bij.2.2, ?_⟩
  all_goals
    intro i j lookup
    obtain ⟨xs, size, data, original, copied, reach, children⟩ := entries i j lookup
    refine ⟨xs, size, data, original, ?_, reach, ?_⟩
    · simp only [isFinal, List.append_assoc, List.cons_append] at copied ⊢
      split_ifs at copied ⊢ <;> assumption
    · simpa [isFinal] using children

/-- A valid root move preserves the major invariant and extends its
forwarding map. This source-shaped result remains untagged while the
invariant's internal finite-map representation is unreviewed. -/
theorem gcInv_move {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α)) (root : HeapAddress α)
    (invariant : gcInv conf state heap0 roots0)
    (valid : ∀ ptr u, root = .pointer ptr u →
      isSomeDataOrForward (heapLookup ptr state.heap) ∧ reachableAddresses roots0 heap0 ptr) :
    ∃ next,
      gcMove conf state root = (addrApply (heapMap1 next.heap) root, next) ∧
      (∀ ptr u, root = .pointer ptr u → (heapMap 0 next.heap).lookup ptr ≠ none) ∧
      (∀ ptr, isSomeDataOrForward (heapLookup ptr state.heap) ↔ isSomeDataOrForward (heapLookup ptr next.heap)) ∧
      (∀ i j, (heapMap 0 state.heap).lookup i = some j → (heapMap 0 next.heap).lookup i = some j) ∧
      gcInv conf next heap0 roots0 := by
  cases root with
  | data value =>
    refine ⟨state, (gcInv_move_data conf state heap0 roots0 value invariant).1, ?_, ?_, ?_, invariant⟩
    · intro ptr u impossible; cases impossible
    · intro ptr; rfl
    · intro i j lookup; exact lookup
  | pointer ptr value =>
    obtain ⟨rootData, reachable⟩ := valid ptr value rfl
    rcases rootData with forward | data
    · obtain ⟨target, forwardedValue, len, found⟩ := forward
      obtain ⟨run, defined, nextInv⟩ := gcInv_move_forward conf state heap0 roots0 ptr target len value forwardedValue invariant found
      refine ⟨state, run, ?_, ?_, ?_, nextInv⟩
      · intro p u eq
        cases eq
        exact defined
      · intro p; rfl
      · intro i j lookup; exact lookup
    · obtain ⟨addresses, len, payload, found⟩ := data
      obtain ⟨before, after, heapEq, ptrEq, enough, run, observation, submap⟩ :=
        gcInv_move_fresh_core conf state heap0 roots0 ptr len value addresses payload invariant found
      let target := if conf.isRef payload then state.a + (state.n - (len + 1)) else state.a
      let forwarded := before ++ .forwardPointer target value len :: after
      let next := if conf.isRef payload then
        { state with r4 := .dataElement addresses len payload :: state.r4, n := state.n - (len + 1), heap := forwarded, ok := true }
      else
        { state with h2 := state.h2 ++ [.dataElement addresses len payload], n := state.n - (len + 1), a := state.a + len + 1, heap := forwarded, ok := true }
      have nextHeap : next.heap = forwarded := by
        dsimp only [next]
        split <;> rfl
      have post : gcInv conf next heap0 roots0 := by
        apply gcInv_fresh_post conf state heap0 roots0 before after len value addresses payload invariant heapEq
        simpa [ptrEq] using reachable
      have mapped : (heapMap 0 forwarded).lookup ptr = some target := by
        dsimp only [forwarded]
        rw [ptrEq, heapMap_replace_data before after target len addresses payload value]
        simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have mapApply : heapMap1 next.heap ptr = target := by
        rw [nextHeap]
        exact holFapply_of_lookup mapped
      refine ⟨next, ?_, ?_, ?_, ?_, post⟩
      · simpa [target, forwarded, next, addrApply, mapApply] using run
      · intro p u eq
        cases eq
        rw [nextHeap, mapped]
        simp
      · intro p
        rw [nextHeap]
        exact observation p
      · intro i j lookup
        rw [nextHeap]
        exact submap i j lookup

/-- Moving a list of valid roots preserves the major invariant, extends the
forwarding map, and renames all roots by the final map. This source-shaped
lemma remains untagged while the invariant's internal map is unreviewed. -/
theorem gcInv_moveList {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 xs : List (HeapAddress α))
    (invariant : gcInv conf state heap0 roots0)
    (rootsValid : ∀ ptr u, .pointer ptr u ∈ xs →
      isSomeDataOrForward (heapLookup ptr state.heap) ∧ reachableAddresses roots0 heap0 ptr) :
    ∃ next,
      gcMoveList conf state xs = (addrMap (heapMap1 next.heap) xs, next) ∧
      (∀ ptr u, .pointer ptr u ∈ xs → (heapMap 0 next.heap).lookup ptr ≠ none) ∧
      (∀ ptr, isSomeDataOrForward (heapLookup ptr state.heap) ↔ isSomeDataOrForward (heapLookup ptr next.heap)) ∧
      (∀ i j, (heapMap 0 state.heap).lookup i = some j → (heapMap 0 next.heap).lookup i = some j) ∧
      gcInv conf next heap0 roots0 := by
  induction xs generalizing state with
  | nil => exact ⟨state, by simp [gcMoveList, addrMap, invariant]⟩
  | cons head tail ih =>
    have headValid : ∀ ptr u, head = .pointer ptr u →
        isSomeDataOrForward (heapLookup ptr state.heap) ∧ reachableAddresses roots0 heap0 ptr := by
      intro ptr u eq
      exact rootsValid ptr u (by simp [← eq])
    obtain ⟨middle, move, headDomain, observation1, submap1, inv1⟩ :=
      gcInv_move conf state heap0 roots0 head invariant headValid
    have tailValid : ∀ ptr u, .pointer ptr u ∈ tail →
        isSomeDataOrForward (heapLookup ptr middle.heap) ∧ reachableAddresses roots0 heap0 ptr := by
      intro ptr u member
      obtain ⟨valid, reach⟩ := rootsValid ptr u (by simp [member])
      exact ⟨(observation1 ptr).mp valid, reach⟩
    obtain ⟨next, moves, tailDomain, observation2, submap2, inv2⟩ := ih middle inv1 tailValid
    have headApply : addrApply (heapMap1 middle.heap) head = addrApply (heapMap1 next.heap) head := by
      cases head with
      | data value => rfl
      | pointer ptr value =>
        have defined := headDomain ptr value rfl
        cases found : (heapMap 0 middle.heap).lookup ptr with
        | none => exact False.elim (defined found)
        | some target =>
          have later := submap2 ptr target found
          simp [addrApply, heapMap1, holFapply_of_lookup found, holFapply_of_lookup later]
    refine ⟨next, ?_, ?_, ?_, ?_, inv2⟩
    · simp only [gcMoveList, move, headApply, moves]
      cases head <;> rfl
    · intro ptr u member
      simp only [List.mem_cons] at member
      rcases member with eq | member
      · have defined := headDomain ptr u eq.symm
        cases found : (heapMap 0 middle.heap).lookup ptr with
        | none => exact False.elim (defined found)
        | some target => rw [submap2 ptr target found]; simp
      · exact tailDomain ptr u member
    · intro ptr
      exact (observation1 ptr).trans (observation2 ptr)
    · intro i j old
      exact submap2 i j (submap1 i j old)

/-- Finishing an empty reference queue moves the scanned reference segment
to the completed segment without changing the major collector invariant. -/
theorem gcInv_refs_finish {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α))
    (invariant : gcInv conf state heap0 roots0) (empty : state.r2 = []) :
    gcInv conf { state with r3 := [], r1 := state.r3 ++ state.r1 } heap0 roots0 := by
  classical
  have finalEq (p : Nat) :
      isFinal conf { state with r3 := [], r1 := state.r3 ++ state.r1 } p ↔ isFinal conf state p := by
    simp only [isFinal, empty, heapLength, List.map_nil, List.sum_nil, Nat.add_zero]
    omega
  simp only [empty] at finalEq
  obtain ⟨allocated, balance, free, size, ok, good, similar, h1, h2, r1, r2, r3, r4, refs,
    into, injective, surjective, entries⟩ := invariant
  simp only [gcInv, empty, List.append_nil, List.append_assoc]
  refine ⟨allocated, ?_, free, size, ok, good, similar, h1, h2, ?_, ?_, ?_, r4, ?_, ?_, injective, ?_, ?_⟩
  · simpa [empty, List.append_assoc] using balance
  · intro h member
    simp only [List.mem_append] at member
    rcases member with member | member
    · exact r3 h member
    · exact r1 h member
  · simp
  · simp
  · simpa [empty, List.append_assoc] using refs
  · simpa [empty, List.append_assoc] using into
  · simpa [empty, List.append_assoc] using surjective
  · intro i j lookup
    obtain ⟨xs, len, payload, original, copied, reachable, children⟩ := entries i j lookup
    refine ⟨xs, len, payload, original, ?_, reachable, ?_⟩
    · simp only [empty, List.append_nil, List.append_assoc, finalEq] at copied ⊢
      split_ifs at copied ⊢ <;> assumption
    · intro ptr value member final
      apply children ptr value member
      exact (finalEq j).mp final

/-- Children of the next unscanned copied data object are valid in the
current heap and reachable in the original heap. -/
theorem gcInv_data_scan_children {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α))
    (xs : List (HeapAddress α)) (len : Nat) (payload : β) (pending : List (HeapElement α β))
    (invariant : gcInv conf state heap0 roots0)
    (head : state.h2 = .dataElement xs len payload :: pending) :
    ∀ ptr u, .pointer ptr u ∈ xs →
      isSomeDataOrForward (heapLookup ptr state.heap) ∧ reachableAddresses roots0 heap0 ptr := by
  obtain ⟨allocated, _, _, _, _, heapGood, similar, _, _, _, _, _, _, _, _, _, surjective, entries⟩ := invariant
  have atBoundary : heapAddresses 0 (state.h1 ++ state.h2) (heapLength state.h1) := by
    rw [head, heapAddresses_append]
    simp [heapAddresses]
  obtain ⟨i, defined, mapEq⟩ := surjective (heapLength state.h1) (Or.inl atBoundary)
  cases lookup : (heapMap 0 state.heap).lookup i with
  | none => exact False.elim (defined lookup)
  | some j =>
    have jEq : j = heapLength state.h1 := by
      change holFapply (heapMap 0 state.heap) i = heapLength state.h1 at mapEq
      rw [holFapply_of_lookup lookup] at mapEq
      exact mapEq
    obtain ⟨oldXs, size, data, oldFound, newFound, parentReach, _⟩ := entries i j lookup
    subst j
    have room : heapLength state.h1 + (len + 1) ≤ state.a := by
      rw [heapLength_append, head] at allocated
      simp [heapLength, elLength] at allocated ⊢
      omega
    have notFinal : ¬ isFinal conf state (heapLength state.h1) := by
      simp only [isFinal, not_or, not_and, not_lt, not_le]
      omega
    simp only [notFinal, ↓reduceIte] at newFound
    have boundary := heapLookup_prefix state.h1
      (pending ++ heapExpand state.n ++ state.r4 ++ state.r3 ++ state.r2 ++ state.r1)
      (.dataElement xs len payload)
    have boundaryFound : heapLookup (heapLength state.h1)
        (state.h1 ++ state.h2 ++ heapExpand state.n ++ state.r4 ++ state.r3 ++ state.r2 ++ state.r1) =
        some (.dataElement xs len payload) := by
      simpa [head, List.append_assoc] using boundary
    have adjusted : heapLookup (heapLength state.h1)
        (state.h1 ++ state.h2 ++ heapExpand state.n ++ (state.r4 ++ state.r3 ++ state.r2 ++ state.r1)) =
        some (.dataElement xs len payload) := by simpa [List.append_assoc] using boundaryFound
    have equalElements : HeapElement.dataElement oldXs size data = .dataElement xs len payload :=
      Option.some.inj (newFound.symm.trans adjusted)
    cases equalElements
    intro ptr u member
    have oldMember : .dataElement xs len payload ∈ heap0 := heapLookup_mem heap0 i _ oldFound
    have originalData : isSomeDataElement (heapLookup ptr heap0) :=
      heapGood.2.2 xs len payload ptr u ⟨oldMember, member⟩
    refine ⟨heapSimilar_data_imp_dataOrForward heap0 state.heap ptr similar originalData, ?_⟩
    obtain ⟨rootValue, root, rootMember, path⟩ := parentReach
    exact ⟨rootValue, root, rootMember, path.tail ⟨xs, len, payload, u, oldFound, member⟩⟩

/-- Children of the next unscanned reference object are valid in the current
heap and reachable in the original heap. -/
theorem gcInv_refs_scan_children {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α))
    (xs : List (HeapAddress α)) (len : Nat) (payload : β) (pending : List (HeapElement α β))
    (invariant : gcInv conf state heap0 roots0)
    (head : state.r2 = .dataElement xs len payload :: pending) :
    ∀ ptr u, .pointer ptr u ∈ xs →
      isSomeDataOrForward (heapLookup ptr state.heap) ∧ reachableAddresses roots0 heap0 ptr := by
  obtain ⟨allocated, _, _, _, _, heapGood, similar, _, _, _, _, _, _, _, _, _, surjective, entries⟩ := invariant
  let boundary := state.a + state.n + heapLength (state.r4 ++ state.r3)
  have atBoundary : heapAddresses (state.a + state.n)
      (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) boundary := by
    rw [head]
    simp only [List.append_assoc]
    rw [← List.append_assoc state.r4 state.r3, heapAddresses_append]
    simp [heapAddresses, boundary, heapLength_append, Nat.add_assoc]
  obtain ⟨i, defined, mapEq⟩ := surjective boundary (Or.inr atBoundary)
  cases lookup : (heapMap 0 state.heap).lookup i with
  | none => exact False.elim (defined lookup)
  | some j =>
    have jEq : j = boundary := by
      change holFapply (heapMap 0 state.heap) i = boundary at mapEq
      rw [holFapply_of_lookup lookup] at mapEq
      exact mapEq
    obtain ⟨oldXs, size, data, oldFound, newFound, parentReach, _⟩ := entries i j lookup
    subst j
    rw [heapLength_append] at allocated
    have notFinal : ¬ isFinal conf state boundary := by
      simp only [isFinal, boundary, head, heapLength, List.map_cons,
        List.sum_cons, elLength, not_or, not_and, not_lt, not_le]
      simp only [heapLength, List.map_append, List.sum_append] at allocated ⊢
      omega
    simp only [notFinal, ↓reduceIte] at newFound
    have boundaryEq : heapLength ((state.h1 ++ state.h2) ++ heapExpand state.n ++ state.r4 ++ state.r3) = boundary := by
      simp only [heapLength_append, heapLength_heapExpand]
      dsimp [boundary]
      simp only [heapLength_append]
      omega
    have atHeap := heapLookup_prefix ((state.h1 ++ state.h2) ++ heapExpand state.n ++ state.r4 ++ state.r3)
      (pending ++ state.r1) (.dataElement xs len payload)
    rw [boundaryEq] at atHeap
    have boundaryFound : heapLookup boundary
        (state.h1 ++ state.h2 ++ heapExpand state.n ++ (state.r4 ++ state.r3 ++ state.r2 ++ state.r1)) =
        some (.dataElement xs len payload) := by
      simpa [head, List.append_assoc] using atHeap
    have equalElements : HeapElement.dataElement oldXs size data = .dataElement xs len payload :=
      Option.some.inj (newFound.symm.trans boundaryFound)
    cases equalElements
    intro ptr u member
    have oldMember : .dataElement xs len payload ∈ heap0 := heapLookup_mem heap0 i _ oldFound
    have originalData : isSomeDataElement (heapLookup ptr heap0) :=
      heapGood.2.2 xs len payload ptr u ⟨oldMember, member⟩
    refine ⟨heapSimilar_data_imp_dataOrForward heap0 state.heap ptr similar originalData, ?_⟩
    obtain ⟨rootValue, root, rootMember, path⟩ := parentReach
    exact ⟨rootValue, root, rootMember, path.tail ⟨xs, len, payload, u, oldFound, member⟩⟩

/-- Moving the children of the next data object preserves the major
invariant and extends the forwarding map. -/
theorem gcInv_data_scan_move {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 xs : List (HeapAddress α))
    (len : Nat) (payload : β) (pending : List (HeapElement α β))
    (invariant : gcInv conf state heap0 roots0)
    (head : state.h2 = .dataElement xs len payload :: pending) :
    ∃ next,
      gcMoveList conf state xs = (addrMap (heapMap1 next.heap) xs, next) ∧
      (∀ ptr u, .pointer ptr u ∈ xs → (heapMap 0 next.heap).lookup ptr ≠ none) ∧
      (∀ ptr, isSomeDataOrForward (heapLookup ptr state.heap) ↔ isSomeDataOrForward (heapLookup ptr next.heap)) ∧
      (∀ i j, (heapMap 0 state.heap).lookup i = some j → (heapMap 0 next.heap).lookup i = some j) ∧
      gcInv conf next heap0 roots0 :=
  gcInv_moveList conf state heap0 roots0 xs invariant
    (gcInv_data_scan_children conf state heap0 roots0 xs len payload pending invariant head)

/-- Moving the children of the next reference object preserves the major
invariant and extends the forwarding map. -/
theorem gcInv_refs_scan_move {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 xs : List (HeapAddress α))
    (len : Nat) (payload : β) (pending : List (HeapElement α β))
    (invariant : gcInv conf state heap0 roots0)
    (head : state.r2 = .dataElement xs len payload :: pending) :
    ∃ next,
      gcMoveList conf state xs = (addrMap (heapMap1 next.heap) xs, next) ∧
      (∀ ptr u, .pointer ptr u ∈ xs → (heapMap 0 next.heap).lookup ptr ≠ none) ∧
      (∀ ptr, isSomeDataOrForward (heapLookup ptr state.heap) ↔ isSomeDataOrForward (heapLookup ptr next.heap)) ∧
      (∀ i j, (heapMap 0 state.heap).lookup i = some j → (heapMap 0 next.heap).lookup i = some j) ∧
      gcInv conf next heap0 roots0 :=
  gcInv_moveList conf state heap0 roots0 xs invariant
    (gcInv_refs_scan_children conf state heap0 roots0 xs len payload pending invariant head)

/-- Moving a scanned data object changes finality only within that object's
old interval. This is Flapjack infrastructure for the scan transition. -/
theorem isFinal_data_scan_outside {α β : Type} (conf : Config β) (state : GcState α β)
    (xs : List (HeapAddress α)) (len : Nat) (payload : β) (tail : List (HeapElement α β)) (p : Nat)
    (outside : p < heapLength state.h1 ∨ heapLength state.h1 + (len + 1) ≤ p) :
    isFinal conf { state with h1 := state.h1 ++ [.dataElement xs len payload], h2 := tail } p ↔
      isFinal conf state p := by
  simp [isFinal, heapLength, List.map_append, List.sum_append, elLength]
  simp only [heapLength] at outside
  omega

open Classical in
/-- Replacing the next copied data object's children by their relocated
addresses and moving the object to the scanned segment preserves the major
collector invariant. -/
theorem gcInv_data_scan_shift {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 xs : List (HeapAddress α))
    (len : Nat) (payload : β) (tail : List (HeapElement α β))
    (invariant : gcInv conf state heap0 roots0)
    (head : state.h2 = .dataElement xs len payload :: tail)
    (children : ∀ ptr u, .pointer ptr u ∈ xs → (heapMap 0 state.heap).lookup ptr ≠ none) :
    gcInv conf { state with h1 := state.h1 ++ [.dataElement (addrMap (heapMap1 state.heap) xs) len payload], h2 := tail } heap0 roots0 := by
  obtain ⟨allocated, balance, free, size, ok, good, similar, h1Data, h2Data,
    r1Data, r2Data, r3Data, r4Data, refs, into, injective, surjective, entries⟩ := invariant
  have tailData : ∀ h ∈ tail, isDataElement h := by
    intro h member
    exact h2Data h (by rw [head]; simp [member])
  have newData : ∀ h ∈ state.h1 ++ [.dataElement (addrMap (heapMap1 state.heap) xs) len payload], isDataElement h := by
    intro h member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact h1Data h member
    · exact ⟨_, _, _, rfl⟩
  have lengthEq : heapLength (state.h1 ++ state.h2) =
      heapLength ((state.h1 ++ [.dataElement (addrMap (heapMap1 state.heap) xs) len payload]) ++ tail) := by
    simp [head, heapLength, List.map_append, List.sum_append, elLength, Nat.add_assoc]
  have addressEq : heapAddresses 0 (state.h1 ++ state.h2) =
      heapAddresses 0 ((state.h1 ++ [.dataElement (addrMap (heapMap1 state.heap) xs) len payload]) ++ tail) := by
    rw [head]
    exact CopyingGc.heapAddresses_scan_replace state.h1 tail xs (addrMap (heapMap1 state.heap) xs) len payload
  have notFinal : ¬ isFinal conf state (heapLength state.h1) := by
    have room : heapLength state.h1 + (len + 1) ≤ state.a := by
      rw [heapLength_append, head] at allocated
      simp [heapLength, elLength] at allocated ⊢
      omega
    simp only [isFinal, not_or, not_and, not_lt, not_le]
    omega
  have newFinal : isFinal conf { state with h1 := state.h1 ++ [.dataElement (addrMap (heapMap1 state.heap) xs) len payload], h2 := tail }
      (heapLength state.h1) := by
    left
    simp [heapLength, List.map_append, List.sum_append, elLength]
  simp only [gcInv]
  refine ⟨?_, balance, free, size, ok, good, similar, newData, tailData,
    r1Data, r2Data, r3Data, r4Data, refs, ?_, injective, ?_, ?_⟩
  · exact lengthEq.symm.trans allocated
  · intro i defined
    have mapped := into i defined
    rw [← addressEq]
    exact mapped
  · intro j member
    apply surjective j
    rw [← addressEq] at member
    exact member
  · intro i j lookup
    obtain ⟨oldXs, oldLen, oldPayload, originalFound, copiedFound, reach, oldChildren⟩ := entries i j lookup
    refine ⟨oldXs, oldLen, oldPayload, originalFound, ?_, reach, ?_⟩
    · by_cases atHead : j = heapLength state.h1
      · subst j
        simp only [notFinal, ↓reduceIte] at copiedFound
        have expected := heapLookup_prefix state.h1
          (tail ++ heapExpand state.n ++ state.r4 ++ state.r3 ++ state.r2 ++ state.r1) (.dataElement xs len payload)
        have same : HeapElement.dataElement oldXs oldLen oldPayload = .dataElement xs len payload := by
          apply Option.some.inj
          exact copiedFound.symm.trans (by simpa [head, List.append_assoc] using expected)
        cases same
        have result := heapLookup_prefix state.h1
          (tail ++ heapExpand state.n ++ state.r4 ++ state.r3 ++ state.r2 ++ state.r1)
          (.dataElement (addrMap (heapMap1 state.heap) xs) len payload)
        simpa [List.append_assoc, newFinal] using result
      · have beforeOrAfter : j < heapLength state.h1 ∨ heapLength state.h1 + (len + 1) ≤ j := by
          by_cases before : j < heapLength state.h1
          · exact Or.inl before
          · right
            by_contra smaller
            have inside : j - heapLength state.h1 < len + 1 := by omega
            have nonzero : j - heapLength state.h1 ≠ 0 := by omega
            simp only [head, List.append_assoc] at copiedFound
            rw [heapLookup_append j state.h1] at copiedFound
            simp [before, heapLookup, nonzero, elLength, inside] at copiedFound
        have finalEq := isFinal_data_scan_outside conf state (addrMap (heapMap1 state.heap) xs) len payload tail j beforeOrAfter
        have same := CopyingGc.heapLookup_scan_replace_ne state.h1
          (tail ++ heapExpand state.n ++ state.r4 ++ state.r3 ++ state.r2 ++ state.r1)
          xs (addrMap (heapMap1 state.heap) xs) len payload j atHead
        have oldCopy : heapLookup j (state.h1 ++ .dataElement xs len payload ::
            (tail ++ heapExpand state.n ++ state.r4 ++ state.r3 ++ state.r2 ++ state.r1)) =
            some (.dataElement (if isFinal conf state j then addrMap (heapMap1 state.heap) oldXs else oldXs) oldLen oldPayload) := by
          simpa [head, List.append_assoc] using copiedFound
        rw [same] at oldCopy
        simpa [List.append_assoc, finalEq] using oldCopy
    · intro ptr u member final
      by_cases atHead : j = heapLength state.h1
      · subst j
        simp only [notFinal, ↓reduceIte] at copiedFound
        have expected := heapLookup_prefix state.h1
          (tail ++ heapExpand state.n ++ state.r4 ++ state.r3 ++ state.r2 ++ state.r1) (.dataElement xs len payload)
        have same : HeapElement.dataElement oldXs oldLen oldPayload = .dataElement xs len payload := by
          apply Option.some.inj
          exact copiedFound.symm.trans (by simpa [head, List.append_assoc] using expected)
        cases same
        exact children ptr u member
      · have beforeOrAfter : j < heapLength state.h1 ∨ heapLength state.h1 + (len + 1) ≤ j := by
          by_cases before : j < heapLength state.h1
          · exact Or.inl before
          · right
            by_contra smaller
            have inside : j - heapLength state.h1 < len + 1 := by omega
            have nonzero : j - heapLength state.h1 ≠ 0 := by omega
            simp only [head, List.append_assoc] at copiedFound
            rw [heapLookup_append j state.h1] at copiedFound
            simp [before, heapLookup, nonzero, elLength, inside] at copiedFound
        apply oldChildren ptr u member
        exact (isFinal_data_scan_outside conf state (addrMap (heapMap1 state.heap) xs) len payload tail j beforeOrAfter).mp final

/-- Moving the next data object's children and transferring that object into
the scanned segment preserves the major invariant. -/
theorem gcInv_data_scan_step {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 xs : List (HeapAddress α))
    (len : Nat) (payload : β) (tail : List (HeapElement α β))
    (invariant : gcInv conf state heap0 roots0)
    (head : state.h2 = .dataElement xs len payload :: tail) :
    ∃ next,
      gcMoveList conf state xs = (addrMap (heapMap1 next.heap) xs, next) ∧
      (∀ i j, (heapMap 0 state.heap).lookup i = some j → (heapMap 0 next.heap).lookup i = some j) ∧
      gcInv conf { next with h1 := next.h1 ++ [.dataElement (addrMap (heapMap1 next.heap) xs) len payload], h2 := next.h2.drop 1 } heap0 roots0 := by
  obtain ⟨next, run, children, _, submap, nextInv⟩ :=
    gcInv_data_scan_move conf state heap0 roots0 xs len payload tail invariant head
  have nextOk : next.ok = true := nextInv.2.2.2.2.1
  obtain ⟨added, _, prefixEq, _, _⟩ :=
    DataToWord.Proofs.Gc.gcMoveList_withNilLemma conf xs (addrMap (heapMap1 next.heap) xs) state next run nextOk
  have nextHead : next.h2 = .dataElement xs len payload :: (tail ++ added) := by
    simpa [head] using prefixEq
  have shifted := gcInv_data_scan_shift conf next heap0 roots0 xs len payload (tail ++ added) nextInv nextHead children
  refine ⟨next, run, submap, ?_⟩
  simpa [nextHead] using shifted

/-- The data scan preserves the major collector invariant and all prior
forwarding entries, and empties the pending data segment. This is stated for
the untagged source-shaped invariant above. -/
theorem gcInv_moveData {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α)) :
    gcInv conf state heap0 roots0 → state.r3 = [] → state.r2 = [] →
    (∀ i j, (heapMap 0 state.heap).lookup i = some j →
      (heapMap 0 (gcMoveData conf state).heap).lookup i = some j) ∧
    gcInv conf (gcMoveData conf state) heap0 roots0 ∧
    (gcMoveData conf state).h2 = [] ∧ (gcMoveData conf state).r3 = [] ∧
    (gcMoveData conf state).r2 = [] := by
  classical
  induction state using gcMoveData.induct conf with
  | case1 state empty =>
    intro invariant r3 r2
    rw [gcMoveData]
    simp [empty, invariant, r3, r2]
  | case2 state head tail heap over =>
    intro invariant _ _
    have allocated := invariant.1
    have balance := invariant.2.1
    rw [heap] at allocated
    omega
  | case3 state tail roots len payload roots1 middle move heap bounded flag ih =>
    intro invariant r3 r2
    obtain ⟨next, run, submap, shifted⟩ :=
      gcInv_data_scan_step conf state heap0 roots0 roots len payload tail invariant heap
    have same : middle = next := by
      rw [move] at run
      exact (Prod.mk.inj run).2
    subst middle
    have rootsEq : roots1 = addrMap (heapMap1 next.heap) roots := by
      rw [move] at run
      exact (Prod.mk.inj run).1
    subst roots1
    obtain ⟨added, _, prefixEq, _, _⟩ :=
      DataToWord.Proofs.Gc.gcMoveList_withNilLemma conf roots (addrMap (heapMap1 next.heap) roots) state next run shifted.2.2.2.2.1
    have nextHead : next.h2 = .dataElement roots len payload :: (tail ++ added) := by
      simpa [heap] using prefixEq
    have refs := DataToWord.Proofs.Memory.gcMoveList_refsUnchanged conf state roots
    rw [run] at refs
    have nextOk : next.ok = true := shifted.2.2.2.2.1
    have flagTrue : flag = true := by
      dsimp only [flag]
      simp [nextOk, nextHead]
    have recursive := ih (by simpa [flagTrue, nextOk] using shifted) (by simpa using refs.2.2.trans r3)
      (by simpa using refs.2.1.trans r2)
    rw [gcMoveData]
    simp only [heap, bounded, ↓reduceIte, move]
    simp only [flagTrue] at recursive
    have composed := And.intro (fun i j old => recursive.1 i j (submap i j old)) recursive.2
    simpa [nextOk, nextHead] using composed
  | case4 state head tail heap bounded notData =>
    intro invariant _ _
    have data := invariant.2.2.2.2.2.2.2.2.1 head (by simp [heap])
    cases head with
    | unused len => simp [isDataElement] at data
    | forwardPointer ptr value len => simp [isDataElement] at data
    | dataElement roots len payload => exact False.elim (notData roots len payload rfl)

/-- Scanning a reference object changes finality only within its own
interval. -/
theorem isFinal_refs_scan_outside {α β : Type} (conf : Config β) (state : GcState α β)
    (xs oldXs : List (HeapAddress α)) (len : Nat) (payload : β) (tail : List (HeapElement α β)) (p : Nat)
    (head : state.r2 = .dataElement oldXs len payload :: tail)
    (outside : p < state.a + state.n + heapLength (state.r4 ++ state.r3) ∨
      state.a + state.n + heapLength (state.r4 ++ state.r3) + (len + 1) ≤ p) :
    isFinal conf { state with r3 := state.r3 ++ [.dataElement xs len payload], r2 := tail } p ↔
      isFinal conf state p := by
  simp only [isFinal, head, heapLength, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, elLength] at outside ⊢
  omega

open Classical in
/-- Relocating the next reference object's children and transferring it to
the scanned reference segment preserves the major collector invariant. -/
theorem gcInv_refs_scan_shift {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 xs : List (HeapAddress α))
    (len : Nat) (payload : β) (tail : List (HeapElement α β))
    (invariant : gcInv conf state heap0 roots0)
    (head : state.r2 = .dataElement xs len payload :: tail)
    (children : ∀ ptr u, .pointer ptr u ∈ xs → (heapMap 0 state.heap).lookup ptr ≠ none) :
    gcInv conf { state with r3 := state.r3 ++ [.dataElement (addrMap (heapMap1 state.heap) xs) len payload], r2 := tail } heap0 roots0 := by
  obtain ⟨allocated, balance, free, size, ok, good, similar, h1Data, h2Data,
    r1Data, r2Data, r3Data, r4Data, refs, into, injective, surjective, entries⟩ := invariant
  let mapped := addrMap (heapMap1 state.heap) xs
  let boundary := state.a + state.n + heapLength (state.r4 ++ state.r3)
  have tailData : ∀ h ∈ tail, isDataElement h := by
    intro h member
    exact r2Data h (by rw [head]; simp [member])
  have newData : ∀ h ∈ state.r3 ++ [.dataElement mapped len payload], isDataElement h := by
    intro h member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact r3Data h member
    · exact ⟨_, _, _, rfl⟩
  have refTag : conf.isRef payload = true := refs xs len payload (by simp [head])
  have refsEq : heapAddresses (state.a + state.n) (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) =
      heapAddresses (state.a + state.n) (state.r4 ++ (state.r3 ++ [.dataElement mapped len payload]) ++ tail ++ state.r1) := by
    rw [head]
    simp only [List.append_assoc, heapAddresses_append]
    funext j
    simp [heapAddresses, heapLength, elLength, Nat.add_assoc, or_assoc]
  have notFinal : ¬ isFinal conf state boundary := by
    simp only [heapLength, List.map_append, List.sum_append] at allocated
    simp only [isFinal, boundary, head, heapLength, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, elLength, not_or, not_and, not_lt, not_le]
    omega
  have newFinal : isFinal conf { state with r3 := state.r3 ++ [.dataElement mapped len payload], r2 := tail } boundary := by
    simp only [isFinal, boundary, heapLength, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, elLength]
    omega
  have prefixLength : heapLength ((state.h1 ++ state.h2) ++ heapExpand state.n ++ state.r4 ++ state.r3) = boundary := by
    simp only [heapLength_append, heapLength_heapExpand]
    dsimp [boundary]
    simp only [heapLength_append] at allocated ⊢
    omega
  simp only [gcInv]
  refine ⟨allocated, ?_, free, size, ok, good, similar, h1Data, h2Data,
    r1Data, tailData, newData, r4Data, ?_, ?_, injective, ?_, ?_⟩
  · simpa [head, heapLength, List.map_append, List.sum_append, elLength, Nat.add_assoc] using balance
  · intro ys n d member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with ((old | old) | old) | old
    · exact refs ys n d (by simp [old])
    · rcases old with old | same
      · exact refs ys n d (by simp [old])
      · cases same
        exact refTag
    · exact refs ys n d (by simp [head, old])
    · exact refs ys n d (by simp [old])
  · intro i defined
    have result := into i defined
    rw [← refsEq]
    exact result
  · intro j member
    apply surjective j
    rw [← refsEq] at member
    exact member
  · intro i j lookup
    obtain ⟨oldXs, oldLen, oldPayload, originalFound, copiedFound, reach, oldChildren⟩ := entries i j lookup
    refine ⟨oldXs, oldLen, oldPayload, originalFound, ?_, reach, ?_⟩
    · by_cases atHead : j = boundary
      · subst j
        simp only [notFinal, ↓reduceIte] at copiedFound
        have expected := heapLookup_prefix ((state.h1 ++ state.h2) ++ heapExpand state.n ++ state.r4 ++ state.r3)
          (tail ++ state.r1) (.dataElement xs len payload)
        rw [prefixLength] at expected
        have same : HeapElement.dataElement oldXs oldLen oldPayload = .dataElement xs len payload := by
          apply Option.some.inj
          exact copiedFound.symm.trans (by simpa [head, List.append_assoc] using expected)
        cases same
        have result := heapLookup_prefix ((state.h1 ++ state.h2) ++ heapExpand state.n ++ state.r4 ++ state.r3)
          (tail ++ state.r1) (.dataElement mapped len payload)
        rw [prefixLength] at result
        simpa [List.append_assoc, newFinal, mapped] using result
      · have beforeOrAfter : j < boundary ∨ boundary + (len + 1) ≤ j := by
          by_cases before : j < boundary
          · exact Or.inl before
          · right
            by_contra smaller
            have inside : j - boundary < len + 1 := by omega
            have nonzero : j - boundary ≠ 0 := by omega
            have copy := copiedFound
            simp only [head, List.append_assoc] at copy
            have rearranged : heapLookup j (((state.h1 ++ state.h2) ++ heapExpand state.n ++ state.r4 ++ state.r3) ++
                .dataElement xs len payload :: (tail ++ state.r1)) =
                some (.dataElement (if isFinal conf state j then addrMap (heapMap1 state.heap) oldXs else oldXs) oldLen oldPayload) := by
              simpa [List.append_assoc] using copy
            rw [heapLookup_append j, prefixLength] at rearranged
            simp [before, heapLookup, nonzero, elLength, inside] at rearranged
        have finalEq := isFinal_refs_scan_outside conf state mapped xs len payload tail j head (by simpa [boundary] using beforeOrAfter)
        have same := CopyingGc.heapLookup_scan_replace_ne
          ((state.h1 ++ state.h2) ++ heapExpand state.n ++ state.r4 ++ state.r3)
          (tail ++ state.r1) xs mapped len payload j (by rw [prefixLength]; exact atHead)
        have oldCopy : heapLookup j (((state.h1 ++ state.h2) ++ heapExpand state.n ++ state.r4 ++ state.r3) ++
            .dataElement xs len payload :: (tail ++ state.r1)) =
            some (.dataElement (if isFinal conf state j then addrMap (heapMap1 state.heap) oldXs else oldXs) oldLen oldPayload) := by
          simpa [head, List.append_assoc] using copiedFound
        rw [same] at oldCopy
        simpa [List.append_assoc, finalEq, mapped] using oldCopy
    · intro ptr u member final
      by_cases atHead : j = boundary
      · subst j
        simp only [notFinal, ↓reduceIte] at copiedFound
        have expected := heapLookup_prefix ((state.h1 ++ state.h2) ++ heapExpand state.n ++ state.r4 ++ state.r3)
          (tail ++ state.r1) (.dataElement xs len payload)
        rw [prefixLength] at expected
        have same : HeapElement.dataElement oldXs oldLen oldPayload = .dataElement xs len payload := by
          apply Option.some.inj
          exact copiedFound.symm.trans (by simpa [head, List.append_assoc] using expected)
        cases same
        exact children ptr u member
      · have beforeOrAfter : j < boundary ∨ boundary + (len + 1) ≤ j := by
          by_cases before : j < boundary
          · exact Or.inl before
          · right
            by_contra smaller
            have inside : j - boundary < len + 1 := by omega
            have nonzero : j - boundary ≠ 0 := by omega
            have copy := copiedFound
            simp only [head, List.append_assoc] at copy
            have rearranged : heapLookup j (((state.h1 ++ state.h2) ++ heapExpand state.n ++ state.r4 ++ state.r3) ++
                .dataElement xs len payload :: (tail ++ state.r1)) =
                some (.dataElement (if isFinal conf state j then addrMap (heapMap1 state.heap) oldXs else oldXs) oldLen oldPayload) := by
              simpa [List.append_assoc] using copy
            rw [heapLookup_append j, prefixLength] at rearranged
            simp [before, heapLookup, nonzero, elLength, inside] at rearranged
        apply oldChildren ptr u member
        exact (isFinal_refs_scan_outside conf state mapped xs len payload tail j head (by simpa [boundary] using beforeOrAfter)).mp final

/-- Traversing a reference object's children and moving it into the scanned
reference segment preserves the major invariant. -/
theorem gcInv_refs_scan_step {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 xs : List (HeapAddress α))
    (len : Nat) (payload : β) (tail : List (HeapElement α β))
    (invariant : gcInv conf state heap0 roots0)
    (head : state.r2 = .dataElement xs len payload :: tail) :
    ∃ next,
      gcMoveList conf state xs = (addrMap (heapMap1 next.heap) xs, next) ∧
      (∀ i j, (heapMap 0 state.heap).lookup i = some j → (heapMap 0 next.heap).lookup i = some j) ∧
      gcInv conf { next with r3 := next.r3 ++ [.dataElement (addrMap (heapMap1 next.heap) xs) len payload], r2 := tail } heap0 roots0 := by
  obtain ⟨next, run, children, _, submap, nextInv⟩ :=
    gcInv_refs_scan_move conf state heap0 roots0 xs len payload tail invariant head
  have refs := DataToWord.Proofs.Memory.gcMoveList_refsUnchanged conf state xs
  rw [run] at refs
  have nextHead : next.r2 = .dataElement xs len payload :: tail := refs.2.1.trans head
  exact ⟨next, run, submap, gcInv_refs_scan_shift conf next heap0 roots0 xs len payload tail nextInv nextHead children⟩

/-- The reference scan preserves the major invariant and prior forwarding
entries, empties both scanned and pending reference segments, and makes
progress when the scanned segment was already nonempty. -/
theorem gcInv_moveRefs {α β : Type} (conf : Config β) (state : GcState α β)
    (heap0 : List (HeapElement α β)) (roots0 : List (HeapAddress α)) :
    gcInv conf state heap0 roots0 →
    (∀ i j, (heapMap 0 state.heap).lookup i = some j →
      (heapMap 0 (gcMoveRefs conf state).heap).lookup i = some j) ∧
    gcInv conf (gcMoveRefs conf state) heap0 roots0 ∧
    (gcMoveRefs conf state).r3 = [] ∧ (gcMoveRefs conf state).r2 = [] ∧
    (0 < heapLength state.r3 → heapLength state.r1 < heapLength (gcMoveRefs conf state).r1) := by
  classical
  induction state using gcMoveRefs.induct conf with
  | case1 state empty =>
    intro invariant
    have finished := gcInv_refs_finish conf state heap0 roots0 invariant empty
    have unfold : gcMoveRefs conf state = { state with r3 := [], r1 := state.r3 ++ state.r1 } := by
      cases state with
      | mk old h1 h2 r4 r3 r2 r1 a n status origHeap origHeap0 =>
        simp only at empty
        subst r2
        rw [gcMoveRefs]
    rw [unfold]
    refine ⟨?_, finished, rfl, empty, ?_⟩
    · intros; assumption
    · intro positive
      simp only [heapLength_append]
      omega
  | case2 state tail roots len payload heap roots1 middle move heapAgain ih =>
    intro invariant
    obtain ⟨next, run, submap, shifted⟩ :=
      gcInv_refs_scan_step conf state heap0 roots0 roots len payload tail invariant heap
    have same : middle = next := by
      rw [move] at run
      exact (Prod.mk.inj run).2
    subst middle
    have rootsEq : roots1 = addrMap (heapMap1 next.heap) roots := by
      rw [move] at run
      exact (Prod.mk.inj run).1
    subst roots1
    have refs := DataToWord.Proofs.Memory.gcMoveList_refsUnchanged conf state roots
    rw [run] at refs
    have recursive := ih shifted
    have unfold : gcMoveRefs conf state = gcMoveRefs conf
        { next with r2 := tail, r3 := next.r3 ++ [.dataElement (addrMap (heapMap1 next.heap) roots) len payload] } := by
      cases state with
      | mk old h1 h2 r4 r3 r2 r1 a n status origHeap origHeap0 =>
        simp only at heap
        subst r2
        rw [gcMoveRefs]
        simp only [move]
    rw [unfold]
    refine ⟨fun i j old => recursive.1 i j (submap i j old), recursive.2.1,
      recursive.2.2.1, recursive.2.2.2.1, ?_⟩
    intro positive
    have longer := recursive.2.2.2.2 (by
      change 0 < heapLength (next.r3 ++ [.dataElement (addrMap (heapMap1 next.heap) roots) len payload])
      simp only [heapLength, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, elLength]
      omega)
    have r1Eq : next.r1 = state.r1 := refs.1
    simpa only [r1Eq] using longer
  | case3 state head tail heap refsAgain notData =>
    intro invariant
    have data := invariant.2.2.2.2.2.2.2.2.2.2.1 head (by simp [heap])
    cases head with
    | unused len => simp [isDataElement] at data
    | forwardPointer ptr value len => simp [isDataElement] at data
    | dataElement roots len payload => exact False.elim (notData roots len payload heap rfl (by rfl))

end Flapjack.Compiler.Backend.GenGc
