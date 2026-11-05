import Flapjack.Compiler.Backend.CopyingGc
import Flapjack.Compiler.Backend.GcShared.HeapSimilarity
import Flapjack.Compiler.Backend.GcShared.Reachability
import Flapjack.Compiler.Backend.GcShared.Related
import Flapjack.Compiler.Backend.GcShared.ForwardPtr
import Flapjack.Compiler.Backend.CopyingGc.Proofs.Append

/-! Abstract invariant for the copying collector. -/
namespace Flapjack.Compiler.Backend.CopyingGc

/-- The source-shaped copying collector invariant. This proof-side definition
uses the canonical finite map internally; it remains untagged until the
representation qualifier can record that internal use. -/
def gcInv {α β : Type}
    (h1 h2 : List (HeapElement α β)) (a n : Nat) (heap : List (HeapElement α β))
    (ok : Bool) (limit : Nat) (heap0 : List (HeapElement α β))
    (roots0 : List (HeapAddress α)) : Prop :=
  let f := heapMap 0 heap
  let target := heapAddresses 0 (h1 ++ h2)
  a + n = limit ∧ a = heapLength (h1 ++ h2) ∧
  n = heapLength (heap.filter (fun h => !(isForwardPointer h))) ∧ ok = true ∧
  heapLength heap = limit ∧ heapOk heap0 limit ∧ heapsSimilar heap0 heap ∧
  (∀ h ∈ h1, isDataElement h) ∧ (∀ h ∈ h2, isDataElement h) ∧
  (∀ i, f.lookup i ≠ none → target (heapMap1 heap i)) ∧
  (∀ i j, f.lookup i ≠ none → f.lookup j ≠ none → heapMap1 heap i = heapMap1 heap j → i = j) ∧
  (∀ j, target j → ∃ i, f.lookup i ≠ none ∧ heapMap1 heap i = j) ∧
  ∀ i j, f.lookup i = some j →
    ∃ xs len data, heapLookup i heap0 = some (.dataElement xs len data) ∧
      heapLookup j (h1 ++ h2) = some (.dataElement
        (if j < heapLength h1 then addrMap (heapMap1 heap) xs else xs) len data) ∧
      reachableAddresses roots0 heap0 i ∧
      ∀ ptr value, .pointer ptr value ∈ xs → j < heapLength h1 → f.lookup ptr ≠ none

/-- The empty initial copying state satisfies the invariant exactly when the
initial heap is well formed. This is a Flapjack proof about `gcInv`, which is
not yet tagged as the original HOL definition. -/
theorem gcInv_init {α β : Type} (heap : List (HeapElement α β))
    (roots : List (HeapAddress α)) (limit : Nat) :
    gcInv [] [] 0 limit heap true limit heap roots ↔ heapOk heap limit := by
  constructor
  · intro invariant
    exact invariant.2.2.2.2.2.1
  · intro good
    have noForward := good.2.1
    have emptyMap : ∀ key, (heapMap 0 heap).lookup key = none := by
      intro key
      have domainEq := congrFun (heapMap_empty heap 0 noForward) key
      by_cases lookup : (heapMap 0 heap).lookup key = none
      · exact lookup
      · exact False.elim (domainEq.mp lookup)
    have filtered := filter_notForward heap noForward
    have similar := heapsSimilar_refl heap noForward
    have lengthEq : (heap.map elLength).sum = limit := good.1
    simp [gcInv, heapAddresses, heapLength, filtered, similar, emptyMap, good, lengthEq]

/-- The data-root case of the copying collector's move-invariant proof. -/
theorem gcInv_move_data {α β : Type} (h1 h2 heap heap0 : List (HeapElement α β))
    (a n limit : Nat) (ok : Bool) (roots0 : List (HeapAddress α)) (value : α)
    (invariant : gcInv h1 h2 a n heap ok limit heap0 roots0) :
    gcMove (.data value, h2, a, n, heap, ok, limit) =
      (addrApply (heapMap1 heap) (.data value), h2, a, n, heap, ok) ∧
    (∀ ptr u, HeapAddress.data value = .pointer ptr u → (heapMap 0 heap).lookup ptr ≠ none) ∧
    (∀ ptr, isSomeDataOrForward (heapLookup ptr heap) ↔ isSomeDataOrForward (heapLookup ptr heap)) ∧
    (∀ i j, (heapMap 0 heap).lookup i = some j → (heapMap 0 heap).lookup i = some j) ∧
    gcInv h1 h2 a n heap ok limit heap0 roots0 := by
  simp [gcMove, addrApply, invariant]

/-- The already-forwarded root case of the copying collector's move-invariant
proof. The found forwarding pointer supplies the domain fact and map value. -/
theorem gcInv_move_forward {α β : Type} (h1 h2 heap heap0 : List (HeapElement α β))
    (a n limit ptr target len : Nat) (ok : Bool) (roots0 : List (HeapAddress α))
    (value forwardedValue : α)
    (invariant : gcInv h1 h2 a n heap ok limit heap0 roots0)
    (found : heapLookup ptr heap = some (.forwardPointer target forwardedValue len)) :
    gcMove (.pointer ptr value, h2, a, n, heap, ok, limit) =
      (addrApply (heapMap1 heap) (.pointer ptr value), h2, a, n, heap, ok) ∧
    (∀ p u, HeapAddress.pointer ptr value = .pointer p u → (heapMap 0 heap).lookup p ≠ none) ∧
    (∀ p, isSomeDataOrForward (heapLookup p heap) ↔ isSomeDataOrForward (heapLookup p heap)) ∧
    (∀ i j, (heapMap 0 heap).lookup i = some j → (heapMap 0 heap).lookup i = some j) ∧
    gcInv h1 h2 a n heap ok limit heap0 roots0 := by
  have lookup := heapLookup_flookup heap ptr target len forwardedValue found
  have applyEq : heapMap1 heap ptr = target := holFapply_of_lookup lookup
  simp [gcMove, found, addrApply, applyEq, lookup, invariant]

/-- The fresh-copy forwarding update extends the old map without altering
any existing entry. This is a Flapjack proof step for the data-root case. -/
theorem heapMap_forward_submap {α β : Type} (before after : List (HeapElement α β))
    (roots : List (HeapAddress α)) (len target : Nat) (data : β) (value : α)
    (key mapped : Nat)
    (old : (heapMap 0 (before ++ .dataElement roots len data :: after)).lookup key = some mapped) :
    (heapMap 0 (before ++ .forwardPointer target value len :: after)).lookup key = some mapped := by
  have absent := not_in_heapMap before after roots len data
  have ne : heapLength before ≠ key := by
    intro eq
    subst key
    rw [absent] at old
    contradiction
  rw [heapMap_replace_data before after target len roots data value]
  simp [HolFiniteMapExact.lookup_update, FUPDATE, ne, old]

/-- Fresh forwarding leaves the total map application unchanged at every
address already present in its domain. This is a Flapjack proof step for
preserving previously copied entries. -/
theorem heapMap1_forward_old {α β : Type} (before after : List (HeapElement α β))
    (roots : List (HeapAddress α)) (len target : Nat) (data : β) (value : α) (key : Nat)
    (defined : (heapMap 0 (before ++ .dataElement roots len data :: after)).lookup key ≠ none) :
    heapMap1 (before ++ .forwardPointer target value len :: after) key =
      heapMap1 (before ++ .dataElement roots len data :: after) key := by
  cases found : (heapMap 0 (before ++ .dataElement roots len data :: after)).lookup key with
  | none => exact False.elim (defined found)
  | some mapped =>
    have next := heapMap_forward_submap before after roots len target data value key mapped found
    change holFapply (heapMap 0 (before ++ .forwardPointer target value len :: after)) key =
      holFapply (heapMap 0 (before ++ .dataElement roots len data :: after)) key
    rw [holFapply_of_lookup next, holFapply_of_lookup found]

/-- The fresh-data branch successfully installs the forwarding pointer,
preserves previous map entries and preserves data-or-forward lookup status.
This is a Flapjack proof step toward the complete move invariant. -/
theorem gcInv_move_fresh_core {α β : Type} (h1 h2 heap heap0 : List (HeapElement α β))
    (a n limit ptr len : Nat) (ok : Bool) (roots0 ys : List (HeapAddress α))
    (value : α) (data : β)
    (invariant : gcInv h1 h2 a n heap ok limit heap0 roots0)
    (found : heapLookup ptr heap = some (.dataElement ys len data)) :
    ∃ before after,
      heap = before ++ .dataElement ys len data :: after ∧ ptr = heapLength before ∧
      gcMove (.pointer ptr value, h2, a, n, heap, ok, limit) =
        (.pointer a value, h2 ++ [.dataElement ys len data], a + (len + 1), n - (len + 1),
          before ++ .forwardPointer a value len :: after, true) ∧
      (∀ p, isSomeDataOrForward (heapLookup p heap) ↔
        isSomeDataOrForward (heapLookup p (before ++ .forwardPointer a value len :: after))) ∧
      (∀ i j, (heapMap 0 heap).lookup i = some j →
        (heapMap 0 (before ++ .forwardPointer a value len :: after)).lookup i = some j) := by
  obtain ⟨before, after, heapEq, ptrEq⟩ := heapLookup_split heap ptr _ found
  have spaceEq := invariant.2.2.1
  have limitEq := invariant.1
  have okEq := invariant.2.2.2.1
  rw [heapEq] at spaceEq
  have enough : len + 1 ≤ n := by
    simp [List.filter_append, isForwardPointer, heapLength, elLength,
      List.map_append, List.sum_append] at spaceEq
    omega
  refine ⟨before, after, heapEq, ptrEq, ?_, ?_, ?_⟩
  · rw [heapEq, ptrEq]
    have atData : heapLookup (heapLength before) (before ++ .dataElement ys len data :: after) =
        some (.dataElement ys len data) := by simpa [heapEq, ptrEq] using found
    simp [gcMove, atData, enough, limitEq, okEq, gcForwardPtr_thm]
  · intro p
    rw [heapEq]
    simpa using isSomeDataOrForward_replace before after p a len ys data value
  · intro i j old
    rw [heapEq] at old
    exact heapMap_forward_submap before after ys len a data value i j old

/-- Reconstruct the size, free-space, heap similarity, and data-element
components of the fresh-copy post-state. This isolates part of the remaining
copying collector move proof; the map bijection and lookup clauses are not
assumed or concluded here. -/
theorem gcInv_move_fresh_structure {α β : Type}
    (h1 h2 before after heap0 : List (HeapElement α β)) (a n limit len : Nat)
    (roots0 ys : List (HeapAddress α)) (value : α) (data : β) (ok : Bool)
    (invariant : gcInv h1 h2 a n (before ++ .dataElement ys len data :: after) ok limit heap0 roots0) :
    (a + (len + 1)) + (n - (len + 1)) = limit ∧
    a + (len + 1) = heapLength (h1 ++ (h2 ++ [.dataElement ys len data])) ∧
    n - (len + 1) = heapLength ((before ++ .forwardPointer a value len :: after).filter
      (fun h => !(isForwardPointer h))) ∧
    heapLength (before ++ .forwardPointer a value len :: after) = limit ∧
    heapsSimilar heap0 (before ++ .forwardPointer a value len :: after) ∧
    (∀ h ∈ h1, isDataElement h) ∧
    (∀ h ∈ h2 ++ [.dataElement ys len data], isDataElement h) := by
  obtain ⟨balance, allocated, free, _, heapSize, _, similar, h1Data, h2Data, _⟩ := invariant
  have enough : len + 1 ≤ n := by
    simp [List.filter_append, isForwardPointer, heapLength, elLength,
      List.map_append, List.sum_append] at free
    omega
  refine ⟨by omega, ?_, ?_, ?_, ?_, h1Data, ?_⟩
  · simp [heapLength, List.map_append, List.sum_append, elLength] at allocated ⊢
    omega
  · simp [List.filter_append, isForwardPointer, heapLength, elLength,
      List.map_append, List.sum_append] at free ⊢
    omega
  · simpa [heapLength, List.map_append, List.sum_append, elLength] using heapSize
  · simpa [← allocated] using heapsSimilar_forward before heap0 after h1 h2 ys len data value similar
  · intro h member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact h2Data h member
    · exact ⟨ys, len, data, rfl⟩

/-- Appending an element adds exactly its starting address to the heap's
address set. -/
@[hol "cakeml/compiler/backend/gc/copying_gcScript.sml" "heap_addresses_SNOC"]
theorem heapAddresses_snoc {α β : Type} (xs : List (HeapElement α β))
    (n : Nat) (x : HeapElement α β) :
    heapAddresses n (xs ++ [x]) =
      (fun p => heapAddresses n xs p ∨ p = heapLength xs + n) := by
  rw [heapAddresses_append]
  funext p
  simp [heapAddresses, Nat.add_comm]

/-- The address immediately after a heap is fresh. This Flapjack proof step
follows from the source heap-address upper bound. -/
theorem heapAddresses_end_fresh {α β : Type} (xs : List (HeapElement α β)) :
    ¬heapAddresses 0 xs (heapLength xs) := by
  intro member
  have bound := heapAddresses_less_heapLength xs 0 (heapLength xs) member
  simp at bound

/-- Adding a fresh key and a fresh target extends a finite-map bijection by
one pair. This Flapjack lemma supplies the copying collector's update step. -/
theorem finiteMap_bij_insert (f : HolFiniteMapExact Nat Nat) (targets : Nat → Prop)
    (source target : Nat) (sourceFresh : f.lookup source = none) (targetFresh : ¬ targets target)
    (mapsInto : ∀ i, f.lookup i ≠ none → targets (holFapply f i))
    (injective : ∀ i j, f.lookup i ≠ none → f.lookup j ≠ none →
      holFapply f i = holFapply f j → i = j)
    (surjective : ∀ j, targets j → ∃ i, f.lookup i ≠ none ∧ holFapply f i = j) :
    (∀ i, (f.update (source, target)).lookup i ≠ none →
      targets (holFapply (f.update (source, target)) i) ∨ holFapply (f.update (source, target)) i = target) ∧
    (∀ i j, (f.update (source, target)).lookup i ≠ none →
      (f.update (source, target)).lookup j ≠ none →
      holFapply (f.update (source, target)) i = holFapply (f.update (source, target)) j → i = j) ∧
    (∀ j, targets j ∨ j = target →
      ∃ i, (f.update (source, target)).lookup i ≠ none ∧ holFapply (f.update (source, target)) i = j) := by
  have lookupAt : (f.update (source, target)).lookup source = some target := by
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have applyAt : holFapply (f.update (source, target)) source = target := holFapply_of_lookup lookupAt
  have lookupOther : ∀ i, i ≠ source → (f.update (source, target)).lookup i = f.lookup i := by
    intro i ne
    simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm ne]
  have applyOther : ∀ i, i ≠ source → holFapply (f.update (source, target)) i = holFapply f i := by
    intro i ne
    unfold holFapply
    rw [lookupOther i ne]
  refine ⟨?_, ?_, ?_⟩
  · intro i defined
    by_cases eq : i = source
    · subst i
      exact Or.inr applyAt
    · left
      rw [applyOther i eq]
      rw [lookupOther i eq] at defined
      exact mapsInto i defined
  · intro i j di dj same
    by_cases ei : i = source
    · subst i
      by_cases ej : j = source
      · exact ej.symm
      · have oldj : f.lookup j ≠ none := by rwa [lookupOther j ej] at dj
        have image := mapsInto j oldj
        rw [applyAt, applyOther j ej] at same
        exact False.elim (targetFresh (same ▸ image))
    · by_cases ej : j = source
      · subst j
        have oldi : f.lookup i ≠ none := by rwa [lookupOther i ei] at di
        have image := mapsInto i oldi
        rw [applyOther i ei, applyAt] at same
        exact False.elim (targetFresh (same ▸ image))
      · apply injective i j
        · rwa [lookupOther i ei] at di
        · rwa [lookupOther j ej] at dj
        · simpa [applyOther i ei, applyOther j ej] using same
  · intro j member
    rcases member with member | rfl
    · obtain ⟨i, defined, eq⟩ := surjective j member
      have ne : i ≠ source := by
        intro same
        subst i
        exact defined sourceFresh
      exact ⟨i, by rw [lookupOther i ne]; exact defined, by rw [applyOther i ne]; exact eq⟩
    · exact ⟨source, by rw [lookupAt]; simp, applyAt⟩

/-- The fresh-copy step extends the invariant's forwarding-map bijection to
the newly appended copied element. This is a Flapjack proof step toward the
complete copying collector move invariant. -/
theorem gcInv_move_fresh_bij {α β : Type}
    (h1 h2 before after heap0 : List (HeapElement α β)) (a n limit len : Nat)
    (roots0 ys : List (HeapAddress α)) (value : α) (data : β) (ok : Bool)
    (invariant : gcInv h1 h2 a n (before ++ .dataElement ys len data :: after) ok limit heap0 roots0) :
    (∀ i, (heapMap 0 (before ++ .forwardPointer a value len :: after)).lookup i ≠ none →
      heapAddresses 0 (h1 ++ (h2 ++ [.dataElement ys len data]))
        (heapMap1 (before ++ .forwardPointer a value len :: after) i)) ∧
    (∀ i j, (heapMap 0 (before ++ .forwardPointer a value len :: after)).lookup i ≠ none →
      (heapMap 0 (before ++ .forwardPointer a value len :: after)).lookup j ≠ none →
      heapMap1 (before ++ .forwardPointer a value len :: after) i =
        heapMap1 (before ++ .forwardPointer a value len :: after) j → i = j) ∧
    (∀ j, heapAddresses 0 (h1 ++ (h2 ++ [.dataElement ys len data])) j →
      ∃ i, (heapMap 0 (before ++ .forwardPointer a value len :: after)).lookup i ≠ none ∧
        heapMap1 (before ++ .forwardPointer a value len :: after) i = j) := by
  obtain ⟨_, allocated, _, _, _, _, _, _, _, mapsInto, injective, surjective, _⟩ := invariant
  have sourceFresh := not_in_heapMap before after ys len data
  have targetFresh : ¬heapAddresses 0 (h1 ++ h2) a := by
    rw [allocated]
    exact heapAddresses_end_fresh (h1 ++ h2)
  have targetEq : heapAddresses 0 (h1 ++ (h2 ++ [.dataElement ys len data])) =
      (fun p => heapAddresses 0 (h1 ++ h2) p ∨ p = a) := by
    rw [← List.append_assoc, heapAddresses_snoc]
    simp [← allocated]
  have newMap := heapMap_replace_data before after a len ys data value
  have bij := finiteMap_bij_insert (heapMap 0 (before ++ .dataElement ys len data :: after))
    (heapAddresses 0 (h1 ++ h2)) (heapLength before) a sourceFresh targetFresh
    mapsInto injective surjective
  simpa only [heapMap1, newMap, targetEq] using bij

/-- The new forwarding entry satisfies the original-heap lookup,
copied-heap lookup, and reachability parts of the move invariant. This is the
new-entry case of the copying collector proof. -/
theorem gcInv_move_fresh_new_entry {α β : Type}
    (h1 h2 before after heap0 : List (HeapElement α β)) (a n limit len : Nat)
    (roots0 ys : List (HeapAddress α)) (value : α) (data : β) (ok : Bool)
    (invariant : gcInv h1 h2 a n (before ++ .dataElement ys len data :: after) ok limit heap0 roots0)
    (reachable : reachableAddresses roots0 heap0 (heapLength before)) :
    (heapMap 0 (before ++ .forwardPointer a value len :: after)).lookup (heapLength before) = some a ∧
    ∃ xs size payload,
      heapLookup (heapLength before) heap0 = some (.dataElement xs size payload) ∧
      heapLookup a (h1 ++ (h2 ++ [.dataElement ys len data])) = some (.dataElement
        (if a < heapLength h1 then
          addrMap (heapMap1 (before ++ .forwardPointer a value len :: after)) xs else xs) size payload) ∧
      reachableAddresses roots0 heap0 (heapLength before) ∧
      ∀ ptr u, .pointer ptr u ∈ xs → a < heapLength h1 →
        (heapMap 0 (before ++ .forwardPointer a value len :: after)).lookup ptr ≠ none := by
  have allocated := invariant.2.1
  have similar := invariant.2.2.2.2.2.2.1
  obtain ⟨before0, after0, heapEq, lengthEq⟩ :=
    heapSimilar_data_imp heap0 before after ys len data similar
  have originalFound : heapLookup (heapLength before) heap0 = some (.dataElement ys len data) := by
    rw [heapEq, lengthEq]
    exact heapLookup_prefix before0 after0 _
  have notBefore : ¬ a < heapLength h1 := by
    rw [allocated, heapLength_append]
    omega
  have copiedFound : heapLookup a (h1 ++ (h2 ++ [.dataElement ys len data])) =
      some (.dataElement ys len data) := by
    rw [allocated, ← List.append_assoc]
    simpa using heapLookup_prefix (h1 ++ h2) [] (.dataElement ys len data)
  have mapped : (heapMap 0 (before ++ .forwardPointer a value len :: after)).lookup
      (heapLength before) = some a := by
    rw [heapMap_replace_data before after a len ys data value]
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine ⟨mapped, ys, len, data, originalFound, ?_, reachable, ?_⟩
  · simpa [notBefore] using copiedFound
  · intro ptr u member less
    exact False.elim (notBefore less)

/-- Every pre-existing forwarding entry retains its original and copied heap
correspondence after a fresh copy. This is the old-entry case of the copying
collector proof. -/
theorem gcInv_move_fresh_old_entry {α β : Type}
    (h1 h2 before after heap0 : List (HeapElement α β)) (a n limit len : Nat)
    (roots0 ys : List (HeapAddress α)) (value : α) (data : β) (ok : Bool) (i j : Nat)
    (invariant : gcInv h1 h2 a n (before ++ .dataElement ys len data :: after) ok limit heap0 roots0)
    (different : i ≠ heapLength before)
    (newLookup : (heapMap 0 (before ++ .forwardPointer a value len :: after)).lookup i = some j) :
    ∃ xs size payload, heapLookup i heap0 = some (.dataElement xs size payload) ∧
      heapLookup j (h1 ++ (h2 ++ [.dataElement ys len data])) = some (.dataElement
        (if j < heapLength h1 then addrMap (heapMap1 (before ++ .forwardPointer a value len :: after)) xs
          else xs) size payload) ∧
      reachableAddresses roots0 heap0 i ∧
      ∀ ptr u, .pointer ptr u ∈ xs → j < heapLength h1 →
        (heapMap 0 (before ++ .forwardPointer a value len :: after)).lookup ptr ≠ none := by
  have oldLookup : (heapMap 0 (before ++ .dataElement ys len data :: after)).lookup i = some j := by
    rw [heapMap_replace_data before after a len ys data value] at newLookup
    simpa [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm different] using newLookup
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, entries⟩ := invariant
  obtain ⟨xs, size, payload, oldFound, copiedFound, reach, children⟩ := entries i j oldLookup
  have mappedEq : j < heapLength h1 →
      addrMap (heapMap1 (before ++ .forwardPointer a value len :: after)) xs =
        addrMap (heapMap1 (before ++ .dataElement ys len data :: after)) xs := by
    intro less
    apply addrMap_eq
    intro ptr u member
    exact heapMap1_forward_old before after ys len a data value ptr (children ptr u member less)
  refine ⟨xs, size, payload, oldFound, ?_, reach, ?_⟩
  · have extended := heapLookup_extend (h1 ++ h2) [.dataElement ys len data] j _ copiedFound
    by_cases less : j < heapLength h1
    · simpa [List.append_assoc, less, mappedEq less] using extended
    · simpa [List.append_assoc, less] using extended
  · intro ptr u member less
    have oldDefined := children ptr u member less
    cases found : (heapMap 0 (before ++ .dataElement ys len data :: after)).lookup ptr with
    | none => exact False.elim (oldDefined found)
    | some mapped =>
      have next := heapMap_forward_submap before after ys len a data value ptr mapped found
      rw [next]
      simp

/-- The fresh-copy post-state satisfies the full source-shaped copying
invariant. This Flapjack theorem assembles the structural, bijection, and
entry cases; `gcInv` remains untagged pending its representation qualifier. -/
theorem gcInv_move_fresh_post {α β : Type}
    (h1 h2 before after heap0 : List (HeapElement α β)) (a n limit len : Nat)
    (roots0 ys : List (HeapAddress α)) (value : α) (data : β) (ok : Bool)
    (invariant : gcInv h1 h2 a n (before ++ .dataElement ys len data :: after) ok limit heap0 roots0)
    (reachable : reachableAddresses roots0 heap0 (heapLength before)) :
    gcInv h1 (h2 ++ [.dataElement ys len data]) (a + (len + 1)) (n - (len + 1))
      (before ++ .forwardPointer a value len :: after) true limit heap0 roots0 := by
  obtain ⟨balance, allocated, free, heapSize, similar, h1Data, h2Data⟩ :=
    gcInv_move_fresh_structure h1 h2 before after heap0 a n limit len roots0 ys value data ok invariant
  obtain ⟨mapsInto, injective, surjective⟩ :=
    gcInv_move_fresh_bij h1 h2 before after heap0 a n limit len roots0 ys value data ok invariant
  refine ⟨balance, allocated, free, rfl, heapSize, invariant.2.2.2.2.2.1,
    similar, h1Data, h2Data, mapsInto, injective, surjective, ?_⟩
  intro i j newLookup
  by_cases eq : i = heapLength before
  · subst i
    obtain ⟨mapped, entry⟩ :=
      gcInv_move_fresh_new_entry h1 h2 before after heap0 a n limit len roots0 ys value data ok invariant reachable
    rw [mapped] at newLookup
    have eq : a = j := Option.some.inj newLookup
    subst j
    exact entry
  · exact gcInv_move_fresh_old_entry h1 h2 before after heap0 a n limit len roots0 ys value data ok i j
      invariant eq newLookup

/-- A single root move preserves the source-shaped copying invariant and
extends the forwarding map. This theorem remains untagged while `gcInv` and
the internal finite-map representation await HOL reference classification. -/
theorem gcInv_move {α β : Type} (x : HeapAddress α)
    (h1 h2 heap heap0 : List (HeapElement α β)) (a n limit : Nat) (ok : Bool)
    (roots0 : List (HeapAddress α))
    (invariant : gcInv h1 h2 a n heap ok limit heap0 roots0)
    (rootValid : ∀ ptr u, x = .pointer ptr u →
      isSomeDataOrForward (heapLookup ptr heap) ∧ reachableAddresses roots0 heap0 ptr) :
    ∃ h23 a3 n3 heap3 c3,
      gcMove (x, h2, a, n, heap, ok, limit) =
        (addrApply (heapMap1 heap3) x, h23, a3, n3, heap3, c3) ∧
      (∀ ptr u, x = .pointer ptr u → (heapMap 0 heap3).lookup ptr ≠ none) ∧
      (∀ ptr, isSomeDataOrForward (heapLookup ptr heap) ↔ isSomeDataOrForward (heapLookup ptr heap3)) ∧
      (∀ i j, (heapMap 0 heap).lookup i = some j → (heapMap 0 heap3).lookup i = some j) ∧
      gcInv h1 h23 a3 n3 heap3 c3 limit heap0 roots0 := by
  cases x with
  | data value =>
    exact ⟨h2, a, n, heap, ok, gcInv_move_data h1 h2 heap heap0 a n limit ok roots0 value invariant⟩
  | pointer ptr value =>
    obtain ⟨valid, reachable⟩ := rootValid ptr value rfl
    rcases valid with forward | data
    · obtain ⟨target, forwardedValue, len, found⟩ := forward
      exact ⟨h2, a, n, heap, ok,
        gcInv_move_forward h1 h2 heap heap0 a n limit ptr target len ok roots0 value forwardedValue invariant found⟩
    · obtain ⟨ys, len, payload, found⟩ := data
      obtain ⟨before, after, heapEq, ptrEq, run, observation, submap⟩ :=
        gcInv_move_fresh_core h1 h2 heap heap0 a n limit ptr len ok roots0 ys value payload invariant found
      have beforeInv : gcInv h1 h2 a n (before ++ .dataElement ys len payload :: after) ok limit heap0 roots0 := by
        simpa [heapEq] using invariant
      have beforeReach : reachableAddresses roots0 heap0 (heapLength before) := by
        simpa [ptrEq] using reachable
      have post := gcInv_move_fresh_post h1 h2 before after heap0 a n limit len roots0 ys value payload ok
        beforeInv beforeReach
      obtain ⟨mapped, _⟩ := gcInv_move_fresh_new_entry h1 h2 before after heap0 a n limit len roots0 ys
        value payload ok beforeInv beforeReach
      have mappedApply : heapMap1 (before ++ .forwardPointer a value len :: after) ptr = a := by
        rw [ptrEq]
        exact holFapply_of_lookup mapped
      refine ⟨h2 ++ [.dataElement ys len payload], a + (len + 1), n - (len + 1),
        before ++ .forwardPointer a value len :: after, true, ?_, ?_, observation, submap, post⟩
      · simpa [addrApply, mappedApply] using run
      · intro p u eq
        cases eq
        rw [ptrEq, mapped]
        simp

/-- Moving a list of valid roots preserves the copying invariant, extends the
forwarding map, and renames the roots by the final map. This theorem is
untagged while `gcInv` awaits its finite-map representation classification. -/
theorem gcInv_moveList {α β : Type} (xs : List (HeapAddress α))
    (h1 h2 heap heap0 : List (HeapElement α β)) (a n limit : Nat) (ok : Bool)
    (roots0 : List (HeapAddress α))
    (invariant : gcInv h1 h2 a n heap ok limit heap0 roots0)
    (rootsValid : ∀ ptr u, .pointer ptr u ∈ xs →
      isSomeDataOrForward (heapLookup ptr heap) ∧ reachableAddresses roots0 heap0 ptr) :
    ∃ h23 a3 n3 heap3 c3,
      gcMoveList (xs, h2, a, n, heap, ok, limit) =
        (addrMap (heapMap1 heap3) xs, h23, a3, n3, heap3, c3) ∧
      (∀ ptr u, .pointer ptr u ∈ xs → (heapMap 0 heap3).lookup ptr ≠ none) ∧
      (∀ ptr, isSomeDataOrForward (heapLookup ptr heap) ↔ isSomeDataOrForward (heapLookup ptr heap3)) ∧
      (∀ i j, (heapMap 0 heap).lookup i = some j → (heapMap 0 heap3).lookup i = some j) ∧
      gcInv h1 h23 a3 n3 heap3 c3 limit heap0 roots0 := by
  induction xs generalizing h2 a n heap ok with
  | nil =>
    exact ⟨h2, a, n, heap, ok, by simp [gcMoveList, addrMap, invariant]⟩
  | cons head tail ih =>
    have headValid : ∀ ptr u, head = .pointer ptr u →
        isSomeDataOrForward (heapLookup ptr heap) ∧ reachableAddresses roots0 heap0 ptr := by
      intro ptr u eq
      exact rootsValid ptr u (by simp [← eq])
    obtain ⟨h21, a1, n1, heap1, ok1, move, headDomain, observation1, submap1, inv1⟩ :=
      gcInv_move head h1 h2 heap heap0 a n limit ok roots0 invariant headValid
    have tailValid : ∀ ptr u, .pointer ptr u ∈ tail →
        isSomeDataOrForward (heapLookup ptr heap1) ∧ reachableAddresses roots0 heap0 ptr := by
      intro ptr u member
      obtain ⟨valid, reach⟩ := rootsValid ptr u (by simp [member])
      exact ⟨(observation1 ptr).mp valid, reach⟩
    obtain ⟨h22, a2, n2, heap2, ok2, moves, tailDomain, observation2, submap2, inv2⟩ :=
      ih h21 heap1 a1 n1 ok1 inv1 tailValid
    have headApply : addrApply (heapMap1 heap1) head = addrApply (heapMap1 heap2) head := by
      cases head with
      | data value => rfl
      | pointer ptr value =>
        have defined := headDomain ptr value rfl
        cases found : (heapMap 0 heap1).lookup ptr with
        | none => exact False.elim (defined found)
        | some target =>
          have next := submap2 ptr target found
          simp [addrApply, heapMap1, holFapply_of_lookup found, holFapply_of_lookup next]
    refine ⟨h22, a2, n2, heap2, ok2, ?_, ?_, ?_, ?_, inv2⟩
    · simp only [gcMoveList, move, headApply, moves]
      cases head <;> rfl
    · intro ptr u member
      simp only [List.mem_cons] at member
      rcases member with eq | member
      · have defined := headDomain ptr u eq.symm
        cases found : (heapMap 0 heap1).lookup ptr with
        | none => exact False.elim (defined found)
        | some target => rw [submap2 ptr target found]; simp
      · exact tailDomain ptr u member
    · intro ptr
      exact (observation1 ptr).trans (observation2 ptr)
    · intro i j old
      exact submap2 i j (submap1 i j old)

/-- Every pointer in the next unscanned data element is valid in the current
heap and reachable in the original heap. This is a Flapjack proof step toward
the copying collector scan-loop invariant. -/
theorem gcInv_scan_children {α β : Type} (h1 pending heap heap0 : List (HeapElement α β))
    (a n limit len : Nat) (ok : Bool) (roots0 ys : List (HeapAddress α)) (data : β)
    (invariant : gcInv h1 (.dataElement ys len data :: pending) a n heap ok limit heap0 roots0) :
    ∀ ptr u, .pointer ptr u ∈ ys →
      isSomeDataOrForward (heapLookup ptr heap) ∧ reachableAddresses roots0 heap0 ptr := by
  obtain ⟨_, _, _, _, _, heapGood, similar, _, _, _, _, surjective, entries⟩ := invariant
  have atBoundary : heapAddresses 0 (h1 ++ .dataElement ys len data :: pending) (heapLength h1) := by
    rw [heapAddresses_append]
    simp [heapAddresses]
  obtain ⟨i, defined, mapEq⟩ := surjective (heapLength h1) atBoundary
  cases found : (heapMap 0 heap).lookup i with
  | none => exact False.elim (defined found)
  | some j =>
    have jEq : j = heapLength h1 := by
      change holFapply (heapMap 0 heap) i = heapLength h1 at mapEq
      rw [holFapply_of_lookup found] at mapEq
      exact mapEq
    obtain ⟨xs, size, payload, oldFound, newFound, parentReach, _⟩ := entries i j found
    subst j
    simp only [Nat.lt_irrefl, ↓reduceIte] at newFound
    have boundaryFound := heapLookup_prefix h1 pending (.dataElement ys len data)
    have equalElements : HeapElement.dataElement xs size payload = .dataElement ys len data :=
      Option.some.inj (newFound.symm.trans boundaryFound)
    cases equalElements
    intro ptr u member
    have oldMember : .dataElement ys len data ∈ heap0 := heapLookup_mem heap0 i _ oldFound
    have originalData : isSomeDataElement (heapLookup ptr heap0) :=
      heapGood.2.2 ys len data ptr u ⟨oldMember, member⟩
    refine ⟨heapSimilar_data_imp_dataOrForward heap0 heap ptr similar originalData, ?_⟩
    obtain ⟨rootValue, root, rootMember, path⟩ := parentReach
    exact ⟨rootValue, root, rootMember, path.tail ⟨ys, len, data, u, oldFound, member⟩⟩

/-- Root-list movement keeps its input copied heap as a prefix. This
Flapjack consequence of `gcMoveList_alt` is used by the scan-loop proof. -/
theorem gcMoveList_preserves_prefix {α β : Type} (roots roots' : List (HeapAddress α))
    (copied copied' heap heap' : List (HeapElement α β)) (a n limit a' n' : Nat) (ok ok' : Bool)
    (run : gcMoveList (roots, copied, a, n, heap, ok, limit) = (roots', copied', a', n', heap', ok')) :
    ∃ added, copied' = copied ++ added := by
  have alt := gcMoveList_alt roots copied a n heap ok limit () () () () () ()
  rw [run] at alt
  cases result : gcMoveList (roots, [], a, n, heap, ok, limit) with
  | mk rootResult rest =>
    rcases rest with ⟨added, a1, n1, heap1, ok1⟩
    simp only [result, Prod.mk.injEq] at alt
    exact ⟨added, alt.2.1⟩

/-- Replacing a data element's pointer payload preserves every heap lookup
away from its starting address. This is a Flapjack scan proof helper. -/
theorem heapLookup_scan_replace_ne {α β : Type} (h1 tail : List (HeapElement α β))
    (ys zs : List (HeapAddress α)) (len : Nat) (data : β) (j : Nat)
    (ne : j ≠ heapLength h1) :
    heapLookup j (h1 ++ .dataElement ys len data :: tail) =
      heapLookup j (h1 ++ .dataElement zs len data :: tail) := by
  rw [GenGc.heapLookup_append j h1, GenGc.heapLookup_append j h1]
  by_cases below : j < heapLength h1
  · simp [below]
  · have nonzero : j - heapLength h1 ≠ 0 := by omega
    simp [below, heapLookup, nonzero, elLength]
    rfl

/-- The scanned and unscanned versions of a data element occupy the same
heap-address set. This is a Flapjack scan proof helper. -/
theorem heapAddresses_scan_replace {α β : Type} (h1 tail : List (HeapElement α β))
    (ys zs : List (HeapAddress α)) (len : Nat) (data : β) :
    heapAddresses 0 (h1 ++ .dataElement ys len data :: tail) =
      heapAddresses 0 ((h1 ++ [.dataElement zs len data]) ++ tail) := by
  rw [List.append_assoc]
  simp only [List.singleton_append, heapAddresses_append]
  funext j
  simp [heapAddresses, elLength]

/-- Moving a fully processed element from the pending heap into the scanned
heap preserves the source-shaped collector invariant. This Flapjack theorem
is the scan-state shift needed for the copying collector loop proof. -/
theorem gcInv_scan_shift {α β : Type} (h1 tail heap heap0 : List (HeapElement α β))
    (a n limit len : Nat) (ok : Bool) (roots0 ys : List (HeapAddress α)) (data : β)
    (invariant : gcInv h1 (.dataElement ys len data :: tail) a n heap ok limit heap0 roots0)
    (children : ∀ ptr u, .pointer ptr u ∈ ys → (heapMap 0 heap).lookup ptr ≠ none) :
    gcInv (h1 ++ [.dataElement (addrMap (heapMap1 heap) ys) len data]) tail
      a n heap ok limit heap0 roots0 := by
  obtain ⟨balance, allocated, free, status, heapSize, heapGood, similar, h1Data, pendingData,
    mapsInto, injective, surjective, entries⟩ := invariant
  have h2Data : ∀ h ∈ tail, isDataElement h := by
    intro h member
    exact pendingData h (by simp [member])
  have newH1Data : ∀ h ∈ h1 ++ [.dataElement (addrMap (heapMap1 heap) ys) len data], isDataElement h := by
    intro h member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact h1Data h member
    · exact ⟨_, _, _, rfl⟩
  have totalLen : heapLength (h1 ++ .dataElement ys len data :: tail) =
      heapLength ((h1 ++ [.dataElement (addrMap (heapMap1 heap) ys) len data]) ++ tail) := by
    simp [heapLength, List.map_append, List.sum_append, elLength, Nat.add_assoc]
  have addressEq := heapAddresses_scan_replace h1 tail ys (addrMap (heapMap1 heap) ys) len data
  refine ⟨balance, allocated.trans totalLen, free, status, heapSize, heapGood, similar,
    newH1Data, h2Data, ?_, injective, ?_, ?_⟩
  · intro i defined
    rw [← addressEq]
    exact mapsInto i defined
  · intro j member
    apply surjective j
    rwa [addressEq]
  · intro i j found
    obtain ⟨xs, size, payload, originalFound, copiedFound, reach, oldChildren⟩ := entries i j found
    refine ⟨xs, size, payload, originalFound, ?_, reach, ?_⟩
    · have newBound : heapLength (h1 ++ [.dataElement (addrMap (heapMap1 heap) ys) len data]) =
          heapLength h1 + (len + 1) := by
        simp [heapLength, List.map_append, List.sum_append, elLength]
      by_cases before : j < heapLength h1
      · have beforeNew : j < heapLength (h1 ++ [.dataElement (addrMap (heapMap1 heap) ys) len data]) := by
          rw [newBound]; omega
        have ne : j ≠ heapLength h1 := by omega
        have sameLookup := heapLookup_scan_replace_ne h1 tail ys (addrMap (heapMap1 heap) ys) len data j ne
        simpa [List.append_assoc, before, beforeNew, ← sameLookup] using copiedFound
      · by_cases atHead : j = heapLength h1
        · subst j
          simp only [Nat.lt_irrefl, ↓reduceIte] at copiedFound
          have expected := heapLookup_prefix h1 tail (.dataElement ys len data)
          have eq : HeapElement.dataElement xs size payload = .dataElement ys len data :=
            Option.some.inj (copiedFound.symm.trans expected)
          cases eq
          have beforeNew : heapLength h1 <
              heapLength (h1 ++ [.dataElement (addrMap (heapMap1 heap) ys) len data]) := by
            rw [newBound]; omega
          have result := heapLookup_prefix h1 tail (.dataElement (addrMap (heapMap1 heap) ys) len data)
          simpa [List.append_assoc, beforeNew] using result
        · have beyond : heapLength h1 + (len + 1) ≤ j := by
            by_contra smaller
            have inside : j - heapLength h1 < len + 1 := by omega
            have nonzero : j - heapLength h1 ≠ 0 := by omega
            rw [GenGc.heapLookup_append j h1] at copiedFound
            simp [before, heapLookup, nonzero, elLength, inside] at copiedFound
          have notBeforeNew : ¬j < heapLength (h1 ++ [.dataElement (addrMap (heapMap1 heap) ys) len data]) := by
            rw [newBound]; omega
          have sameLookup := heapLookup_scan_replace_ne h1 tail ys (addrMap (heapMap1 heap) ys) len data j atHead
          simpa [List.append_assoc, before, notBeforeNew, ← sameLookup] using copiedFound
    · intro ptr u member scanned
      by_cases before : j < heapLength h1
      · exact oldChildren ptr u member before
      · have upper : j < heapLength h1 + (len + 1) := by
          simpa [heapLength, List.map_append, List.sum_append, elLength] using scanned
        have atHead : j = heapLength h1 := by
          by_contra ne
          have inside : j - heapLength h1 < len + 1 := by omega
          have nonzero : j - heapLength h1 ≠ 0 := by omega
          rw [GenGc.heapLookup_append j h1] at copiedFound
          simp [before, heapLookup, nonzero, elLength, inside] at copiedFound
        subst j
        simp only [Nat.lt_irrefl, ↓reduceIte] at copiedFound
        have expected := heapLookup_prefix h1 tail (.dataElement ys len data)
        have eq : HeapElement.dataElement xs size payload = .dataElement ys len data :=
          Option.some.inj (copiedFound.symm.trans expected)
        cases eq
        exact children ptr u member

/-- Scanning all pending copied elements preserves the source-shaped
collector invariant and extends the forwarding map. This theorem is untagged
while `gcInv` awaits finite-map representation classification. -/
theorem gcInv_moveLoop {α β : Type} (h1 h2 heap heap0 : List (HeapElement α β))
    (a n limit : Nat) (ok : Bool) (roots0 : List (HeapAddress α))
    (invariant : gcInv h1 h2 a n heap ok limit heap0 roots0) :
    ∃ h13 a3 n3 heap3 c3,
      gcMoveLoop (h1, h2, a, n, heap, ok, limit) = (h13, a3, n3, heap3, c3) ∧
      (∀ i j, (heapMap 0 heap).lookup i = some j → (heapMap 0 heap3).lookup i = some j) ∧
      gcInv h13 [] a3 n3 heap3 c3 limit heap0 roots0 := by
  cases h2 with
  | nil => exact ⟨h1, a, n, heap, ok, by simp [gcMoveLoop, invariant]⟩
  | cons head tail =>
    have headData : isDataElement head := invariant.2.2.2.2.2.2.2.2.1 head (by simp)
    obtain ⟨ys, len, data, rfl⟩ := headData
    have guard : ¬limit < heapLength (h1 ++ .dataElement ys len data :: tail) := by
      have balance := invariant.1
      have allocated := invariant.2.1
      omega
    have childrenValid := gcInv_scan_children h1 tail heap heap0 a n limit len ok roots0 ys data invariant
    obtain ⟨pending', a1, n1, heap1, ok1, moved, childrenDomain, _, submap1, inv1⟩ :=
      gcInv_moveList ys h1 (.dataElement ys len data :: tail) heap heap0 a n limit ok roots0 invariant childrenValid
    obtain ⟨added, pendingEq⟩ := gcMoveList_preserves_prefix ys (addrMap (heapMap1 heap1) ys)
      (.dataElement ys len data :: tail) pending' heap heap1 a n limit a1 n1 ok ok1 moved
    subst pending'
    have shifted := gcInv_scan_shift h1 (tail ++ added) heap1 heap0 a1 n1 limit len ok1 roots0 ys data inv1 childrenDomain
    have positive : 0 < len + 1 := by omega
    have oldBelow : heapLength h1 < limit := by
      have balance := invariant.1
      have allocated := invariant.2.1
      simp [heapLength, List.map_append, List.sum_append, elLength] at allocated ⊢
      omega
    have decrease : limit - heapLength (h1 ++ [.dataElement (addrMap (heapMap1 heap1) ys) len data]) <
        limit - heapLength h1 := by
      simp [heapLength, List.map_append, List.sum_append, elLength] at oldBelow ⊢
      omega
    obtain ⟨h13, a3, n3, heap3, c3, scan, submap2, resultInv⟩ :=
      gcInv_moveLoop (h1 ++ [.dataElement (addrMap (heapMap1 heap1) ys) len data]) (tail ++ added)
        heap1 heap0 a1 n1 limit ok1 roots0 shifted
    refine ⟨h13, a3, n3, heap3, c3, ?_, ?_, resultInv⟩
    · simp only [gcMoveLoop, if_neg guard, moved, List.cons_append, List.drop, List.head?]
      simpa using scan
    · intro i j old
      exact submap2 i j (submap1 i j old)
termination_by limit - heapLength h1
decreasing_by exact decrease

/-- A well-formed heap and valid roots produce a successful full collection
and the final source-shaped invariant. This result remains untagged while
`gcInv` and its finite-map representation await source classification. -/
theorem fullGc_invariant {α β : Type} (roots : List (HeapAddress α))
    (heap : List (HeapElement α β)) (limit : Nat)
    (rootOk : rootsOk roots heap) (heapGood : heapOk heap limit) :
    ∃ heap2 a2 heap3,
      fullGc (roots, heap, limit) = (addrMap (heapMap1 heap3) roots, heap2, a2, true) ∧
      (∀ ptr u, .pointer ptr u ∈ roots → (heapMap 0 heap3).lookup ptr ≠ none) ∧
      gcInv heap2 [] a2 (limit - a2) heap3 true limit heap roots := by
  have initial := (gcInv_init heap roots limit).mpr heapGood
  have valid : ∀ ptr u, .pointer ptr u ∈ roots →
      isSomeDataOrForward (heapLookup ptr heap) ∧ reachableAddresses roots heap ptr := by
    intro ptr u member
    exact ⟨Or.inr (rootOk ptr u member), ⟨u, ptr, member, .refl⟩⟩
  obtain ⟨pending, a1, n1, heap1, c1, moved, domain1, _, _, inv1⟩ :=
    gcInv_moveList roots [] [] heap heap 0 limit limit true roots initial valid
  obtain ⟨heap2, a2, n2, heap3, c3, scanned, submap, inv2⟩ :=
    gcInv_moveLoop [] pending heap1 heap a1 n1 limit c1 roots inv1
  have status : c3 = true := inv2.2.2.2.1
  have balance : a2 + n2 = limit := inv2.1
  have allocated : a2 = heapLength heap2 := by simpa using inv2.2.1
  have finalHeap : heapLength heap3 = limit := inv2.2.2.2.2.1
  have remaining : n2 = limit - a2 := by omega
  have within : heapLength heap2 ≤ limit := by omega
  have rootDomain : ∀ ptr u, .pointer ptr u ∈ roots → (heapMap 0 heap3).lookup ptr ≠ none := by
    intro ptr u member
    have defined := domain1 ptr u member
    cases lookup : (heapMap 0 heap1).lookup ptr with
    | none => exact False.elim (defined lookup)
    | some target => rw [submap ptr target lookup]; simp
  have rootMap : addrMap (heapMap1 heap1) roots = addrMap (heapMap1 heap3) roots := by
    apply addrMap_eq
    intro ptr u member
    have defined := domain1 ptr u member
    cases lookup : (heapMap 0 heap1).lookup ptr with
    | none => exact False.elim (defined lookup)
    | some target =>
      have final := submap ptr target lookup
      change holFapply (heapMap 0 heap1) ptr = holFapply (heapMap 0 heap3) ptr
      rw [holFapply_of_lookup lookup, holFapply_of_lookup final]
  refine ⟨heap2, a2, heap3, ?_, rootDomain, ?_⟩
  · simp [fullGc, moved, scanned, rootMap, status, allocated, finalHeap, heapGood.1, remaining, within]
  · simpa [status, remaining] using inv2

/-- At the end of scanning, the forwarding-map domain is exactly the set of
addresses reachable from the original roots. This Flapjack theorem derives
the domain clause needed for the full collector heap relation. -/
theorem gcInv_final_domain {α β : Type} (heap2 heap3 heap : List (HeapElement α β))
    (a n limit : Nat) (ok : Bool) (roots : List (HeapAddress α))
    (invariant : gcInv heap2 [] a n heap3 ok limit heap roots)
    (rootDomain : ∀ ptr u, .pointer ptr u ∈ roots → (heapMap 0 heap3).lookup ptr ≠ none) :
    (fun ptr => (heapMap 0 heap3).lookup ptr ≠ none) = reachableAddresses roots heap := by
  obtain ⟨_, _, _, _, _, _, _, _, _, mapsInto, _, _, entries⟩ := invariant
  funext ptr
  apply propext
  constructor
  · intro defined
    cases found : (heapMap 0 heap3).lookup ptr with
    | none => exact False.elim (defined found)
    | some target =>
      obtain ⟨_, _, _, _, _, reach, _⟩ := entries ptr target found
      exact reach
  · intro reach
    obtain ⟨value, source, member, path⟩ := reach
    induction path with
    | refl => exact rootDomain source value member
    | @tail middle target path edge ih =>
      cases found : (heapMap 0 heap3).lookup middle with
      | none => exact False.elim (ih found)
      | some mapped =>
        have mapValue : heapMap1 heap3 middle = mapped := holFapply_of_lookup found
        have address : heapAddresses 0 heap2 mapped := by
          have bound := mapsInto middle (by rw [found]; simp)
          simpa [mapValue] using bound
        have below : mapped < heapLength heap2 := by
          simpa using heapAddresses_less_heapLength heap2 0 mapped address
        obtain ⟨xs, size, payload, oldFound, _, _, children⟩ := entries middle mapped found
        obtain ⟨edgeRoots, edgeLen, edgeData, edgeValue, edgeFound, edgeMember⟩ := edge
        have equal : HeapElement.dataElement xs size payload = .dataElement edgeRoots edgeLen edgeData :=
          Option.some.inj (oldFound.symm.trans edgeFound)
        cases equal
        exact children target edgeValue edgeMember below

/-- At the end of scanning, the forwarding-map range is exactly the set of
data-element addresses in the copied heap. This is a Flapjack consequence of
the final copying invariant. -/
theorem gcInv_final_range {α β : Type} (heap2 heap3 heap : List (HeapElement α β))
    (a n limit : Nat) (ok : Bool) (roots : List (HeapAddress α))
    (invariant : gcInv heap2 [] a n heap3 ok limit heap roots) :
    (fun target => ∃ ptr, (heapMap 0 heap3).lookup ptr = some target) =
      (fun target => isSomeDataElement (heapLookup target heap2)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, mapsInto, _, surjective, entries⟩ := invariant
  funext target
  apply propext
  constructor
  · rintro ⟨ptr, found⟩
    have mapValue : heapMap1 heap3 ptr = target := holFapply_of_lookup found
    have address : heapAddresses 0 heap2 target := by
      have bound := mapsInto ptr (by rw [found]; simp)
      simpa [mapValue] using bound
    have below : target < heapLength heap2 := by
      simpa using heapAddresses_less_heapLength heap2 0 target address
    obtain ⟨xs, len, payload, _, copied, _, _⟩ := entries ptr target found
    simp only [List.append_nil, below, ↓reduceIte] at copied
    exact ⟨addrMap (heapMap1 heap3) xs, len, payload, copied⟩
  · rintro ⟨xs, len, payload, found⟩
    have address := GenGc.heapLookup_imp_heapAddresses heap2 target (.dataElement xs len payload) found
    have inAddresses : heapAddresses 0 (heap2 ++ []) target := by simpa using address
    obtain ⟨ptr, defined, mapValue⟩ := surjective target inAddresses
    cases lookup : (heapMap 0 heap3).lookup ptr with
    | none => exact False.elim (defined lookup)
    | some value =>
      have eq : value = target := by
        change holFapply (heapMap 0 heap3) ptr = target at mapValue
        rwa [holFapply_of_lookup lookup] at mapValue
      exact ⟨ptr, eq ▸ lookup⟩

/-- The final copying invariant establishes the abstract relation between the
original heap and the copied heap. This is a Flapjack consequence of `gcInv`. -/
theorem gcInv_final_related {α β : Type} (heap2 heap3 heap : List (HeapElement α β))
    (a n limit : Nat) (ok : Bool) (roots : List (HeapAddress α))
    (invariant : gcInv heap2 [] a n heap3 ok limit heap roots) :
    gcRelated (heapMap 0 heap3) heap heap2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, mapsInto, injective, _, entries⟩ := invariant
  have entry : ∀ i, (heapMap 0 heap3).lookup i ≠ none →
      ∃ xs len payload, heapLookup i heap = some (.dataElement xs len payload) ∧
        heapLookup (heapMap1 heap3 i) heap2 = some (.dataElement (addrMap (heapMap1 heap3) xs) len payload) ∧
        ∀ ptr value, .pointer ptr value ∈ xs → (heapMap 0 heap3).lookup ptr ≠ none := by
    intro i defined
    cases found : (heapMap 0 heap3).lookup i with
    | none => exact False.elim (defined found)
    | some mapped =>
      have mapValue : heapMap1 heap3 i = mapped := holFapply_of_lookup found
      have address : heapAddresses 0 heap2 mapped := by
        have h := mapsInto i defined
        simpa [mapValue] using h
      have below : mapped < heapLength heap2 := by
        simpa using heapAddresses_less_heapLength heap2 0 mapped address
      obtain ⟨xs, len, payload, oldFound, newFound, _, childDomain⟩ := entries i mapped found
      refine ⟨xs, len, payload, oldFound, ?_, ?_⟩
      · simpa [mapValue, below] using newFound
      · intro ptr value member
        exact childDomain ptr value member below
  refine ⟨?_, injective, ?_, ?_⟩
  · intro i defined
    obtain ⟨xs, len, payload, _, found, _⟩ := entry i defined
    exact ⟨addrMap (heapMap1 heap3) xs, len, payload, found⟩
  · intro i defined
    obtain ⟨xs, len, payload, found, _, _⟩ := entry i defined
    exact ⟨xs, len, payload, found⟩
  · intro i xs len payload defined found
    obtain ⟨xs', len', payload', oldFound, newFound, children⟩ := entry i defined
    have eq : HeapElement.dataElement xs' len' payload' = .dataElement xs len payload :=
      Option.some.inj (oldFound.symm.trans found)
    cases eq
    exact ⟨newFound, children⟩

/-- Successful full collection supplies the source-domain, target-range,
and heap-relation clauses of the abstract collector theorem. The source's
heap-filter length equality remains to be proved separately. -/
theorem fullGc_relation_clauses {α β : Type} (roots : List (HeapAddress α))
    (heap : List (HeapElement α β)) (limit : Nat)
    (rootOk : rootsOk roots heap) (heapGood : heapOk heap limit) :
    ∃ (heap2 : List (HeapElement α β)) (a2 : Nat) (f : HolFiniteMapExact Nat Nat),
      fullGc (roots, heap, limit) = (addrMap (holFapply f) roots, heap2, a2, true) ∧
      (fun ptr => f.lookup ptr ≠ none) = reachableAddresses roots heap ∧
      (fun target => ∃ ptr, f.lookup ptr = some target) =
        (fun target => isSomeDataElement (heapLookup target heap2)) ∧
      gcRelated f heap heap2 ∧
      (∀ element ∈ heap2, isDataElement element) ∧ heapLength heap2 = a2 := by
  obtain ⟨heap2, a2, heap3, run, rootDomain, invariant⟩ := fullGc_invariant roots heap limit rootOk heapGood
  refine ⟨heap2, a2, heapMap 0 heap3, run, ?_, ?_, ?_, ?_, ?_⟩
  · exact gcInv_final_domain heap2 heap3 heap a2 (limit - a2) limit true roots invariant rootDomain
  · exact gcInv_final_range heap2 heap3 heap a2 (limit - a2) limit true roots invariant
  · exact gcInv_final_related heap2 heap3 heap a2 (limit - a2) limit true roots invariant
  · exact invariant.2.2.2.2.2.2.2.1
  · simpa using invariant.2.1.symm

end Flapjack.Compiler.Backend.CopyingGc
