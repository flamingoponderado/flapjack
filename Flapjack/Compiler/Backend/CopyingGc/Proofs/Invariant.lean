import Flapjack.Compiler.Backend.CopyingGc
import Flapjack.Compiler.Backend.GcShared.HeapSimilarity
import Flapjack.Compiler.Backend.GcShared.Reachability
import Flapjack.Compiler.Backend.GcShared.ForwardPtr

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

end Flapjack.Compiler.Backend.CopyingGc
