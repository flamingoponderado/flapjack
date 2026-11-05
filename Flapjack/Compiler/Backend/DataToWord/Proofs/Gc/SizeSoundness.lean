import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.SizeVisited

/-! Generalized source sizing bound for heap reachability. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend

/-- Flapjack infrastructure: a member of the left side of a related pair of
lists has a corresponding right-side witness. -/
theorem forall₂_member_witness {α β : Type} (R : α → β → Prop)
    (xs : List α) (ys : List β) (related : List.Forall₂ R xs ys)
    (x : α) (member : x ∈ xs) : ∃ y, R x y := by
  induction related with
  | nil => simp at member
  | cons h t ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | later
    · exact ⟨_, h⟩
    · exact ih later

/-- Flapjack infrastructure: select related heap addresses for a list whose
members are all represented in an existing related list. -/
theorem forall₂_subset_witness {α β : Type} (R : α → β → Prop)
    (xs roots : List α) (addresses : List β) (related : List.Forall₂ R roots addresses)
    (subset : ∀ x, x ∈ xs → x ∈ roots) : ∃ selected, List.Forall₂ R xs selected := by
  induction xs with
  | nil => exact ⟨[], List.Forall₂.nil⟩
  | cons value tail ih =>
    obtain ⟨address, pair⟩ := forall₂_member_witness R roots addresses related value (subset value (by simp))
    obtain ⟨rest, pairs⟩ := ih (fun x member => subset x (by simp [member]))
    exact ⟨address :: rest, List.Forall₂.cons pair pairs⟩

/-- Flapjack infrastructure: source sizing bounds a list covering every heap
address reachable from the represented roots. This is the generalized sizing
bound, stated with exact finite-map carriers and lookup-form domain premises;
it has not yet been classified as a reviewed HOL theorem port. -/
theorem sizeSound_reachable {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (roots2 dups roots : List DataSem.Value)
    (addresses : List (HeapAddress (WordLocW width)))
    (refs : Spt (BvlSem.Ref DataSem.Value)) (conf : Config)
    (f tf : HolFiniteMapExact Nat Nat) (heap : Memory.ValueHeap width) (be : Bool)
    (good : goodDimindex width) (architecture : limits.arch64Bit = decide (width = 64))
    (perm : roots2.Perm (dups ++ roots)) (duplicates : ∀ value, value ∈ dups → value ∈ roots)
    (related : List.Forall₂ (fun v a => Memory.valueInv conf v refs (a, f, tf, heap)) roots addresses)
    (noThunks : DataSem.noThunksInRefs refs)
    (mapInRefs : ∀ key ptr, f.lookup key = some ptr → sptLookup key refs ≠ none)
    (cells : ∀ key ptr, Memory.reachableRefs roots refs key → f.lookup key = some ptr →
      Memory.bcRefInv conf key refs (f, tf, heap, be)) :
    ∃ after : List Nat, (after.map (Memory.lookupLen heap)).sum ≤ (DataSem.sizeOfValues limits roots2 refs .ln).1 ∧
      ∀ ptr, reachableAddresses addresses heap ptr → ptr ∈ after := by
  obtain ⟨dupAddresses, dupRelated⟩ := forall₂_subset_witness
    (fun v a => Memory.valueInv conf v refs (a, f, tf, heap)) dups roots addresses related duplicates
  have allRelated := List.rel_append dupRelated related
  have allCells : ∀ key ptr, Memory.reachableRefs (dups ++ roots) refs key → f.lookup key = some ptr →
      Memory.bcRefInv conf key refs (f, tf, heap, be) := by
    intro key ptr reachable mapped
    apply cells key ptr _ mapped
    apply reachableRefs_roots_mono refs (dups ++ roots) roots key _ reachable
    intro value member
    rcases List.mem_append.mp member with dup | original
    · exact duplicates value dup
    · exact original
  have initial : sizeVisited refs refs .ln f tf [] := by
    constructor
    · simp [sptLookup]
    · intro key present absent
      exact False.elim (present absent)
  have sub : sptSubspt refs refs := by
    rw [sptSubsptLookup]
    exact fun _ _ found => found
  have result := sizeSound_all limits conf roots2 (dups ++ roots) (dupAddresses ++ addresses)
    refs refs .ln f tf heap be [] good architecture perm allRelated noThunks sub initial mapInRefs allCells
  obtain ⟨after, bound, traversal, _, _⟩ := result
  refine ⟨after, ?_, ?_⟩
  · simpa using bound
  · intro ptr reachable
    apply traverseHeap_reachable heap (dupAddresses ++ addresses) after ptr traversal
    obtain ⟨value, root, member, path⟩ := reachable
    exact ⟨value, root, List.mem_append_right _ member, path⟩

/-- Flapjack infrastructure: when all heap data is reachable from the
represented roots, the generalized sizing bound covers the whole data length. -/
theorem dataLength_le_sizeSound {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (roots2 : List DataSem.Value)
    (addresses : List (HeapAddress (WordLocW width)))
    (refs : Spt (BvlSem.Ref DataSem.Value)) (heap : Memory.ValueHeap width)
    (reachable : Memory.allReachableFromRoots addresses heap)
    (bound : ∃ after : List Nat,
      (after.map (Memory.lookupLen heap)).sum ≤ (DataSem.sizeOfValues limits roots2 refs .ln).1 ∧
      ∀ ptr, reachableAddresses addresses heap ptr → ptr ∈ after) :
    Memory.dataLength heap ≤ (DataSem.sizeOfValues limits roots2 refs .ln).1 := by
  obtain ⟨after, size, cover⟩ := bound
  exact Nat.le_trans (dataLength_le_reachableCover addresses heap after reachable cover) size

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
