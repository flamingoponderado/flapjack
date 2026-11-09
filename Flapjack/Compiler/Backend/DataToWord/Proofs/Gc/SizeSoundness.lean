module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.SizeVisited

@[expose] public section

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

/-- Flapjack infrastructure: the abstract ML invariant supplies the exact
finite maps and related roots needed to bound a fully reachable heap by the
source sizing result, including duplicated source roots. -/
theorem absMlInv_dataLength_le_size {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (roots2 dups stack : List DataSem.Value)
    (roots : List (HeapAddress (WordLocW width))) (heap : Memory.ValueHeap width)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (be : Bool) (a sp sp1 limit next : Nat)
    (gens : GcCombined.GenState) (good : goodDimindex width)
    (architecture : limits.arch64Bit = decide (width = 64))
    (invariant : Memory.absMlInv conf stack refs (roots, heap, be, a, sp, sp1, gens) limit next)
    (reachable : Memory.allReachableFromRoots roots heap)
    (noThunks : DataSem.noThunksInRefs refs)
    (perm : roots2.Perm (dups ++ stack)) (duplicates : ∀ value, value ∈ dups → value ∈ stack) :
    Memory.dataLength heap ≤ (DataSem.sizeOfValues limits roots2 refs .ln).1 := by
  obtain ⟨_, _, _, _, f, tf, _, mapSubset, _, _, _, _, _, related, cells⟩ := invariant
  have mapInRefs : ∀ key ptr, f.lookup key = some ptr → sptLookup key refs ≠ none := by
    intro key ptr mapped absent
    obtain ⟨cell, found⟩ := mapSubset key (by simp [Memory.mapDomain, mapped])
    rw [absent] at found
    contradiction
  have cells' : ∀ key ptr, Memory.reachableRefs stack refs key → f.lookup key = some ptr →
      Memory.bcRefInv conf key refs (f, tf, heap, be) := by
    intro key ptr reach mapped
    exact cells key ⟨reach, by simp [Memory.mapDomain, mapped]⟩
  apply dataLength_le_sizeSound limits roots2 roots refs heap reachable
  exact sizeSound_reachable limits roots2 dups stack roots refs conf f tf heap be good architecture
    perm duplicates related noThunks mapInRefs cells'

/-- Flapjack infrastructure: after a fully reachable collection, failure of a
request implies the corresponding source heap-size limit is exceeded. -/
theorem absMlInv_failed_request {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (roots2 dups stack : List DataSem.Value)
    (roots : List (HeapAddress (WordLocW width))) (heap : Memory.ValueHeap width)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (be : Bool) (a sp sp1 limit next request : Nat)
    (gens : GcCombined.GenState) (good : goodDimindex width)
    (architecture : limits.arch64Bit = decide (width = 64)) (limitEq : limits.heapLimit = limit)
    (invariant : Memory.absMlInv conf stack refs (roots, heap, be, a, sp, sp1, gens) limit next)
    (reachable : Memory.allReachableFromRoots roots heap)
    (noThunks : DataSem.noThunksInRefs refs)
    (heapSplit : heapLength heap = Memory.dataLength heap + sp + sp1)
    (failed : sp + sp1 < request)
    (perm : roots2.Perm (dups ++ stack)) (duplicates : ∀ value, value ∈ dups → value ∈ stack) :
    limits.heapLimit < (DataSem.sizeOfValues limits roots2 refs .ln).1 + request := by
  have bound := absMlInv_dataLength_le_size limits conf roots2 dups stack roots heap refs be a sp sp1
    limit next gens good architecture invariant reachable noThunks perm duplicates
  have heapSize : heapLength heap = limit := invariant.2.1.1
  omega

/-- Canonical lookup and finite-support roundtrip for the source reference map. -/
theorem holFmapAsFiniteSupportParamWitness_soundnessSizeOfGen_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (Memory.ReferenceMapBroad.ofBroad (Memory.ReferenceMapBroad.toBroad f)).lookup key = f.lookup key ∧
    (Memory.ReferenceMapBroad.ofBroad (Memory.ReferenceMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    Memory.ReferenceMapBroad.ofBroad (Memory.ReferenceMapBroad.toBroad f) = f := by
  cases f
  exact ⟨rfl, rfl, rfl⟩

/-- Canonical lookup and finite-support roundtrip for the source timestamp map. -/
theorem holFmapAsFiniteSupportParamWitness_soundnessSizeOfGen_tf
    (tf : HolFiniteMapExact Nat Nat) (key : Nat) :
    (Memory.ReferenceMapBroad.ofBroad (Memory.ReferenceMapBroad.toBroad tf)).lookup key = tf.lookup key ∧
    (Memory.ReferenceMapBroad.ofBroad (Memory.ReferenceMapBroad.toBroad tf)).finiteSupport = tf.finiteSupport ∧
    Memory.ReferenceMapBroad.ofBroad (Memory.ReferenceMapBroad.toBroad tf) = tf := by
  cases tf
  exact ⟨rfl, rfl, rfl⟩

/-- The source's generalized heap-size soundness theorem, retaining the
explicit sizing result and the source's duplicate-root and reachability premises. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "soundness_size_of_gen"
  (fmap_as_finite_support_parameters := [f, tf]) (words_as_type_indexed_bitvec)]
theorem soundnessSizeOfGen {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (roots2 dups roots : List Flapjack.Compiler.Backend.DataSem.Value)
    (addresses : List (HeapAddress (WordLocW width))) (n2 : Nat)
    (r2 : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (s2 : Spt Unit)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (conf : Config)
    (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat) (heap : Memory.ValueHeap width) (be : Bool)
    (cells : ∀ key, Memory.reachableRefs roots refs key ∧ Memory.mapDomain f key →
      Memory.bcRefInv conf key refs (f, tf, heap, be))
    (noThunks : DataSem.noThunksInRefs refs)
    (related : List.Forall₂ (fun v a => Memory.valueInv conf v refs (a, f, tf, heap)) roots addresses)
    (perm : roots2.Perm (dups ++ roots)) (duplicates : ∀ value, value ∈ dups → value ∈ roots)
    (good : goodDimindex width) (mapInRefs : ∀ key, Memory.mapDomain f key → sptDomain refs key)
    (architecture : limits.arch64Bit = decide (width = 64))
    (sizing : DataSem.sizeOfValues limits roots2 refs .ln = (n2, r2, s2)) :
    ∃ after : List Nat, (after.map (Memory.lookupLen heap)).sum ≤ n2 ∧
      ∀ ptr, reachableAddresses addresses heap ptr → ptr ∈ after := by
  have mapInRefs' : ∀ key ptr, f.lookup key = some ptr → sptLookup key refs ≠ none := by
    intro key ptr mapped absent
    have present := mapInRefs key ⟨ptr, mapped⟩
    simp [sptDomain, absent] at present
  have cells' : ∀ key ptr, Memory.reachableRefs roots refs key → f.lookup key = some ptr →
      Memory.bcRefInv conf key refs (f, tf, heap, be) := by
    intro key ptr reachable mapped
    exact cells key ⟨reachable, ptr, mapped⟩
  obtain ⟨after, bound, reachable⟩ := sizeSound_reachable limits roots2 dups roots addresses refs conf f tf heap be
    good architecture perm duplicates related noThunks mapInRefs' cells'
  refine ⟨after, ?_, reachable⟩
  simpa [sizing] using bound

/-- Canonical lookup and finite-support roundtrip for the reference map. -/
theorem holFmapAsFiniteSupportParamWitness_soundnessSizeOf_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (Memory.ReferenceMapBroad.ofBroad (Memory.ReferenceMapBroad.toBroad f)).lookup key = f.lookup key ∧
    (Memory.ReferenceMapBroad.ofBroad (Memory.ReferenceMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    Memory.ReferenceMapBroad.ofBroad (Memory.ReferenceMapBroad.toBroad f) = f := by
  cases f
  exact ⟨rfl, rfl, rfl⟩

/-- Canonical lookup and finite-support roundtrip for the timestamp map. -/
theorem holFmapAsFiniteSupportParamWitness_soundnessSizeOf_tf
    (tf : HolFiniteMapExact Nat Nat) (key : Nat) :
    (Memory.ReferenceMapBroad.ofBroad (Memory.ReferenceMapBroad.toBroad tf)).lookup key = tf.lookup key ∧
    (Memory.ReferenceMapBroad.ofBroad (Memory.ReferenceMapBroad.toBroad tf)).finiteSupport = tf.finiteSupport ∧
    Memory.ReferenceMapBroad.ofBroad (Memory.ReferenceMapBroad.toBroad tf) = tf := by
  cases tf
  exact ⟨rfl, rfl, rfl⟩

/-- Source heap sizing is bounded by an actual traversal, preserving the
reference submap and both visited images, including out-of-domain map values. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "soundness_size_of"
  (fmap_as_finite_support_parameters := [f, tf]) (words_as_type_indexed_bitvec)]
theorem soundnessSizeOf {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (roots : List Flapjack.Compiler.Backend.DataSem.Value)
    (r1 : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (s1 : Spt Unit)
    (rootVars : List Flapjack.Compiler.Backend.DataSem.Value)
    (addresses : List (HeapAddress (WordLocW width))) (n2 : Nat)
    (r2 : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (s2 : Spt Unit) (p1 : List Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (conf : Config)
    (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat) (heap : Memory.ValueHeap width) (be : Bool)
    (cells : ∀ key, Memory.reachableRefs rootVars refs key ∧ Memory.mapDomain f key →
      Memory.bcRefInv conf key refs (f, tf, heap, be))
    (noThunks : DataSem.noThunksInRefs refs)
    (related : List.Forall₂ (fun v a => Memory.valueInv conf v refs (a, f, tf, heap)) rootVars addresses)
    (perm : roots.Perm rootVars) (good : goodDimindex width)
    (seenImage : (holFapply tf '' {key | sptDomain s1 key}) ⊆ {ptr | ptr ∈ p1})
    (refImage : (holFapply f '' {key | sptDomain refs key ∧ ¬ sptDomain r1 key}) ⊆ {ptr | ptr ∈ p1})
    (mapInRefs : ∀ key, Memory.mapDomain f key → sptDomain refs key)
    (subset : sptSubspt r1 refs) (architecture : limits.arch64Bit = decide (width = 64))
    (sizing : DataSem.sizeOfValues limits roots r1 s1 = (n2, r2, s2)) :
    ∃ p2 : List Nat, (p2.map (Memory.lookupLen heap)).sum ≤ n2 + (p1.map (Memory.lookupLen heap)).sum ∧
      traverseHeap heap p1 addresses p2 ∧ sptSubspt r2 refs ∧
      (holFapply tf '' {key | sptDomain s2 key}) ⊆ {ptr | ptr ∈ p2} ∧
      (holFapply f '' {key | sptDomain refs key ∧ ¬ sptDomain r2 key}) ⊆ {ptr | ptr ∈ p2} := by
  have mapInRefs' : ∀ key ptr, f.lookup key = some ptr → sptLookup key refs ≠ none := by
    intro key ptr mapped absent
    have present := mapInRefs key ⟨ptr, mapped⟩
    simp [sptDomain, absent] at present
  have cells' : ∀ key ptr, Memory.reachableRefs rootVars refs key → f.lookup key = some ptr →
      Memory.bcRefInv conf key refs (f, tf, heap, be) := by
    intro key ptr reachable mapped
    exact cells key ⟨reachable, ptr, mapped⟩
  have covered : sizeVisited refs r1 s1 f tf p1 := by
    constructor
    · intro key present
      exact seenImage ⟨key, present, rfl⟩
    · intro key present absent
      apply refImage
      refine ⟨key, ?_, rfl⟩
      constructor
      · simpa [sptDomain, Option.isSome_iff_ne_none] using present
      · simp [sptDomain, absent]
  obtain ⟨p2, bound, traversal, sub, coverage⟩ :=
    sizeSound_all limits conf roots rootVars addresses refs r1 s1 f tf heap be p1
      good architecture perm related noThunks subset covered mapInRefs' cells'
  simp only [sizing] at bound sub coverage
  refine ⟨p2, bound, traversal, sub, ?_, ?_⟩
  · rintro ptr ⟨key, present, rfl⟩
    exact coverage.1 key present
  · rintro ptr ⟨key, ⟨present, absent⟩, rfl⟩
    apply coverage.2 key
    · simpa [sptDomain, Option.isSome_iff_ne_none] using present
    · simpa [sptDomain, Option.isSome_iff_ne_none] using absent

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
