import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.SizeValues

/-! Visited-address bookkeeping for source heap sizing. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend

/-- Flapjack infrastructure: the two source maps send seen timestamps and
removed references into the collector's visited-address list. -/
def sizeVisited (refs remaining : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (f tf : HolFiniteMapExact Nat Nat) (visited : List Nat) : Prop :=
  (∀ key ptr, (sptLookup key seen).isSome = true → tf.lookup key = some ptr → ptr ∈ visited) ∧
  (∀ key ptr, sptLookup key refs ≠ none → sptLookup key remaining = none →
    f.lookup key = some ptr → ptr ∈ visited)

/-- Flapjack infrastructure: extending the visited list retains both map
coverage conditions. -/
theorem sizeVisited_mono (refs remaining : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (f tf : HolFiniteMapExact Nat Nat) (before after : List Nat)
    (valid : sizeVisited refs remaining seen f tf before)
    (subset : ∀ ptr ∈ before, ptr ∈ after) : sizeVisited refs remaining seen f tf after := by
  exact ⟨fun key ptr seenKey mapKey => subset ptr (valid.1 key ptr seenKey mapKey),
    fun key ptr inRefs absent mapKey => subset ptr (valid.2 key ptr inRefs absent mapKey)⟩

/-- Flapjack infrastructure: recording a newly visited block timestamp and
its mapped heap address preserves both map coverage conditions. -/
theorem sizeVisited_insertStamp (refs remaining : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (f tf : HolFiniteMapExact Nat Nat) (visited : List Nat) (stamp ptr : Nat)
    (valid : sizeVisited refs remaining seen f tf visited) (mapped : tf.lookup stamp = some ptr) :
    sizeVisited refs remaining (sptInsert stamp () seen) f tf (ptr :: visited) := by
  refine ⟨?_, ?_⟩
  · intro key target present lookup
    by_cases equal : key = stamp
    · subst key
      have same : target = ptr := Option.some.inj (lookup.symm.trans mapped)
      simp [same]
    · have previous : (sptLookup key seen).isSome = true := by
        simpa [sptLookup_sptInsert_ne stamp key () seen equal] using present
      exact List.mem_cons_of_mem _ (valid.1 key target previous lookup)
  · intro key target inRefs absent lookup
    exact List.mem_cons_of_mem _ (valid.2 key target inRefs absent lookup)

/-- Flapjack infrastructure: removing a reference from the source work tree
and visiting its mapped cell preserves both map coverage conditions. -/
theorem sizeVisited_deleteRef (refs remaining : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (f tf : HolFiniteMapExact Nat Nat) (visited : List Nat) (index ptr : Nat)
    (valid : sizeVisited refs remaining seen f tf visited) (mapped : f.lookup index = some ptr) :
    sizeVisited refs (sptDelete index remaining) seen f tf (ptr :: visited) := by
  refine ⟨?_, ?_⟩
  · intro key target present lookup
    exact List.mem_cons_of_mem _ (valid.1 key target present lookup)
  · intro key target inRefs absent lookup
    by_cases equal : key = index
    · subst key
      have same : target = ptr := Option.some.inj (lookup.symm.trans mapped)
      simp [same]
    · have previouslyAbsent : sptLookup key remaining = none := by
        simpa [sptLookup_sptDelete, equal] using absent
      exact List.mem_cons_of_mem _ (valid.2 key target inRefs previouslyAbsent lookup)

/-- Flapjack infrastructure: the source sizing result is sound when it has a
bounded heap traversal, retains a reference submap, and covers the updated
seen and removed-reference maps with the visited list. -/
def sizeSound {width : Nat} [NeZero width] (limits : DataSem.Limits) (values : List DataSem.Value)
    (refs remaining : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (addresses : List (HeapAddress (WordLocW width)))
    (f tf : HolFiniteMapExact Nat Nat) (heap : Memory.ValueHeap width) (visited : List Nat) : Prop :=
  let result := DataSem.sizeOfValues limits values remaining seen
  ∃ after, (after.map (Memory.lookupLen heap)).sum ≤ result.1 + (visited.map (Memory.lookupLen heap)).sum ∧
    traverseHeap heap visited addresses after ∧ sptSubspt result.2.1 refs ∧
    sizeVisited refs result.2.1 result.2.2 f tf after

/-- Flapjack infrastructure: an atomic sizing case that leaves source
reference and timestamp trees unchanged preserves the complete sizing
bookkeeping whenever it has a bounded traversal. -/
theorem sizeSound_atomic {width : Nat} [NeZero width] (limits : DataSem.Limits) (value : DataSem.Value)
    (refs remaining : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (visited : List Nat)
    (subset : sptSubspt remaining refs) (covered : sizeVisited refs remaining seen f tf visited)
    (unchanged : (DataSem.sizeOfValues limits [value] remaining seen).2 = (remaining, seen))
    (bounded : ∃ after, traverseHeap heap visited [address] after ∧
      (after.map (Memory.lookupLen heap)).sum ≤
        (DataSem.sizeOfValues limits [value] remaining seen).1 + (visited.map (Memory.lookupLen heap)).sum) :
    sizeSound limits [value] refs remaining seen [address] f tf heap visited := by
  obtain ⟨after, traversal, cost⟩ := bounded
  have outputRefs : (DataSem.sizeOfValues limits [value] remaining seen).2.1 = remaining :=
    congrArg Prod.fst unchanged
  have outputSeen : (DataSem.sizeOfValues limits [value] remaining seen).2.2 = seen :=
    congrArg Prod.snd unchanged
  refine ⟨after, cost, traversal, ?_, ?_⟩
  · simpa only [outputRefs] using subset
  · rw [outputRefs, outputSeen]
    apply sizeVisited_mono refs remaining seen f tf visited after covered
    exact fun ptr member => traverseHeap_visited_mono heap visited [address] after traversal member

/-- Flapjack infrastructure: an immediate or heap-allocated number satisfies
the full singleton sizing bookkeeping at either supported word width. -/
theorem sizeSound_number {width : Nat} [NeZero width] (limits : DataSem.Limits) (conf : Config) (value : Int)
    (refs remaining : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (visited : List Nat)
    (good : goodDimindex width) (architecture : limits.arch64Bit = decide (width = 64))
    (related : Memory.valueInv conf (.number value) refs (address, f, tf, heap))
    (subset : sptSubspt remaining refs) (covered : sizeVisited refs remaining seen f tf visited) :
    sizeSound limits [.number value] refs remaining seen [address] f tf heap visited := by
  apply sizeSound_atomic limits (.number value) refs remaining seen address f tf heap visited subset covered
  · simp [DataSem.sizeOfValues]
  · have same := (Memory.valueInv_number conf value remaining address f tf heap).mpr
      ((Memory.valueInv_number conf value refs address f tf heap).mp related)
    exact sizeOf_number_traversal limits conf value remaining seen address f tf heap visited good architecture same

/-- Flapjack infrastructure: a Word64 value satisfies the complete singleton
sizing bookkeeping. -/
theorem sizeSound_word64 {width : Nat} [NeZero width] (limits : DataSem.Limits) (conf : Config) (value : BitVec 64)
    (refs remaining : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (visited : List Nat)
    (related : Memory.valueInv conf (.word64 value) refs (address, f, tf, heap))
    (subset : sptSubspt remaining refs) (covered : sizeVisited refs remaining seen f tf visited) :
    sizeSound limits [.word64 value] refs remaining seen [address] f tf heap visited := by
  apply sizeSound_atomic limits (.word64 value) refs remaining seen address f tf heap visited subset covered
  · simp [DataSem.sizeOfValues]
  · have same := (Memory.valueInv_word64 conf value remaining address f tf heap).mpr
      ((Memory.valueInv_word64 conf value refs address f tf heap).mp related)
    exact sizeOf_word64_traversal limits conf value remaining seen address f tf heap visited same

/-- Flapjack infrastructure: a code pointer satisfies the complete singleton
sizing bookkeeping without visiting another heap cell. -/
theorem sizeSound_codePtr {width : Nat} [NeZero width] (limits : DataSem.Limits) (conf : Config) (value : Nat)
    (refs remaining : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (visited : List Nat)
    (related : Memory.valueInv conf (.codePtr value) refs (address, f, tf, heap))
    (subset : sptSubspt remaining refs) (covered : sizeVisited refs remaining seen f tf visited) :
    sizeSound limits [.codePtr value] refs remaining seen [address] f tf heap visited := by
  apply sizeSound_atomic limits (.codePtr value) refs remaining seen address f tf heap visited subset covered
  · simp [DataSem.sizeOfValues]
  · have same := (Memory.valueInv_codePtr conf value remaining address f tf heap).mpr
      ((Memory.valueInv_codePtr conf value refs address f tf heap).mp related)
    exact sizeOf_codePtr_traversal limits conf value remaining seen address f tf heap visited same

/-- Flapjack infrastructure: an empty source block is immediate and
preserves the complete singleton sizing bookkeeping. -/
theorem sizeSound_emptyBlock {width : Nat} [NeZero width] (limits : DataSem.Limits) (conf : Config) (stamp tag : Nat)
    (refs remaining : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (visited : List Nat)
    (related : Memory.valueInv conf (.block stamp tag []) refs (address, f, tf, heap))
    (subset : sptSubspt remaining refs) (covered : sizeVisited refs remaining seen f tf visited) :
    sizeSound limits [.block stamp tag []] refs remaining seen [address] f tf heap visited := by
  apply sizeSound_atomic limits (.block stamp tag []) refs remaining seen address f tf heap visited subset covered
  · simp [DataSem.sizeOfValues]
  · have same := (Memory.valueInv_block conf stamp tag [] remaining address f tf heap).mpr
      ((Memory.valueInv_block conf stamp tag [] refs address f tf heap).mp related)
    exact sizeOf_emptyBlock_traversal limits conf stamp tag remaining seen address f tf heap visited same

/-- Flapjack infrastructure: an empty collection of roots preserves the
source bookkeeping without traversing the heap. -/
theorem sizeSound_nil {width : Nat} [NeZero width] (limits : DataSem.Limits)
    (refs remaining : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (f tf : HolFiniteMapExact Nat Nat) (heap : Memory.ValueHeap width) (visited : List Nat)
    (subset : sptSubspt remaining refs) (covered : sizeVisited refs remaining seen f tf visited) :
    sizeSound limits [] refs remaining seen [] f tf heap visited := by
  exact ⟨visited, by simp [DataSem.sizeOfValues], traverseHeap.empty visited,
    by simpa [DataSem.sizeOfValues] using subset,
    by simpa [DataSem.sizeOfValues] using covered⟩

/-- Flapjack infrastructure: a previously visited block preserves the full
sizing invariant even when the remaining reference tree has shrunk. -/
theorem sizeSound_seenBlock {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (stamp tag : Nat) (head : DataSem.Value)
    (tail : List DataSem.Value) (refs remaining : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (visited : List Nat)
    (related : Memory.valueInv conf (.block stamp tag (head :: tail)) refs (address, f, tf, heap))
    (already : (sptLookup stamp seen).isSome = true)
    (subset : sptSubspt remaining refs) (covered : sizeVisited refs remaining seen f tf visited) :
    sizeSound limits [.block stamp tag (head :: tail)] refs remaining seen [address] f tf heap visited := by
  apply sizeSound_atomic limits _ refs remaining seen address f tf heap visited subset covered
  · simp [DataSem.sizeOfValues, already]
  · have block := (Memory.valueInv_block conf stamp tag (head :: tail) refs address f tf heap).mp related
    simp only [List.cons_ne_nil, ↓reduceIte] at block
    obtain ⟨ptr, children, _, timestamp, rfl, _⟩ := block
    exact ⟨visited, traverseHeap.seen visited ptr _ (covered.1 stamp ptr already timestamp),
      by simp [DataSem.sizeOfValues, already]⟩

/-- Flapjack infrastructure: a reference already removed from the source
work tree is already visited and preserves the complete sizing invariant. -/
theorem sizeSound_seenRef {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (bit : Bool) (index : Nat)
    (refs remaining : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (visited : List Nat)
    (related : Memory.valueInv conf (.refPtr bit index) refs (address, f, tf, heap))
    (noThunks : DataSem.noThunksInRefs refs) (missing : sptLookup index remaining = none)
    (mapInRefs : ∀ key ptr, f.lookup key = some ptr → sptLookup key refs ≠ none)
    (subset : sptSubspt remaining refs) (covered : sizeVisited refs remaining seen f tf visited) :
    sizeSound limits [.refPtr bit index] refs remaining seen [address] f tf heap visited := by
  apply sizeSound_atomic limits _ refs remaining seen address f tf heap visited subset covered
  · simp [sizeOfValues_missingRef limits bit index remaining seen missing]
  · exact sizeOf_seenRef_traversal limits conf bit index remaining refs seen address f tf heap visited
      related noThunks missing mapInRefs covered.2

/-- Flapjack infrastructure: the recursive sizing result for the children of
an unseen block extends to the block, including the updated map coverage. -/
theorem sizeSound_freshBlock {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (stamp tag : Nat) (head : DataSem.Value)
    (tail : List DataSem.Value) (refs remaining : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (visited : List Nat)
    (related : Memory.valueInv conf (.block stamp tag (head :: tail)) refs (address, f, tf, heap))
    (fresh : (sptLookup stamp seen).isSome = false)
    (subset : sptSubspt remaining refs) (covered : sizeVisited refs remaining seen f tf visited)
    (childrenSound : ∀ ptr children,
      List.Forall₂ (fun value addr => Memory.valueInv conf value refs (addr, f, tf, heap)) (head :: tail) children →
      tf.lookup stamp = some ptr → heapLookup ptr heap = some (Memory.blockRep tag children) →
      sptSubspt remaining refs → sizeVisited refs remaining (sptInsert stamp () seen) f tf (ptr :: visited) →
      sizeSound limits (head :: tail) refs remaining (sptInsert stamp () seen) children f tf heap (ptr :: visited)) :
    sizeSound limits [.block stamp tag (head :: tail)] refs remaining seen [address] f tf heap visited := by
  have block := (Memory.valueInv_block conf stamp tag (head :: tail) refs address f tf heap).mp related
  simp only [List.cons_ne_nil, ↓reduceIte] at block
  obtain ⟨ptr, children, valuesRel, timestamp, rfl, found⟩ := block
  have child := childrenSound ptr children valuesRel timestamp found subset
    (sizeVisited_insertStamp refs remaining seen f tf visited stamp ptr covered timestamp)
  obtain ⟨after, bound, traversal, subOut, coverOut⟩ := child
  have lengths := valuesRel.length_eq
  have ptrCost : Memory.lookupLen heap ptr = (head :: tail).length + 1 := by
    simp [Memory.lookupLen, found, Memory.blockRep, elLength, ← lengths]
  simp only [List.map_cons, List.sum_cons, ptrCost] at bound
  cases result : DataSem.sizeOfValues limits (head :: tail) remaining (sptInsert stamp () seen) with
  | mk n rest =>
    cases rest with
    | mk remaining' seen' =>
      simp only [result] at bound subOut coverOut
      refine ⟨after, ?_, ?_, ?_, ?_⟩
      · simp [DataSem.sizeOfValues, fresh, result]
        simp only [List.length_cons] at bound
        omega
      · apply traverseHeap.visit (children := children)
        · simpa [Memory.blockRep] using found
        · exact traversal
      · simpa [DataSem.sizeOfValues, fresh, result] using subOut
      · simpa [DataSem.sizeOfValues, fresh, result] using coverOut

/-- Flapjack infrastructure: every pointer presented as a root is in the
visited set at the end of a heap traversal. -/
theorem traverseHeap_roots_visited {α β : Type} (heap : List (HeapElement α β))
    (before : List Nat) (roots : List (HeapAddress α)) (after : List Nat)
    (run : traverseHeap heap before roots after) :
    ∀ ptr value, .pointer ptr value ∈ roots → ptr ∈ after := by
  induction run with
  | empty => simp
  | @append before middle after first second vars firstRun secondRun same ih1 ih2 =>
    intro ptr value member
    have inAppend : .pointer ptr value ∈ first ++ second := (Iff.of_eq (congrFun same _)).mp member
    rcases List.mem_append.mp inAppend with inFirst | inSecond
    · exact traverseHeap_visited_mono heap middle second after secondRun (ih1 ptr value inFirst)
    · exact ih2 ptr value inSecond
  | data => simp
  | seen visited ptr value present =>
    intro target other member
    simp only [List.mem_singleton, HeapAddress.pointer.injEq] at member
    rcases member with ⟨rfl, _⟩
    exact present
  | @visit visited after ptr len value children payload found traversal ih =>
    intro target other member
    simp only [List.mem_singleton, HeapAddress.pointer.injEq] at member
    rcases member with ⟨rfl, _⟩
    exact traverseHeap_visited_mono heap (target :: visited) children after traversal (by simp)

/-- Flapjack infrastructure: sizing a live byte-array reference removes it
from the work tree while recording its represented heap address. -/
theorem sizeSound_byteArray {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (bit : Bool) (index : Nat)
    (compareByContents : Bool) (bytes : List (BitVec 8))
    (refs remaining : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (be : Bool) (visited : List Nat)
    (good : goodDimindex width) (architecture : limits.arch64Bit = decide (width = 64))
    (related : Memory.valueInv conf (.refPtr bit index) refs (address, f, tf, heap))
    (noThunks : DataSem.noThunksInRefs refs) (subset : sptSubspt remaining refs)
    (found : sptLookup index remaining = some (.byteArray compareByContents bytes))
    (refInv : Memory.bcRefInv conf index refs (f, tf, heap, be))
    (covered : sizeVisited refs remaining seen f tf visited) :
    sizeSound limits [.refPtr bit index] refs remaining seen [address] f tf heap visited := by
  have direct := (Memory.valueInv_refPtr_notThunk conf bit index refs address f tf heap
    (noThunks index)).mp related
  obtain ⟨⟨ptr, mapFound⟩, _, addressEq⟩ := direct
  have address' : address = .pointer ptr (Memory.refPtrAnnot conf (sptLookup index refs)) := by
    simpa [holFapply_of_lookup mapFound] using addressEq
  obtain ⟨after, traversal, cost⟩ := sizeOf_byteArray_traversal limits conf bit index
    compareByContents bytes remaining refs seen address f tf heap be visited good architecture
    related noThunks subset found refInv
  have ptrPresent : ptr ∈ after := by
    apply traverseHeap_roots_visited heap visited [address] after traversal ptr
      (Memory.refPtrAnnot conf (sptLookup index refs))
    simp [address']
  have outputCoverage := sizeVisited_mono refs (sptDelete index remaining) seen f tf
    (ptr :: visited) after (sizeVisited_deleteRef refs remaining seen f tf visited index ptr covered mapFound)
    (by
      intro key member
      rcases List.mem_cons.mp member with rfl | old
      · exact ptrPresent
      · exact traverseHeap_visited_mono heap visited [address] after traversal old)
  refine ⟨after, cost, traversal, ?_, ?_⟩
  · rw [sizeOfValues_byteArray limits bit index compareByContents bytes remaining seen found]
    exact sptSubsptTrans _ _ _ ⟨DataSem.sptDelete_subspt remaining index, subset⟩
  · simpa [sizeOfValues_byteArray limits bit index compareByContents bytes remaining seen found] using outputCoverage

/-- Flapjack infrastructure: recursive sizing of a live value array preserves
both map coverage conditions after removing its source reference. -/
theorem sizeSound_refArray {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (bit : Bool) (index : Nat)
    (values : List DataSem.Value) (refs remaining : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (be : Bool) (visited : List Nat)
    (related : Memory.valueInv conf (.refPtr bit index) refs (address, f, tf, heap))
    (noThunks : DataSem.noThunksInRefs refs) (subset : sptSubspt remaining refs)
    (found : sptLookup index remaining = some (.valueArray values))
    (refInv : Memory.bcRefInv conf index refs (f, tf, heap, be))
    (covered : sizeVisited refs remaining seen f tf visited)
    (childrenSound : ∀ ptr children,
      List.Forall₂ (fun addr item => Memory.valueInv conf item refs (addr, f, tf, heap)) children values →
      f.lookup index = some ptr → heapLookup ptr heap = some (Memory.refBlock children) →
      sptSubspt (sptDelete index remaining) refs → sizeVisited refs (sptDelete index remaining) seen f tf (ptr :: visited) →
      sizeSound limits values refs (sptDelete index remaining) seen children f tf heap (ptr :: visited)) :
    sizeSound limits [.refPtr bit index] refs remaining seen [address] f tf heap visited := by
  have original := (sptSubsptLookup remaining refs).mp subset index (.valueArray values) found
  have direct := (Memory.valueInv_refPtr_notThunk conf bit index refs address f tf heap
    (noThunks index)).mp related
  obtain ⟨⟨ptr, mapFound⟩, _, addressEq⟩ := direct
  have address' : address = .pointer ptr (Memory.refPtrAnnot conf (sptLookup index refs)) := by
    simpa [holFapply_of_lookup mapFound] using addressEq
  subst address
  have cell := refInv
  simp only [Memory.bcRefInv, mapFound, original] at cell
  obtain ⟨children, heapFound, valuesRel⟩ := cell
  have child := childrenSound ptr children valuesRel mapFound heapFound
    (sptSubsptTrans _ _ _ ⟨DataSem.sptDelete_subspt remaining index, subset⟩)
    (sizeVisited_deleteRef refs remaining seen f tf visited index ptr covered mapFound)
  obtain ⟨after, bound, traversal, subOut, coverOut⟩ := child
  have lengths := valuesRel.length_eq
  have ptrCost : Memory.lookupLen heap ptr = values.length + 1 := by
    simp [Memory.lookupLen, heapFound, Memory.refBlock, elLength, lengths]
  simp only [List.map_cons, List.sum_cons, ptrCost] at bound
  cases result : DataSem.sizeOfValues limits values (sptDelete index remaining) seen with
  | mk n rest =>
    cases rest with
    | mk remaining' seen' =>
      simp only [result] at bound subOut coverOut
      refine ⟨after, ?_, ?_, ?_, ?_⟩
      · rw [sizeOfValues_refArray limits bit index values remaining seen found, result]
        dsimp only
        omega
      · rw [holFapply_of_lookup mapFound]
        apply traverseHeap.visit (children := children)
        · simpa [Memory.refBlock] using heapFound
        · exact traversal
      · simpa [sizeOfValues_refArray limits bit index values remaining seen found, result] using subOut
      · simpa [sizeOfValues_refArray limits bit index values remaining seen found, result] using coverOut

/-- Flapjack infrastructure: recursive sizing of a live mutable block preserves
the reference submap and visited-address coverage. -/
theorem sizeSound_mutBlock {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (bit : Bool) (index tag : Nat) (finalised : Bool)
    (left : List DataSem.Value) (value : DataSem.Value) (right : List DataSem.Value)
    (refs remaining : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (be : Bool) (visited : List Nat)
    (related : Memory.valueInv conf (.refPtr bit index) refs (address, f, tf, heap))
    (noThunks : DataSem.noThunksInRefs refs) (subset : sptSubspt remaining refs)
    (found : sptLookup index remaining = some (.mutBlock tag finalised left value right))
    (refInv : Memory.bcRefInv conf index refs (f, tf, heap, be))
    (covered : sizeVisited refs remaining seen f tf visited)
    (childrenSound : ∀ ptr children,
      List.Forall₂ (fun addr item => Memory.valueInv conf item refs (addr, f, tf, heap)) children (left ++ [value] ++ right) →
      f.lookup index = some ptr → heapLookup ptr heap = some (Memory.blockRep tag children) →
      sptSubspt (sptDelete index remaining) refs → sizeVisited refs (sptDelete index remaining) seen f tf (ptr :: visited) →
      sizeSound limits (left ++ [value] ++ right) refs (sptDelete index remaining) seen children f tf heap (ptr :: visited)) :
    sizeSound limits [.refPtr bit index] refs remaining seen [address] f tf heap visited := by
  have original := (sptSubsptLookup remaining refs).mp subset index (.mutBlock tag finalised left value right) found
  have direct := (Memory.valueInv_refPtr_notThunk conf bit index refs address f tf heap
    (noThunks index)).mp related
  obtain ⟨⟨ptr, mapFound⟩, _, addressEq⟩ := direct
  have address' : address = .pointer ptr (Memory.refPtrAnnot conf (sptLookup index refs)) := by
    simpa [holFapply_of_lookup mapFound] using addressEq
  subst address
  have cell := refInv
  simp only [Memory.bcRefInv, mapFound, original] at cell
  obtain ⟨_, _, children, heapFound, valuesRel⟩ := cell
  have child := childrenSound ptr children valuesRel mapFound heapFound
    (sptSubsptTrans _ _ _ ⟨DataSem.sptDelete_subspt remaining index, subset⟩)
    (sizeVisited_deleteRef refs remaining seen f tf visited index ptr covered mapFound)
  obtain ⟨after, bound, traversal, subOut, coverOut⟩ := child
  have lengths := valuesRel.length_eq
  have ptrCost : Memory.lookupLen heap ptr = left.length + right.length + 2 := by
    simp [Memory.lookupLen, heapFound, Memory.blockRep, elLength, lengths]
    omega
  simp only [List.map_cons, List.sum_cons, ptrCost] at bound
  cases result : DataSem.sizeOfValues limits (left ++ [value] ++ right) (sptDelete index remaining) seen with
  | mk n rest =>
    cases rest with
    | mk remaining' seen' =>
      simp only [result] at bound subOut coverOut
      refine ⟨after, ?_, ?_, ?_, ?_⟩
      · rw [sizeOfValues_mutBlock limits bit index tag finalised left value right remaining seen found, result]
        dsimp only
        omega
      · rw [holFapply_of_lookup mapFound]
        apply traverseHeap.visit (children := children)
        · simpa [Memory.blockRep] using heapFound
        · exact traversal
      · rw [sizeOfValues_mutBlock limits bit index tag finalised left value right remaining seen found, result]
        exact subOut
      · rw [sizeOfValues_mutBlock limits bit index tag finalised left value right remaining seen found, result]
        exact coverOut

/-- Flapjack infrastructure: compose tail-first source sizing with heap
traversal of a corresponding head and tail of addresses. -/
theorem sizeSound_cons {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (value : DataSem.Value) (values : List DataSem.Value)
    (refs remaining : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (addresses : List (HeapAddress (WordLocW width)))
    (f tf : HolFiniteMapExact Nat Nat) (heap : Memory.ValueHeap width) (visited : List Nat)
    (tailSound : sizeSound limits values refs remaining seen addresses f tf heap visited)
    (headSound : ∀ middle,
      sptSubspt (DataSem.sizeOfValues limits values remaining seen).2.1 refs →
      sizeVisited refs (DataSem.sizeOfValues limits values remaining seen).2.1
        (DataSem.sizeOfValues limits values remaining seen).2.2 f tf middle →
      sizeSound limits [value] refs (DataSem.sizeOfValues limits values remaining seen).2.1
        (DataSem.sizeOfValues limits values remaining seen).2.2 [address] f tf heap middle) :
    sizeSound limits (value :: values) refs remaining seen (address :: addresses) f tf heap visited := by
  obtain ⟨middle, tailBound, tailRun, tailSub, tailCovered⟩ := tailSound
  obtain ⟨after, headBound, headRun, headSub, headCovered⟩ := headSound middle tailSub tailCovered
  cases tailResult : DataSem.sizeOfValues limits values remaining seen with
  | mk n rest =>
    cases rest with
    | mk remaining' seen' =>
      simp only [tailResult] at tailBound headBound headSub headCovered
      cases headResult : DataSem.sizeOfValues limits [value] remaining' seen' with
      | mk m rest =>
        cases rest with
        | mk remaining'' seen'' =>
          simp only [headResult] at headBound headSub headCovered
          refine ⟨after, ?_, ?_, ?_, ?_⟩
          · simp only [sizeOfValues_cons, tailResult, headResult]
            omega
          · apply traverseHeap.append tailRun headRun
            ext root
            simp [or_comm]
          · simp only [sizeOfValues_cons, tailResult, headResult]
            exact headSub
          · simp only [sizeOfValues_cons, tailResult, headResult]
            exact headCovered

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
