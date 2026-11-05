import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CombinedGenerational
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.FullStore
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.GcConfig
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.DoPartial
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
import Flapjack.Compiler.Backend.GenGcPartial.Proofs.Similarity

/-! Generational collectors under the heap/store invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.Compiler.Backend.GcCombined

/-- If an allocation fits in the available space, the chosen trigger is no
smaller than that allocation. This factors the source's local trigger fact. -/
theorem newTrig_alloc_le {width : Nat} [NeZero width] (space alloc : BitVec width) (limits : List Nat)
    (fits : alloc ≤ space) : alloc ≤ newTrig space alloc limits := by
  have fitsNat : alloc.toNat ≤ space.toNat := by simpa only [BitVec.le_def] using fits
  by_cases allocLeGen : alloc.toNat ≤ (getGenSize limits : BitVec width).toNat
  ·
    have minBound : min space.toNat (getGenSize limits : BitVec width).toNat < 2 ^ width :=
      lt_of_le_of_lt (Nat.min_le_left _ _) space.isLt
    simp only [newTrig, allocLeGen, ↓reduceIte, BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt minBound]
    exact Nat.le_min.mpr ⟨fitsNat, allocLeGen⟩
  · have notSmall : ¬ space.toNat < alloc.toNat := by omega
    by_cases aligned : holByteAligned alloc = true
    · simp [newTrig, allocLeGen, notSmall, aligned]
    · simp [newTrig, allocLeGen, notSmall, aligned, BitVec.le_def, fitsNat]

/-- The trigger offset never exceeds the available heap space. -/
theorem newTrig_le_space {width : Nat} [NeZero width] (space alloc : BitVec width) (limits : List Nat) :
    newTrig space alloc limits ≤ space := by
  by_cases allocLeGen : alloc.toNat ≤ (getGenSize limits : BitVec width).toNat
  · have bound : min space.toNat (getGenSize limits : BitVec width).toNat < 2 ^ width :=
      lt_of_le_of_lt (Nat.min_le_left _ _) space.isLt
    simp only [newTrig, allocLeGen, ↓reduceIte, BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    exact Nat.min_le_left _ _
  · by_cases small : space.toNat < alloc.toNat
    · simp [newTrig, allocLeGen, small]
    · by_cases aligned : holByteAligned alloc = true
      · simp [newTrig, allocLeGen, small, aligned, BitVec.le_def]
        omega
      · simp [newTrig, allocLeGen, small, aligned]

/-- In a supported machine dimension, byte alignment means divisibility by
the number of bytes per word. -/
theorem byteAligned_iff_divisible {width : Nat} [NeZero width] (word : BitVec width)
    (good : goodDimindex width) : holByteAligned word = true ↔ word.toNat % (width / 8) = 0 := by
  rcases good with rfl | rfl
  · simpa [holByteAligned, show holLOG2 4 = 2 from holLOG_UNIQUE 2 4 2 ⟨by decide, by decide⟩] using
      holAligned_iff 2 word
  · simpa [holByteAligned, show holLOG2 8 = 3 from holLOG_UNIQUE 2 8 3 ⟨by decide, by decide⟩] using
      holAligned_iff 3 word

/-- A word-sized multiple is byte aligned in either supported dimension. -/
theorem byteAligned_wordMultiple {width : Nat} [NeZero width] (word : BitVec width)
    (good : goodDimindex width) : holByteAligned (wordSemBytesInWord * word) = true := by
  rw [byteAligned_iff_divisible _ good]
  rcases good with rfl | rfl <;>
    norm_num [BitVec.toNat_mul, wordSemBytesInWord, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd,
      Nat.mul_mod]

/-- Every configured generation size is a whole number of machine words. -/
theorem genSize_byteAligned {width : Nat} [NeZero width] (limits : List Nat)
    (good : goodDimindex width) : holByteAligned (getGenSize limits : BitVec width) = true := by
  cases limits with
  | nil => exact byteAligned_wordMultiple (-1) good
  | cons size rest =>
    simp only [getGenSize]
    split <;> exact byteAligned_wordMultiple _ good

/-- A byte-aligned available space yields a byte-aligned trigger offset. -/
theorem newTrig_byteAligned {width : Nat} [NeZero width] (space alloc : BitVec width) (limits : List Nat)
    (good : goodDimindex width) (aligned : holByteAligned space = true) :
    holByteAligned (newTrig space alloc limits) = true := by
  by_cases allocLeGen : alloc.toNat ≤ (getGenSize limits : BitVec width).toNat
  · by_cases spaceLeGen : space.toNat ≤ (getGenSize limits : BitVec width).toNat
    · simpa [newTrig, allocLeGen, Nat.min_eq_left spaceLeGen] using aligned
    · have genLeSpace : (getGenSize limits : BitVec width).toNat ≤ space.toNat := by omega
      simpa [newTrig, allocLeGen, Nat.min_eq_right genLeSpace] using genSize_byteAligned limits good
  · by_cases small : space.toNat < alloc.toNat
    · simpa [newTrig, allocLeGen, small] using aligned
    · by_cases allocAligned : holByteAligned alloc = true
      · simp [newTrig, allocLeGen, small, allocAligned]
      · simpa [newTrig, allocLeGen, small, allocAligned] using aligned

/-- A bounded aligned byte offset has a whole-word representation whose
word count is bounded by the available count. -/
theorem byteAligned_boundedWords {width : Nat} [NeZero width] (word : BitVec width) (n : Nat)
    (good : goodDimindex width) (aligned : holByteAligned word = true)
    (bound : word.toNat ≤ n * (width / 8)) :
    ∃ k, word = wordSemBytesInWord * BitVec.ofNat width k ∧ k ≤ n := by
  have divisible := (byteAligned_iff_divisible word good).mp aligned
  refine ⟨word.toNat / (width / 8), ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rcases good with rfl | rfl <;>
      norm_num [wordSemBytesInWord, BitVec.toNat_mul, BitVec.toNat_ofNat] at divisible ⊢ <;>
      omega
  · rcases good with rfl | rfl <;> norm_num at bound ⊢ <;> omega

/-- The new trigger is a whole-word offset bounded by the available words. -/
theorem newTrig_boundedWords {width : Nat} [NeZero width] (space alloc : BitVec width)
    (limits : List Nat) (n : Nat) (good : goodDimindex width)
    (aligned : holByteAligned space = true) (bound : space.toNat ≤ n * (width / 8)) :
    ∃ k, newTrig space alloc limits = wordSemBytesInWord * BitVec.ofNat width k ∧ k ≤ n := by
  apply byteAligned_boundedWords _ n good (newTrig_byteAligned space alloc limits good aligned)
  have le := BitVec.le_def.mp (newTrig_le_space space alloc limits)
  omega

/-- A trigger for a word-count-sized heap has a word count no larger than
the supplied count, including when the input word arithmetic wraps. -/
theorem newTrig_wordCount {width : Nat} [NeZero width] (n : Nat) (alloc : BitVec width)
    (limits : List Nat) (good : goodDimindex width) :
    ∃ k, newTrig (wordSemBytesInWord * BitVec.ofNat width n) alloc limits =
      wordSemBytesInWord * BitVec.ofNat width k ∧ k ≤ n := by
  apply newTrig_boundedWords _ alloc limits n good (byteAligned_wordMultiple _ good)
  rcases good with rfl | rfl <;>
    norm_num [wordSemBytesInWord, BitVec.toNat_mul, BitVec.toNat_ofNat] <;> omega

/-- Moving an allocation pointer earlier within a bounded heap cannot reduce
the unsigned byte space remaining before its end. -/
theorem partialAvailableSpace_mono {width : Nat} [NeZero width] (base : BitVec width)
    (earlier later finish : Nat) (ordered : earlier ≤ later) (within : later ≤ finish)
    (bound : finish * (width / 8) < 2 ^ width) (good : goodDimindex width) :
    (base + wordSemBytesInWord * BitVec.ofNat width finish) -
        (base + wordSemBytesInWord * BitVec.ofNat width later) ≤
      (base + wordSemBytesInWord * BitVec.ofNat width finish) -
        (base + wordSemBytesInWord * BitVec.ofNat width earlier) := by
  have bytesPos : 0 < width / 8 := by rcases good with rfl | rfl <;> decide
  have finishSmall : finish < 2 ^ width := by
    have le := Nat.le_mul_of_pos_right finish bytesPos
    omega
  have earlierSmall : earlier < 2 ^ width := by omega
  have laterSmall : later < 2 ^ width := by omega
  have cancelCommon (x y z : BitVec width) : (x + y) - (x + z) = y - z := by
    apply BitVec.sub_eq_iff_eq_add.mpr
    calc
      x + y = x + ((y - z) + z) := by rw [BitVec.sub_add_cancel]
      _ = (y - z) + (x + z) := by ac_rfl
  simp only [cancelCommon, ← BitVec.mul_sub,
    BitVec.ofNat_sub_ofNat_of_le finish later laterSmall within,
    BitVec.ofNat_sub_ofNat_of_le finish earlier earlierSmall (le_trans ordered within)]
  have smallerBound : (width / 8) * (finish - later) < 2 ^ width := by
    have le := Nat.mul_le_mul_left (width / 8) (Nat.sub_le finish later)
    rw [Nat.mul_comm] at bound
    omega
  have largerBound : (width / 8) * (finish - earlier) < 2 ^ width := by
    have le := Nat.mul_le_mul_left (width / 8) (Nat.sub_le finish earlier)
    rw [Nat.mul_comm] at bound
    omega
  simp only [BitVec.le_def, BitVec.toNat_mul, wordSemBytesInWord, BitVec.toNat_ofNat]
  rcases good with h | h <;> subst width <;>
    norm_num at smallerBound largerBound ⊢ <;> omega

/-- The partial-selection test guarantees that an allocation still fits if
the collector's new pointer does not pass the previous trigger. -/
theorem partialAllocation_fits {width : Nat} [NeZero width] (conf : Config)
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit newIndex : Nat) (gens : GenState) (limits : List Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool) (curr : BitVec width)
    (selected : wordGenGcCanDoPartial limits store) (indexBound : newIndex ≤ a + sp)
    (heapBound : a + sp + sp1 ≤ heapLength heap) (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit)
    (currLookup : store.lookup .currHeap = some (.word curr)) :
    wordSemTheWord (holFapply store .allocSize) ≤
      (curr + wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1)) -
        (curr + wordSemBytesInWord * BitVec.ofNat width newIndex) := by
  rcases heapMem with ⟨_, byteBound, _, _, _, _, _, oldCurr, other, _, _, oldCurrLookup, _, _, trigger, endHeap, _⟩
  have same : oldCurr = curr := by simpa [oldCurrLookup] using currLookup
  subst oldCurr
  have triggerValue := holFapply_of_lookup trigger
  have endValue := holFapply_of_lookup endHeap
  have chosen : wordSemTheWord (holFapply store .allocSize) ≤
      (curr + wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1)) -
        (curr + wordSemBytesInWord * BitVec.ofNat width (a + sp)) := by
    simpa [wordGenGcCanDoPartial, triggerValue, endValue, wordSemTheWord,
      wordSemBytesInWord, StackRemove.bytesInWord] using selected.2
  have endBound : (a + sp + sp1) * (width / 8) < 2 ^ width :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) byteBound
  have monotone := partialAvailableSpace_mono curr newIndex (a + sp) (a + sp + sp1)
    indexBound (by omega) endBound good
  apply BitVec.le_def.mpr
  have first := BitVec.le_def.mp chosen
  have second := BitVec.le_def.mp monotone
  omega

/-- A selectable partial collection has a nonempty abstract generation list,
and the stored generation-start word represents its first boundary. -/
theorem partialGenStart_store {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width))) (gens : GenState) (refsStart : Nat)
    (limits : List Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (kind : conf.gcKind = .generational limits) (selected : wordGenGcCanDoPartial limits store)
    (related : genStartsInStore conf gens (store.lookup .genStart)) :
    ∃ start tail count,
      gens = .genState count (start :: tail) ∧
      (makePartialConf genConf gens refsStart).genStart = start ∧
      store.lookup .genStart = some (.word (wordSemBytesInWord * BitVec.ofNat width start)) := by
  obtain ⟨word, lookup⟩ := genStartsInStoreImp conf gens _ related
  cases gens with
  | genState count starts =>
    have shape := related
    simp only [lookup, genStartsInStore] at shape
    have lengths := (shape limits kind).1
    have nonempty : limits ≠ [] := selected.1
    cases starts with
    | nil =>
      cases limits with
      | nil => exact False.elim (nonempty rfl)
      | cons head tail => simp at lengths
    | cons start tail =>
      have wordEq := (shape limits kind).2 start tail rfl
      refine ⟨start, tail, count, rfl, ?_, ?_⟩
      · simp [makePartialConf, holHd]
      · simpa only [wordEq, wordSemBytesInWord, StackRemove.bytesInWord] using lookup

/-- The source ML and store invariants provide the heap size, reference
suffix, and generation ordering needed by partial collection. -/
theorem partialSource_conditions {width : Nat} [NeZero width] (conf : Config)
    (values : List DataSem.Value) (references : Spt (BvlSem.Ref DataSem.Value))
    (roots : List (HeapAddress (WordLocW width)))
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (be : Bool) (a sp sp1 limit next : Nat) (gens : GenState) (limits : List Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (source : absMlInv conf values references (roots, heap, be, a, sp, sp1, gens) limit next)
    (kind : conf.gcKind = .generational limits) (selected : wordGenGcCanDoPartial limits store)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    limit = heapLength heap ∧ endsWithRefs (a + sp + sp1) heap ∧
      (makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).genStart ≤ a ∧
      a + sp + sp1 ≤ heapLength heap := by
  rcases source with ⟨rootsOk, heapOk, gcOk, unused, stackOk⟩
  rcases heapMem with ⟨_, _, _, _, _, _, _, curr, other, _, _, _, _, _, _, _, _, _, generations, _⟩
  obtain ⟨start, tail, count, gensEq, startEq, startLookup⟩ :=
    partialGenStart_store conf (makeGcConf limit) gens (a + sp + sp1) limits store kind selected generations
  simp only [gcKindInv, kind] at gcOk
  obtain ⟨genOk, first, second, split, _, refTail⟩ := gcOk
  have startBound : start ≤ a := by
    rw [gensEq] at genOk
    exact genOk.1 start (by simp)
  refine ⟨heapOk.1.symm, ⟨first, second, split, refTail⟩, ?_, ?_⟩
  · simpa [startEq] using startBound
  · simpa [Nat.add_assoc] using unused.2.1

/-- The source unused-space invariant accounts for the data before the free
region and excludes that region from the data mass. -/
theorem partialSource_dataMass {α β : Type} (heap before refs : List (HeapElement α β))
    (allocation free : Nat) (unused : unusedSpaceInv allocation free heap)
    (split : heapSplit (allocation + free) heap = some (before, refs)) :
    GenGcPartial.dataMass heap = allocation + GenGcPartial.dataMass refs := by
  classical
  obtain ⟨data, suffix, dataSplit, allData⟩ := unused.2.2
  obtain ⟨dataLen, _, whole⟩ := heapSplit_heapLength heap data suffix allocation dataSplit
  have dataMass := GenGcPartial.dataMass_of_allData data allData
  by_cases freeZero : free = 0
  · subst free
    simp only [Nat.add_zero] at split
    rw [dataSplit] at split
    simp only [Option.some.injEq, Prod.mk.injEq] at split
    obtain ⟨_, rfl⟩ := split
    rw [← whole, GenGcPartial.dataMass_append, dataMass, dataLen]
  · obtain ⟨left, right, shape, leftLen⟩ := heapLookup_split heap allocation _ (unused.1 freeZero)
    have canonical : heapSplit allocation heap = some (left, .unused (free - 1) :: right) := by
      rw [shape, leftLen]
      exact heapSplit_append left _
    rw [canonical] at dataSplit
    simp only [Option.some.injEq, Prod.mk.injEq] at dataSplit
    obtain ⟨rfl, _⟩ := dataSplit
    have afterFree : heapSplit (allocation + free) heap = some (left ++ [.unused (free - 1)], right) := by
      have size : heapLength (left ++ [.unused (free - 1)]) = allocation + free := by
        rw [heapLength_append, dataLen]
        have singleton : heapLength ([.unused (free - 1)] : List (HeapElement α β)) = free := by
          simp [heapLength, elLength]
          omega
        rw [singleton]
      rw [← size, shape]
      have assoc : left ++ .unused (free - 1) :: right =
          (left ++ [.unused (free - 1)]) ++ right := by
        exact (List.append_assoc left [.unused (free - 1)] right).symm
      rw [assoc]
      exact heapSplit_append (left ++ [.unused (free - 1)]) right
    rw [afterFree] at split
    simp only [Option.some.injEq, Prod.mk.injEq] at split
    obtain ⟨_, rfl⟩ := split
    rw [shape, GenGcPartial.dataMass_append]
    have zero : GenGcPartial.dataMass (.unused (free - 1) :: right) = GenGcPartial.dataMass right := by
      simp [GenGcPartial.dataMass, isDataElement]
    rw [zero, dataMass, dataLen]

/-- The old-generation prefix contains only data when its boundary precedes
the source allocation boundary. -/
theorem partialSource_oldData {α β : Type} (heap : List (HeapElement α β))
    (old current refs : List (HeapElement α β)) (start finish allocation : Nat)
    (segment : heapSegment (start, finish) heap = some (old, current, refs))
    (beforeAllocation : dataUpTo allocation heap) (ordered : start ≤ allocation) :
    ∀ element ∈ old, isDataElement element := by
  obtain ⟨whole, oldLen, _, _⟩ := heapSegment_imp heap start finish old current refs segment
  obtain ⟨before, after, split, allData⟩ := beforeAllocation
  obtain ⟨beforeLen, _, beforeWhole⟩ := heapSplit_heapLength heap before after allocation split
  have oldPrefix : old <+: heap := ⟨current ++ refs, by simpa [List.append_assoc] using whole⟩
  have beforePrefix : before <+: heap := ⟨after, beforeWhole⟩
  have included : old <+: before := by
    rcases List.prefix_or_prefix_of_prefix oldPrefix beforePrefix with h | h
    · exact h
    · obtain ⟨tail, oldEq⟩ := h
      have zero : heapLength tail = 0 := by
        have lengths := congrArg heapLength oldEq
        rw [heapLength_append, oldLen, beforeLen] at lengths
        omega
      have tailEmpty : tail = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (by
        have le := length_le_heapLength tail
        omega))
      simp only [tailEmpty, List.append_nil] at oldEq
      subst old
      exact ⟨[], by simp⟩
  intro element member
  exact allData element (included.sublist.subset member)

/-- A successful partial collection preserves the original old-generation
prefix as the first component of the input heap segment. -/
theorem partialSource_resultSegment {α β : Type} (conf : GenGcPartial.Config β)
    (roots roots1 : List (HeapAddress α)) (heap : List (HeapElement α β)) (state : GcState α β)
    (run : GenGcPartial.partialGc conf (roots, heap) = (roots1, state)) (ok : state.ok = true) :
    ∃ current refs, heapSegment (conf.genStart, conf.refsStart) heap = some (state.old, current, refs) := by
  obtain ⟨old, current, refs, middle, refs1, afterRefs, segment, rootRun, _, refRun, _, dataRun⟩ :=
    partialFull_abstractSteps conf roots roots1 heap state run ok
  let initial : GcState α β :=
    { emptyGcState with heap := heap, old := old, r2 := refs, a := conf.genStart, n := heapLength current }
  have rootOld := (partialMoveList_fixedFields conf roots roots1 initial middle rootRun).2.2.2.2.2
  have refsOld := (partialFull_refListFixed conf refs refs1 middle afterRefs refRun).2.2.2.2.2
  have dataOld := (partialFull_dataFixed conf { afterRefs with r1 := refs1, r2 := [] }).2.2.2.2.1
  rw [dataRun] at dataOld
  have oldEq : state.old = old := by simpa [initial] using dataOld.trans (refsOld.trans rootOld)
  exact ⟨current, refs, by simpa [oldEq] using segment⟩

/-- A successful partial collection retains the original reference suffix up
to the source's similarity relation. -/
theorem partialSource_resultRefsSimilar {α β : Type} (conf : GenGcPartial.Config β)
    (roots roots1 : List (HeapAddress α)) (heap : List (HeapElement α β)) (state : GcState α β)
    (run : GenGcPartial.partialGc conf (roots, heap) = (roots1, state)) (ok : state.ok = true) :
    ∃ current refs,
      heapSegment (conf.genStart, conf.refsStart) heap = some (state.old, current, refs) ∧
      List.Forall₂ (GenGcPartial.similarData conf) refs state.r1 := by
  obtain ⟨old, current, refs, middle, refs1, afterRefs, segment, rootRun, _, refRun, _, dataRun⟩ :=
    partialFull_abstractSteps conf roots roots1 heap state run ok
  let initial : GcState α β :=
    { emptyGcState with heap := heap, old := old, r2 := refs, a := conf.genStart, n := heapLength current }
  have rootOld := (partialMoveList_fixedFields conf roots roots1 initial middle rootRun).2.2.2.2.2
  have refsOld := (partialFull_refListFixed conf refs refs1 middle afterRefs refRun).2.2.2.2.2
  have fixed := partialFull_dataFixed conf { afterRefs with r1 := refs1, r2 := [] }
  rw [dataRun] at fixed
  have oldEq : state.old = old := by simpa [initial] using fixed.2.2.2.2.1.trans (refsOld.trans rootOld)
  have refsEq : state.r1 = refs1 := fixed.2.2.2.1
  refine ⟨current, refs, by simpa [oldEq] using segment, ?_⟩
  rw [refsEq]
  exact GenGcPartial.gcMoveRefList_similar conf refs refs1 middle afterRefs refRun

/-- The old region returned by a successful partial collection is composed
of source data elements. -/
theorem partialSource_resultOldData {width : Nat} [NeZero width] (conf : Config)
    (values : List DataSem.Value) (references : Spt (BvlSem.Ref DataSem.Value))
    (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (state : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (be : Bool) (a sp sp1 limit next : Nat) (gens : GenState) (limits : List Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (source : absMlInv conf values references (roots, heap, be, a, sp, sp1, gens) limit next)
    (kind : conf.gcKind = .generational limits) (selected : wordGenGcCanDoPartial limits store)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit)
    (run : GenGcPartial.partialGc (makePartialConf (makeGcConf limit) gens (a + sp + sp1)) (roots, heap) =
      (roots1, state)) (ok : state.ok = true) :
    ∀ element ∈ state.old, isDataElement element := by
  obtain ⟨_, _, startBound, _⟩ := partialSource_conditions conf values references roots heap be a sp sp1 limit next
    gens limits store memory domain source kind selected heapMem
  obtain ⟨current, refs, segment⟩ := partialSource_resultSegment _ roots roots1 heap state run ok
  exact partialSource_oldData heap state.old current refs _ (a + sp + sp1) a segment source.2.2.2.1.2.2 startBound

/-- Source unused-space accounting and the preserved outer heap segments
bound the copied old generation by the original allocation point. -/
theorem partialSource_allocationBound {α β : Type} (conf : GenGcPartial.Config β)
    (roots roots1 : List (HeapAddress α)) (heap : List (HeapElement α β)) (state : GcState α β)
    (a free : Nat) (finish : conf.refsStart = a + free)
    (unused : unusedSpaceInv a free heap)
    (run : GenGcPartial.partialGc conf (roots, heap) = (roots1, state)) (ok : state.ok = true)
    (ordered : conf.genStart ≤ conf.refsStart) (oldData : ∀ element ∈ state.old, isDataElement element) :
    heapLength (state.old ++ state.h1) ≤ a := by
  obtain ⟨current, current1, refs, inputSegment, outputSegment⟩ :=
    partialFull_collectSegment conf roots roots1 heap state run ok ordered
  obtain ⟨inputWhole, _, inputEnd, _⟩ := heapSegment_imp heap _ _ state.old current refs inputSegment
  obtain ⟨outputWhole, _, _, _⟩ := heapSegment_imp state.heap _ _ state.old current1 refs outputSegment
  have split : heapSplit (a + free) heap = some (state.old ++ current, refs) := by
    rw [← finish, ← inputEnd, ← inputWhole]
    exact heapSplit_append (state.old ++ current) refs
  have sourceMass := partialSource_dataMass heap (state.old ++ current) refs a free unused split
  have resultMass := partialFull_collectDataMass conf roots roots1 heap state run ok
  have oldMass := GenGcPartial.dataMass_of_allData state.old oldData
  rw [← outputWhole, GenGcPartial.dataMass_append, GenGcPartial.dataMass_append, oldMass] at resultMass
  rw [heapLength_append]
  omega

/-- Both generational collection branches preserve the number of roots. -/
theorem combinedGenerational_rootsLength {α β : Type} (conf : GenGc.Config β) (limits : List Nat)
    (roots roots1 : List (HeapAddress α)) (heap heap1 : List (HeapElement α β))
    (gens gens1 : GenState) (refsStart a1 n1 : Nat) (flag ok : Bool)
    (run : gcCombined conf (.generational limits) (roots, heap, gens, refsStart, flag) =
      (roots1, heap1, a1, n1, gens1, ok)) : roots1.length = roots.length := by
  classical
  cases flag with
  | false =>
    simp only [gcCombined, Bool.false_eq_true, ↓reduceIte] at run
    cases moved : GenGc.genGc conf (roots, heap) with
    | mk out state =>
      simp only [moved, Prod.mk.injEq] at run
      obtain ⟨rfl, _⟩ := run
      exact GenGc.genGc_length conf roots out heap state moved
  | true =>
    simp only [gcCombined, ↓reduceIte] at run
    cases moved : GenGcPartial.partialGc (makePartialConf conf gens refsStart) (roots, heap) with
    | mk out state =>
      simp only [moved, Prod.mk.injEq] at run
      obtain ⟨rfl, _⟩ := run
      exact GenGcPartial.partialGc_length _ roots out heap state moved

/-- The store invariant supplies the memory and machine-word premises for a
successful combined partial collection. -/
theorem combinedPartial_store_simulation {width : Nat} [NeZero width] (conf : Config)
    (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit a1 n1 : Nat) (gens gens1 : GenState) (limits : List Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (run : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits) (roots, heap, gens, a + sp + sp1, true) =
      (roots1, heap1, a1, n1, gens1, true))
    (kind : conf.gcKind = .generational limits) (selected : wordGenGcCanDoPartial limits store)
    (limitEq : limit = heapLength heap) (ending : endsWithRefs (a + sp + sp1) heap)
    (ordered : (makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).genStart ≤ a + sp + sp1)
    (refBound : a + sp + sp1 ≤ heapLength heap) (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ curr other : BitVec width, ∃ outMemory : BitVec width → WordLocW width,
      ∃ state : GcState (WordLocW width) (HeapTag × List (WordLocW width)),
      ∃ current1 refs1,
      store.lookup .currHeap = some (.word curr) ∧ store.lookup .otherHeap = some (.word other) ∧
      store.lookup .genStart = some (.word (wordSemBytesInWord * BitVec.ofNat width
        (makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).genStart)) ∧
      GenGcPartial.partialGc (makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)) (roots, heap) = (roots1, state) ∧
      heap1 = state.old ++ state.h1 ++ heapExpand state.n ++ state.r1 ∧ a1 = state.a ∧ n1 = state.n ∧
      gens1 = .genState 0 (limits.map fun _ => state.a) ∧
      wordGenGcPartialFull conf (roots.map (wordAddr conf), curr, other,
        wordSemBytesInWord * BitVec.ofNat width limit, memory, domain,
        wordSemBytesInWord * BitVec.ofNat width (makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).genStart,
        wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1)) =
        (roots1.map (wordAddr conf), BitVec.ofNat width a1,
         curr + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.old ++ state.h1)), outMemory, true) ∧
      SetSep.star (wordHeap curr heap1 conf) (wordHeap other (heapExpand limit) conf)
        (SetSep.fun2Set (outMemory, fun address => domain address = true)) ∧
      state.h2 = [] ∧ state.r4 = [] ∧ state.r3 = [] ∧ state.r2 = [] ∧
      heapLength state.heap = heapLength heap ∧
      heapSegment ((makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).genStart, a + sp + sp1) state.heap =
        some (state.old, current1, refs1) ∧ partialLenInv state ∧
      state.r1.all (isRefElement (makeGcConf (α := List (WordLocW width)) limit).isRef) = true := by
  classical
  rcases heapMem with ⟨heapBound, byteBound, shift, nonzero, lenBound, shiftBound, global,
    curr, other, currAligned, otherAligned, currLookup, otherLookup, next, trigger, endHeap, heapSize,
    globReal, generations, separated⟩
  obtain ⟨start, tail, count, gensEq, startEq, startLookup⟩ :=
    partialGenStart_store conf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1) limits store kind selected generations
  have storedStart : store.lookup .genStart = some (.word (wordSemBytesInWord * BitVec.ofNat width
      (makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).genStart)) := by simpa [startEq] using startLookup
  have byteBound1 : heapLength heap * (width / 8) < 2 ^ width :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) byteBound
  have dataBound : conf.lenSize + 2 < width := by omega
  have refClass : ∀ (t : HeapTag) (r : List (WordLocW width)), (makeGcConf (α := List (WordLocW width)) limit).isRef (t, r) = true ↔ isMutTag t := by
    intro t r
    simp [makeGcConf]
  have sepFrame : SetSep.star (SetSep.star (wordHeap curr heap conf)
      (Misc.wordListExists other (heapLength heap))) SetSep.emp
      (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    rw [wordHeap_heapExpand, limitEq] at separated
    simpa [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft] using separated
  generalize wordRun : wordGenGcPartialFull conf (roots.map (wordAddr conf), curr, other,
      wordSemBytesInWord * BitVec.ofNat width (heapLength heap), memory, domain,
      wordSemBytesInWord * BitVec.ofNat width (makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).genStart,
      wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1)) = result
  obtain ⟨wordRoots, wordI, wordPa, outMemory, wordOk⟩ := result
  obtain ⟨state, current1, refs1, abstractRun, heapEq, allocEq, freeEq, gensOut, output,
    h2Empty, r4Empty, r3Empty, r2Empty, rootsEq, heapLen, segment, okEq, indexEq, paEq, inv, refsOk⟩ :=
    combinedPartial_heap_correct conf (makeGcConf (α := List (WordLocW width)) limit) gens gens1 limits (a + sp + sp1) roots roots1 heap heap1 a1 n1
      memory outMemory domain curr other wordPa wordI SetSep.emp wordRoots wordOk run heapBound byteBound1 ending
      limitEq ordered refBound dataBound refClass wordRun sepFrame good
  refine ⟨curr, other, outMemory, state, current1, refs1, currLookup, otherLookup, storedStart, abstractRun,
    heapEq, allocEq, freeEq, gensOut, ?_, ?_, h2Empty, r4Empty, r3Empty, r2Empty, heapLen, segment, inv, refsOk⟩
  · simpa [limitEq, rootsEq, indexEq, paEq, okEq] using wordRun
  · simpa [limitEq, SetSep.starComm, StackRemove.StackHeap.starEmptyLeft] using output

/-- The input store invariant discharges the memory and dimensional
preconditions of the combined major collector's heap simulation. -/
theorem combinedMajor_store_simulation {width : Nat} [NeZero width] (conf : Config)
    (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit a1 n1 : Nat) (gens gens1 : GenState) (limits : List Nat) (refsStart : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (run : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits) (roots, heap, gens, refsStart, false) =
      (roots1, heap1, a1, n1, gens1, true))
    (limitEq : limit = heapLength heap) (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ curr other : BitVec width, ∃ outMemory : BitVec width → WordLocW width,
      ∃ state : GcState (WordLocW width) (HeapTag × List (WordLocW width)),
      store.lookup .currHeap = some (.word curr) ∧ store.lookup .otherHeap = some (.word other) ∧
      GenGc.genGc (makeGcConf (α := List (WordLocW width)) limit) (roots, heap) = (roots1, state) ∧
      heap1 = state.h1 ++ heapExpand state.n ++ state.r1 ∧ a1 = state.a ∧ n1 = state.n ∧
      gens1 = .genState 0 (limits.map fun _ => state.a) ∧
      wordGenGc conf (roots.map (wordAddr conf), curr, other,
        wordSemBytesInWord * BitVec.ofNat width limit, memory, domain) =
        (roots1.map (wordAddr conf), BitVec.ofNat width a1,
         other + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1),
         BitVec.ofNat width (a1 + n1),
         other + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1 + state.n), outMemory, true) ∧
      SetSep.star (wordHeap other heap1 conf) (wordHeap curr (heapExpand limit) conf)
        (SetSep.fun2Set (outMemory, fun address => domain address = true)) ∧
      state.h2 = [] ∧ state.r4 = [] ∧ state.r3 = [] ∧ state.r2 = [] ∧
      heapLength state.heap = heapLength heap ∧ genLenInv state ∧
      state.r1.all (isRefElement (makeGcConf (α := List (WordLocW width)) limit).isRef) = true := by
  classical
  rcases heapMem with ⟨heapBound, byteBound, shift, nonzero, lenBound, shiftBound, global,
    curr, other, currAligned, otherAligned, currLookup, otherLookup, next, trigger, endHeap, heapSize,
    globReal, generations, separated⟩
  have byteBound1 : heapLength heap * (width / 8) < 2 ^ width :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) byteBound
  have dataBound : conf.lenSize + 2 < width := by omega
  have lenBound1 : conf.lenSize + 5 ≤ width := by omega
  have refClass : ∀ (t : HeapTag) (r : List (WordLocW width)), (makeGcConf (α := List (WordLocW width)) limit).isRef (t, r) = true ↔ isMutTag t := by
    intro t r
    simp [makeGcConf]
  have sepFrame : SetSep.star (SetSep.star (wordHeap curr heap conf)
      (Misc.wordListExists other (heapLength heap))) SetSep.emp
      (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    rw [wordHeap_heapExpand, limitEq] at separated
    simpa [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft] using separated
  generalize wordRun : wordGenGc conf (roots.map (wordAddr conf), curr, other,
      wordSemBytesInWord * BitVec.ofNat width (heapLength heap), memory, domain) = result
  obtain ⟨wordRoots, wordI, wordPa, wordIb, wordPb, outMemory, wordOk⟩ := result
  obtain ⟨state, abstractRun, heapEq, allocEq, freeEq, gensEq, output, h2Empty, r4Empty, r3Empty, r2Empty,
    rootsEq, originalLen, okEq, indexEq, ibEq, paEq, pbEq, inv, refsOk⟩ :=
    combinedMajor_heap_correct conf (makeGcConf (α := List (WordLocW width)) limit) gens gens1 limits refsStart roots roots1 heap heap1 a1 n1
      memory outMemory domain curr other wordPb wordPa wordIb wordI SetSep.emp wordRoots wordOk run heapBound byteBound1
      dataBound refClass lenBound1 good wordRun sepFrame
  refine ⟨curr, other, outMemory, state, currLookup, otherLookup, abstractRun, heapEq, allocEq, freeEq, gensEq,
    ?_, ?_, h2Empty, r4Empty, r3Empty, r2Empty, originalLen, inv, refsOk⟩
  · simpa [limitEq, rootsEq, indexEq, ibEq, paEq, pbEq, okEq] using wordRun
  · simpa [limitEq, SetSep.starComm, StackRemove.StackHeap.starEmptyLeft] using output

/-- Execute the major generational branch of the concrete collector using
the combined collector's successful run and the input store invariant. -/
theorem combinedMajor_store_execution {width : Nat} [NeZero width] (conf : Config)
    (root root1 : HeapAddress (WordLocW width)) (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit a1 n1 : Nat) (gens gens1 : GenState) (limits : List Nat) (refsStart : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (run : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits) (root :: roots, heap, gens, refsStart, false) =
      (root1 :: roots1, heap1, a1, n1, gens1, true))
    (kind : conf.gcKind = .generational limits) (full : ¬ wordGenGcCanDoPartial limits store)
    (global : store.lookup .globals = some (wordAddr conf root))
    (limitEq : limit = heapLength heap) (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ curr other : BitVec width, ∃ outMemory : BitVec width → WordLocW width,
      ∃ state : GcState (WordLocW width) (HeapTag × List (WordLocW width)),
      let pa := other + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)
      let pb := other + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1 + state.n)
      let g := wordAddr conf root1
      let alloc := wordSemTheWord (holFapply store .allocSize)
      store.lookup .currHeap = some (.word curr) ∧ store.lookup .otherHeap = some (.word other) ∧
      GenGc.genGc (makeGcConf (α := List (WordLocW width)) limit) (root :: roots, heap) = (root1 :: roots1, state) ∧
      heap1 = state.h1 ++ heapExpand state.n ++ state.r1 ∧ a1 = state.a ∧ n1 = state.n ∧
      gens1 = .genState 0 (limits.map fun _ => state.a) ∧
      wordGcFun conf (roots.map (wordAddr conf), memory, domain, store) =
        some (roots1.map (wordAddr conf), outMemory,
          store.updateListEq [(.currHeap, .word other), (.otherHeap, .word curr),
            (.nextFree, .word pa), (.genStart, .word (pa - other)),
            (.triggerGC, .word (pa + newTrig (pb - pa) alloc limits)), (.endOfHeap, .word pb),
            (.globals, g), (.globReal, globReal conf other g),
            (.temp 0, .word 0), (.temp 1, .word 0), (.temp 2, .word 0), (.temp 3, .word 0),
            (.temp 4, .word 0), (.temp 5, .word 0), (.temp 6, .word 0)]) ∧
      SetSep.star (wordHeap other heap1 conf) (wordHeap curr (heapExpand limit) conf)
        (SetSep.fun2Set (outMemory, fun address => domain address = true)) ∧
      state.h2 = [] ∧ state.r4 = [] ∧ state.r3 = [] ∧ state.r2 = [] ∧
      heapLength state.heap = heapLength heap ∧ genLenInv state ∧
      state.r1.all (isRefElement (makeGcConf (α := List (WordLocW width)) limit).isRef) = true := by
  classical
  obtain ⟨curr, other, outMemory, state, currLookup, otherLookup, abstractRun, heapEq, allocEq, freeEq, gensEq,
    concrete, separated, h2Empty, r4Empty, r3Empty, r2Empty, heapLen, inv, refsOk⟩ :=
    combinedMajor_store_simulation conf (root :: roots) (root1 :: roots1) heap heap1 a sp sp1 limit a1 n1
      gens gens1 limits refsStart store memory domain run limitEq good heapMem
  refine ⟨curr, other, outMemory, state, currLookup, otherLookup, abstractRun, heapEq, allocEq, freeEq, gensEq,
    ?_, separated, h2Empty, r4Empty, r3Empty, r2Empty, heapLen, inv, refsOk⟩
  have globalValue : holFapply store .globals = wordAddr conf root := holFapply_of_lookup global
  have currValue : holFapply store .currHeap = .word curr := holFapply_of_lookup currLookup
  have otherValue : holFapply store .otherHeap = .word other := holFapply_of_lookup otherLookup
  have assum := heapInMemoryStore_gcAssum conf heap a sp sp1 limit gens store memory domain good heapMem
  have sizeValue : holFapply store .heapLength = .word (wordSemBytesInWord * BitVec.ofNat width limit) := by
    rcases heapMem with ⟨_, _, _, _, _, _, _, oldCurr, oldOther, _, _, oldCurrLookup, oldOtherLookup,
      _, _, _, heapSize, _⟩
    exact holFapply_of_lookup heapSize
  simp only [List.map_cons] at concrete
  simp [wordGcFun, kind, full, globalValue, currValue, otherValue, sizeValue, wordSemTheWord, concrete, holHd, assum]

/-- Execute the concrete partial branch, deriving the allocation bound from
the source invariant and the collector's preserved heap segments. -/
theorem combinedPartial_store_execution {width : Nat} [NeZero width] (conf : Config)
    (root root1 : HeapAddress (WordLocW width)) (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (values : List DataSem.Value) (references : Spt (BvlSem.Ref DataSem.Value)) (be : Bool) (next : Nat)
    (a sp sp1 limit a1 n1 : Nat) (gens gens1 : GenState) (limits : List Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (run : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits)
      (root :: roots, heap, gens, a + sp + sp1, true) = (root1 :: roots1, heap1, a1, n1, gens1, true))
    (kind : conf.gcKind = .generational limits) (selected : wordGenGcCanDoPartial limits store)
    (global : store.lookup .globals = some (wordAddr conf root))
    (source : absMlInv conf values references (root :: roots, heap, be, a, sp, sp1, gens) limit next)
    (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ curr other : BitVec width, ∃ outMemory : BitVec width → WordLocW width,
      ∃ state : GcState (WordLocW width) (HeapTag × List (WordLocW width)),
      let pa := curr + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.old ++ state.h1))
      let endh := curr + wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1)
      let alloc := wordSemTheWord (holFapply store .allocSize)
      let g := wordAddr conf root1
      store.lookup .currHeap = some (.word curr) ∧ store.lookup .otherHeap = some (.word other) ∧
      GenGcPartial.partialGc (makePartialConf (makeGcConf limit) gens (a + sp + sp1)) (root :: roots, heap) =
        (root1 :: roots1, state) ∧
      heap1 = state.old ++ state.h1 ++ heapExpand state.n ++ state.r1 ∧ a1 = state.a ∧ n1 = state.n ∧
      gens1 = .genState 0 (limits.map fun _ => state.a) ∧
      wordGcFun conf (roots.map (wordAddr conf), memory, domain, store) =
        some (roots1.map (wordAddr conf), outMemory,
          store.updateListEq [(.currHeap, .word curr), (.otherHeap, .word other),
            (.nextFree, .word pa), (.genStart, .word (pa - curr)),
            (.triggerGC, .word (pa + newTrig (endh - pa) alloc limits)),
            (.globals, g), (.globReal, globReal conf curr g), (.temp 0, .word 0), (.temp 1, .word 0)]) ∧
      SetSep.star (wordHeap curr heap1 conf) (wordHeap other (heapExpand limit) conf)
        (SetSep.fun2Set (outMemory, fun address => domain address = true)) ∧
      state.h2 = [] ∧ state.r4 = [] ∧ state.r3 = [] ∧ state.r2 = [] ∧
      heapLength state.heap = heapLength heap ∧
      (∃ current1 refs1, heapSegment
        ((makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).genStart,
          a + sp + sp1) state.heap = some (state.old, current1, refs1)) ∧ partialLenInv state := by
  classical
  obtain ⟨limitEq, ending, startBound, refBound⟩ := partialSource_conditions conf values references (root :: roots) heap
    be a sp sp1 limit next gens limits store memory domain source kind selected heapMem
  have ordered : (makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).genStart ≤ a + sp + sp1 := by omega
  obtain ⟨curr, other, outMemory, state, current1, refs1, currLookup, otherLookup, startLookup,
    abstractRun, heapEq, allocEq, freeEq, gensEq, concrete, separated, h2Empty, r4Empty, r3Empty, r2Empty,
    heapLen, segment, inv, refsOk⟩ :=
    combinedPartial_store_simulation conf (root :: roots) (root1 :: roots1) heap heap1 a sp sp1 limit a1 n1
      gens gens1 limits store memory domain run kind selected limitEq ending ordered refBound good heapMem
  have stateOk : state.ok = true := by
    have combinedRun := run
    simp only [gcCombined, ↓reduceIte, abstractRun, Prod.mk.injEq] at combinedRun
    exact combinedRun.2.2.2.2.2
  have oldData := partialSource_resultOldData conf values references (root :: roots) (root1 :: roots1) heap state
    be a sp sp1 limit next gens limits store memory domain source kind selected heapMem abstractRun stateOk
  have finish : (makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).refsStart =
      a + (sp + sp1) := by cases gens; simp [makePartialConf, Nat.add_assoc]
  have allocationBound := partialSource_allocationBound _ (root :: roots) (root1 :: roots1) heap state a (sp + sp1)
    finish source.2.2.2.1 abstractRun stateOk ordered oldData
  refine ⟨curr, other, outMemory, state, currLookup, otherLookup, abstractRun, heapEq, allocEq, freeEq, gensEq,
    ?_, separated, h2Empty, r4Empty, r3Empty, r2Empty, heapLen, ⟨current1, refs1, segment⟩, inv⟩
  have globalValue : holFapply store .globals = wordAddr conf root := holFapply_of_lookup global
  have currValue : holFapply store .currHeap = .word curr := holFapply_of_lookup currLookup
  have otherValue : holFapply store .otherHeap = .word other := holFapply_of_lookup otherLookup
  have startValue := holFapply_of_lookup startLookup
  have assum := heapInMemoryStore_gcAssum conf heap a sp sp1 limit gens store memory domain good heapMem
  have sizeValue : holFapply store .heapLength = .word (wordSemBytesInWord * BitVec.ofNat width limit) := by
    rcases heapMem with ⟨_, _, _, _, _, _, _, oldCurr, oldOther, _, _, oldCurrLookup, oldOtherLookup,
      _, _, _, heapSize, _⟩
    exact holFapply_of_lookup heapSize
  have endValue : holFapply store .endOfHeap = .word (curr + wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1)) := by
    rcases heapMem with ⟨_, _, _, _, _, _, _, oldCurr, oldOther, _, _, oldCurrLookup, _, _, _, oldEnd, _⟩
    have same : oldCurr = curr := by simpa [oldCurrLookup] using currLookup
    subst oldCurr
    exact holFapply_of_lookup oldEnd
  have enoughSpace := partialAllocation_fits conf heap a sp sp1 limit (heapLength (state.old ++ state.h1))
    gens limits store memory domain curr selected (by omega) refBound good heapMem currLookup
  have enough' :
      let endh := curr + wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1)
      let pa := curr + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.old ++ state.h1))
      let alloc := wordSemTheWord (holFapply store .allocSize)
      alloc ≤ endh - pa ∧ alloc ≤ newTrig (endh - pa) alloc limits :=
    ⟨enoughSpace, newTrig_alloc_le _ _ limits enoughSpace⟩
  have endOffset : (curr + wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1)) - curr =
      wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1) := by
    simp only [BitVec.add_comm curr, BitVec.add_sub_cancel]
  have cancelCommon (x y z : BitVec width) : (x + y) - (x + z) = y - z := by
    apply BitVec.sub_eq_iff_eq_add.mpr
    calc
      x + y = x + ((y - z) + z) := by rw [BitVec.sub_add_cancel]
      _ = (y - z) + (x + z) := by ac_rfl
  have enoughNorm :
      wordSemTheWord (holFapply store .allocSize) ≤
        wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1) -
          wordSemBytesInWord * BitVec.ofNat width (heapLength (state.old ++ state.h1)) ∧
      wordSemTheWord (holFapply store .allocSize) ≤ newTrig
        (wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1) -
          wordSemBytesInWord * BitVec.ofNat width (heapLength (state.old ++ state.h1)))
        (wordSemTheWord (holFapply store .allocSize)) limits := by
    simpa only [cancelCommon] using enough'
  simp only [List.map_cons] at concrete
  simp [wordGcFun, kind, selected, globalValue, currValue, otherValue, startValue, sizeValue, endValue,
    wordSemTheWord, endOffset, concrete, holHd, assum]
  simpa only [wordSemTheWord] using enoughNorm

/-- A successful partial collection preserves the word shape of its global
root. -/
theorem combinedPartial_global_word {width : Nat} [NeZero width] (conf : Config)
    (values : List DataSem.Value) (references : Spt (BvlSem.Ref DataSem.Value))
    (root root1 : HeapAddress (WordLocW width)) (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (be : Bool) (a sp sp1 limit next a1 n1 : Nat) (gens gens1 : GenState) (limits : List Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (run : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits)
      (root :: roots, heap, gens, a + sp + sp1, true) = (root1 :: roots1, heap1, a1, n1, gens1, true))
    (kind : conf.gcKind = .generational limits) (selected : wordGenGcCanDoPartial limits store)
    (global : store.lookup .globals = some (wordAddr conf root))
    (source : absMlInv conf values references (root :: roots, heap, be, a, sp, sp1, gens) limit next)
    (good : goodDimindex width) (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ g, wordAddr conf root1 = .word g := by
  have assum := heapInMemoryStore_gcAssum conf heap a sp sp1 limit gens store memory domain good heapMem
  have inputWord : wordSemIsWordLoc (wordAddr conf root) = true := by
    simpa [holFapply_of_lookup global] using assum.2.2.2.2.2.2.2.1
  obtain ⟨limitEq, ending, startBound, refBound⟩ :=
    partialSource_conditions conf values references (root :: roots) heap be a sp sp1 limit next
      gens limits store memory domain source kind selected heapMem
  have ordered : (makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).genStart ≤
      a + sp + sp1 := by omega
  obtain ⟨curr, other, outMemory, state, current1, refs1, _, _, _, _, _, _, _, _, concrete, _⟩ :=
    combinedPartial_store_simulation conf (root :: roots) (root1 :: roots1) heap heap1 a sp sp1 limit a1 n1
      gens gens1 limits store memory domain run kind selected limitEq ending ordered refBound good heapMem
  let gs := wordSemBytesInWord * BitVec.ofNat width
    (makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).genStart
  let rs := wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1)
  have rel := wordGenGcPartialMoveRoots_rootRel conf ((root :: roots).map (wordAddr conf))
    (gs >>> wordShiftAmount width) other curr memory domain gs rs
  rw [← wordGenGcPartialFull_fst, concrete] at rel
  simp only [List.map_cons] at rel
  cases rel with
  | cons head tail =>
    have outputWord : wordSemIsWordLoc (wordAddr conf root1) = true := by simpa [inputWord] using head.1.symm
    cases value : wordAddr conf root1 with
    | word w => exact ⟨w, rfl⟩
    | loc l o => simp [value, wordSemIsWordLoc] at outputWord

/-- A successful major collection preserves the word shape of its global
root. -/
theorem combinedMajor_global_word {width : Nat} [NeZero width] (conf : Config)
    (root root1 : HeapAddress (WordLocW width)) (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit a1 n1 : Nat) (gens gens1 : GenState) (limits : List Nat) (refsStart : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (run : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits)
      (root :: roots, heap, gens, refsStart, false) = (root1 :: roots1, heap1, a1, n1, gens1, true))
    (global : store.lookup .globals = some (wordAddr conf root)) (limitEq : limit = heapLength heap)
    (good : goodDimindex width) (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ g, wordAddr conf root1 = .word g := by
  have assum := heapInMemoryStore_gcAssum conf heap a sp sp1 limit gens store memory domain good heapMem
  have inputWord : wordSemIsWordLoc (wordAddr conf root) = true := by
    simpa [holFapply_of_lookup global] using assum.2.2.2.2.2.2.2.1
  obtain ⟨curr, other, outMemory, state, _, _, _, _, _, _, _, concrete, _⟩ :=
    combinedMajor_store_simulation conf (root :: roots) (root1 :: roots1) heap heap1 a sp sp1 limit a1 n1
      gens gens1 limits refsStart store memory domain run limitEq good heapMem
  have rel := wordGenGcMoveRoots_rootRel conf ((root :: roots).map (wordAddr conf)) 0 other
    ((wordSemBytesInWord * BitVec.ofNat width limit) >>> wordShiftAmount width)
    (other + wordSemBytesInWord * BitVec.ofNat width limit) curr memory domain
  rw [← wordGenGc_fst, concrete] at rel
  simp only [List.map_cons] at rel
  cases rel with
  | cons head tail =>
    have outputWord : wordSemIsWordLoc (wordAddr conf root1) = true := by simpa [inputWord] using head.1.symm
    cases value : wordAddr conf root1 with
    | word w => exact ⟨w, rfl⟩
    | loc l o => simp [value, wordSemIsWordLoc] at outputWord

/-- Rebuild the major collector's heap/store invariant after swapping spaces
and choosing a whole-word trigger within the available free region. -/
theorem combinedMajor_store_reconstruct {width : Nat} [NeZero width] (conf : Config)
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit copied free triggerWords : Nat) (gens : GenState) (limits : List Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory outMemory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (curr other g : BitVec width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit)
    (kind : conf.gcKind = .generational limits) (lengthEq : heapLength heap1 = heapLength heap)
    (triggerBound : triggerWords ≤ free)
    (triggerEq : newTrig (wordSemBytesInWord * BitVec.ofNat width free)
      (wordSemTheWord (holFapply store .allocSize)) limits = wordSemBytesInWord * BitVec.ofNat width triggerWords)
    (currLookup : store.lookup .currHeap = some (.word curr))
    (otherLookup : store.lookup .otherHeap = some (.word other))
    (separated : SetSep.star (wordHeap other heap1 conf) (wordHeap curr (heapExpand limit) conf)
      (SetSep.fun2Set (outMemory, fun address => domain address = true))) :
    heapInMemoryStore heap1 copied triggerWords (free - triggerWords) (.genState 0 (limits.map fun _ => copied)) conf
      (store.updateListEq [(.currHeap, .word other), (.otherHeap, .word curr),
        (.nextFree, .word (other + wordSemBytesInWord * BitVec.ofNat width copied)),
        (.genStart, .word ((other + wordSemBytesInWord * BitVec.ofNat width copied) - other)),
        (.triggerGC, .word ((other + wordSemBytesInWord * BitVec.ofNat width copied) +
          newTrig ((other + wordSemBytesInWord * BitVec.ofNat width (copied + free)) -
            (other + wordSemBytesInWord * BitVec.ofNat width copied))
            (wordSemTheWord (holFapply store .allocSize)) limits)),
        (.endOfHeap, .word (other + wordSemBytesInWord * BitVec.ofNat width (copied + free))),
        (.globals, .word g), (.globReal, globReal conf other (.word g)),
        (.temp 0, .word 0), (.temp 1, .word 0), (.temp 2, .word 0), (.temp 3, .word 0),
        (.temp 4, .word 0), (.temp 5, .word 0), (.temp 6, .word 0)]) outMemory domain limit := by
  classical
  rcases heapMem with ⟨heapBound, byteBound, shift, nonzero, lenBound, shiftBound, global,
    oldCurr, oldOther, currAligned, otherAligned, oldCurrLookup, oldOtherLookup, next, trigger, endHeap, heapSize,
    globRealOld, generations, oldSeparated⟩
  have currEq : oldCurr = curr := by simpa [oldCurrLookup] using currLookup
  have otherEq : oldOther = other := by simpa [oldOtherLookup] using otherLookup
  subst oldCurr
  subst oldOther
  have offset : (other + wordSemBytesInWord * BitVec.ofNat width (copied + free)) -
      (other + wordSemBytesInWord * BitVec.ofNat width copied) = wordSemBytesInWord * BitVec.ofNat width free := by
    rw [BitVec.ofNat_add, BitVec.mul_add, ← BitVec.add_assoc]
    simp
  have sum : copied + triggerWords + (free - triggerWords) = copied + free := by omega
  have genValid : genStartsInStore conf (.genState 0 (limits.map fun _ => copied))
      (some (.word (StackRemove.bytesInWord width * BitVec.ofNat width copied))) := by
    simp only [genStartsInStore]
    intro sizes eq
    have sizesEq : sizes = limits := by simpa [kind] using eq.symm
    subst sizes
    simp only [List.length_map, true_and]
    intro x xs first
    cases limits with
    | nil => simp at first
    | cons size rest =>
      simp only [List.map_cons, List.cons.injEq] at first
      obtain ⟨rfl, _⟩ := first
      rfl
  rw [offset, triggerEq]
  rw [heapInMemoryStore, lengthEq]
  refine ⟨heapBound, byteBound, shift, nonzero, lenBound, shiftBound, ?_, other, curr,
    otherAligned, currAligned, ?_⟩
  · simp [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL,
      wordSemBytesInWord, StackRemove.bytesInWord, sum, BitVec.ofNat_add, BitVec.mul_add,
      BitVec.add_assoc, heapSize, globRealInv, globReal, genStartsInStore, kind, separated]
    simpa [genStartsInStore, kind, StackRemove.bytesInWord] using genValid

/-- Rebuild the partial collector's heap/store invariant in the existing
heap space, splitting the remaining free space at the new trigger. -/
theorem combinedPartial_store_reconstruct {width : Nat} [NeZero width] (conf : Config)
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit copied free triggerWords : Nat) (gens : GenState) (limits : List Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory outMemory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (curr other g : BitVec width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit)
    (kind : conf.gcKind = .generational limits) (lengthEq : heapLength heap1 = heapLength heap)
    (endEq : copied + free = a + sp + sp1) (triggerBound : triggerWords ≤ free)
    (triggerEq : newTrig (wordSemBytesInWord * BitVec.ofNat width free)
      (wordSemTheWord (holFapply store .allocSize)) limits = wordSemBytesInWord * BitVec.ofNat width triggerWords)
    (currLookup : store.lookup .currHeap = some (.word curr))
    (otherLookup : store.lookup .otherHeap = some (.word other))
    (separated : SetSep.star (wordHeap curr heap1 conf) (wordHeap other (heapExpand limit) conf)
      (SetSep.fun2Set (outMemory, fun address => domain address = true))) :
    heapInMemoryStore heap1 copied triggerWords (free - triggerWords) (.genState 0 (limits.map fun _ => copied)) conf
      (store.updateListEq [(.currHeap, .word curr), (.otherHeap, .word other),
        (.nextFree, .word (curr + wordSemBytesInWord * BitVec.ofNat width copied)),
        (.genStart, .word ((curr + wordSemBytesInWord * BitVec.ofNat width copied) - curr)),
        (.triggerGC, .word ((curr + wordSemBytesInWord * BitVec.ofNat width copied) +
          newTrig ((curr + wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1)) -
            (curr + wordSemBytesInWord * BitVec.ofNat width copied))
            (wordSemTheWord (holFapply store .allocSize)) limits)),
        (.globals, .word g), (.globReal, globReal conf curr (.word g)),
        (.temp 0, .word 0), (.temp 1, .word 0)]) outMemory domain limit := by
  classical
  rcases heapMem with ⟨heapBound, byteBound, shift, nonzero, lenBound, shiftBound, global,
    oldCurr, oldOther, currAligned, otherAligned, oldCurrLookup, oldOtherLookup, next, trigger, endHeap, heapSize,
    globRealOld, generations, oldSeparated⟩
  have currEq : oldCurr = curr := by simpa [oldCurrLookup] using currLookup
  have otherEq : oldOther = other := by simpa [oldOtherLookup] using otherLookup
  subst oldCurr
  subst oldOther
  have offset : (curr + wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1)) -
      (curr + wordSemBytesInWord * BitVec.ofNat width copied) = wordSemBytesInWord * BitVec.ofNat width free := by
    rw [← endEq, BitVec.ofNat_add, BitVec.mul_add, ← BitVec.add_assoc]
    simp
  have sum : copied + triggerWords + (free - triggerWords) = a + sp + sp1 := by omega
  have genValid : genStartsInStore conf (.genState 0 (limits.map fun _ => copied))
      (some (.word (StackRemove.bytesInWord width * BitVec.ofNat width copied))) := by
    simp only [genStartsInStore]
    intro sizes eq
    have sizesEq : sizes = limits := by simpa [kind] using eq.symm
    subst sizes
    simp only [List.length_map, true_and]
    intro x xs first
    cases limits with
    | nil => simp at first
    | cons size rest =>
      simp only [List.map_cons, List.cons.injEq] at first
      obtain ⟨rfl, _⟩ := first
      rfl
  rw [offset, triggerEq]
  rw [heapInMemoryStore, lengthEq]
  refine ⟨heapBound, byteBound, shift, nonzero, lenBound, shiftBound, ?_, curr, other,
    currAligned, otherAligned, ?_⟩
  · simp [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL,
      wordSemBytesInWord, StackRemove.bytesInWord, sum, BitVec.ofNat_add, BitVec.mul_add,
      BitVec.add_assoc, heapSize, endHeap, globRealInv, globReal, genStartsInStore, kind, separated]
    simpa [genStartsInStore, kind, StackRemove.bytesInWord] using genValid

/-- A successful partial collection executes the concrete collector and
reconstructs the complete heap/store invariant. -/
theorem combinedPartial_store_correct {width : Nat} [NeZero width] (conf : Config)
    (values : List DataSem.Value) (references : Spt (BvlSem.Ref DataSem.Value))
    (root root1 : HeapAddress (WordLocW width)) (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (be : Bool) (a sp sp1 limit next a1 n1 : Nat) (gens gens1 : GenState) (limits : List Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (run : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits)
      (root :: roots, heap, gens, a + sp + sp1, true) = (root1 :: roots1, heap1, a1, n1, gens1, true))
    (kind : conf.gcKind = .generational limits) (selected : wordGenGcCanDoPartial limits store)
    (global : store.lookup .globals = some (wordAddr conf root))
    (source : absMlInv conf values references (root :: roots, heap, be, a, sp, sp1, gens) limit next)
    (good : goodDimindex width) (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ outMemory outStore k,
      wordGcFun conf (roots.map (wordAddr conf), memory, domain, store) =
        some (roots1.map (wordAddr conf), outMemory, outStore) ∧
      heapInMemoryStore heap1 a1 k (n1 - k) gens1 conf outStore outMemory domain limit ∧
      k ≤ n1 ∧ outStore.lookup .globals = some (wordAddr conf root1) ∧
      ∃ p t, outStore.lookup .nextFree = some (.word p) ∧ outStore.lookup .triggerGC = some (.word t) ∧
        wordSemTheWord (holFapply store .allocSize) ≤ t - p := by
  classical
  obtain ⟨g, globalEq⟩ := combinedPartial_global_word conf values references root root1 roots roots1 heap heap1
    be a sp sp1 limit next a1 n1 gens gens1 limits store memory domain run kind selected global source good heapMem
  obtain ⟨curr, other, outMemory, state, currLookup, otherLookup, abstractRun, heapEq, allocEq, freeEq, gensEq,
    execution, separated, h2Empty, r4Empty, r3Empty, r2Empty, heapLen, ⟨current1, refs1, segment⟩, inv⟩ :=
    combinedPartial_store_execution conf root root1 roots roots1 heap heap1 values references be next a sp sp1 limit
      a1 n1 gens gens1 limits store memory domain run kind selected global source good heapMem
  have stateOk : state.ok = true := by
    have combinedRun := run
    simp only [gcCombined, ↓reduceIte, abstractRun, Prod.mk.injEq] at combinedRun
    exact combinedRun.2.2.2.2.2
  have index := partialFull_dataIndex _ (root :: roots) (root1 :: roots1) heap state abstractRun stateOk h2Empty
  have expandLen : heapLength (heapExpand state.n : List (HeapElement (WordLocW width)
      (HeapTag × List (WordLocW width)))) = state.n := by cases state.n <;> simp [heapExpand, heapLength, elLength]
  have outputLength : heapLength heap1 = heapLength heap := by
    rw [heapEq]
    simp only [heapLength_append, expandLen]
    simp [partialLenInv, h2Empty, r4Empty, r3Empty, r2Empty, heapLength] at inv
    simp [heapLength] at heapLen ⊢
    omega
  obtain ⟨current, refs, inputSegment, similar⟩ := partialSource_resultRefsSimilar _
    (root :: roots) (root1 :: roots1) heap state abstractRun stateOk
  have refLengths := (GenGcPartial.similarData_lengths _ refs state.r1 similar).1
  obtain ⟨_, _, _, inputRefsLen⟩ := heapSegment_imp heap _ _ state.old current refs inputSegment
  obtain ⟨_, _, _, outputRefsLen⟩ := heapSegment_imp state.heap _ _ state.old current1 refs1 segment
  have refsStartEq : (makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).refsStart =
      a + sp + sp1 := by cases gens; rfl
  rw [refsStartEq] at inputRefsLen
  have refsEqual : heapLength state.r1 = heapLength refs1 := by omega
  obtain ⟨_, endCount⟩ := partialFull_outputBounds state state.old current1 refs1 _ (a + sp + sp1)
    segment h2Empty r4Empty r3Empty r2Empty rfl refsEqual inv
  have endEq : heapLength (state.old ++ state.h1) + state.n = a + sp + sp1 := by
    have oldLen := (heapSegment_imp state.heap _ _ state.old current1 refs1 segment).2.1
    simp only [heapLength_append]
    omega
  obtain ⟨_, _, _, refBound⟩ := partialSource_conditions conf values references (root :: roots) heap
    be a sp sp1 limit next gens limits store memory domain source kind selected heapMem
  have oldData := partialSource_resultOldData conf values references (root :: roots) (root1 :: roots1) heap state
    be a sp sp1 limit next gens limits store memory domain source kind selected heapMem abstractRun stateOk
  have ordered : (makePartialConf (makeGcConf (α := List (WordLocW width)) limit) gens (a + sp + sp1)).genStart ≤
      a + sp + sp1 := by
    obtain ⟨_, _, startBound, _⟩ := partialSource_conditions conf values references (root :: roots) heap
      be a sp sp1 limit next gens limits store memory domain source kind selected heapMem
    omega
  have allocationBound := partialSource_allocationBound _ (root :: roots) (root1 :: roots1) heap state a (sp + sp1)
    (by simpa [Nat.add_assoc] using refsStartEq) source.2.2.2.1 abstractRun stateOk ordered oldData
  have fits := partialAllocation_fits conf heap a sp sp1 limit (heapLength (state.old ++ state.h1))
    gens limits store memory domain curr selected (by omega) refBound good heapMem currLookup
  have triggerFits := newTrig_alloc_le _ _ limits fits
  obtain ⟨k, triggerEq, kBound⟩ := newTrig_wordCount state.n
    (wordSemTheWord (holFapply store .allocSize)) limits good
  have invariant := combinedPartial_store_reconstruct conf heap heap1 a sp sp1 limit
    (heapLength (state.old ++ state.h1)) state.n k gens limits store memory outMemory domain curr other g
    heapMem kind outputLength endEq kBound triggerEq currLookup otherLookup separated
  let outStore := store.updateListEq [(.currHeap, .word curr), (.otherHeap, .word other),
    (.nextFree, .word (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.old ++ state.h1)))),
    (.genStart, .word ((curr + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.old ++ state.h1))) - curr)),
    (.triggerGC, .word ((curr + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.old ++ state.h1))) +
      newTrig ((curr + wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1)) -
        (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.old ++ state.h1))))
        (wordSemTheWord (holFapply store .allocSize)) limits)),
    (.globals, .word g), (.globReal, globReal conf curr (.word g)), (.temp 0, .word 0), (.temp 1, .word 0)]
  refine ⟨outMemory, outStore, k, ?_, ?_, by simpa [freeEq] using kBound, ?_, ?_⟩
  · simpa [outStore, globalEq] using execution
  · simpa [outStore, allocEq, freeEq, gensEq, index] using invariant
  · simp [outStore, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL, globalEq]
  · let pa := curr + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.old ++ state.h1))
    let endh := curr + wordSemBytesInWord * BitVec.ofNat width (a + sp + sp1)
    let trigger := newTrig (endh - pa) (wordSemTheWord (holFapply store .allocSize)) limits
    refine ⟨pa, pa + trigger, ?_, ?_, ?_⟩
    · simp [outStore, pa, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL]
    · simp [outStore, pa, endh, trigger, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL]
    · simpa [pa, endh, trigger] using triggerFits

/-- A successful major collection executes the concrete collector and
reconstructs the complete heap/store invariant. -/
theorem combinedMajor_store_correct {width : Nat} [NeZero width] (conf : Config)
    (root root1 : HeapAddress (WordLocW width)) (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 limit a1 n1 : Nat) (gens gens1 : GenState) (limits : List Nat) (refsStart : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (run : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits)
      (root :: roots, heap, gens, refsStart, false) = (root1 :: roots1, heap1, a1, n1, gens1, true))
    (kind : conf.gcKind = .generational limits) (full : ¬ wordGenGcCanDoPartial limits store)
    (global : store.lookup .globals = some (wordAddr conf root)) (limitEq : limit = heapLength heap)
    (good : goodDimindex width) (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ outMemory outStore k,
      wordGcFun conf (roots.map (wordAddr conf), memory, domain, store) =
        some (roots1.map (wordAddr conf), outMemory, outStore) ∧
      heapInMemoryStore heap1 a1 k (n1 - k) gens1 conf outStore outMemory domain limit ∧
      k ≤ n1 ∧ outStore.lookup .globals = some (wordAddr conf root1) := by
  classical
  obtain ⟨g, globalEq⟩ := combinedMajor_global_word conf root root1 roots roots1 heap heap1 a sp sp1 limit a1 n1
    gens gens1 limits refsStart store memory domain run global limitEq good heapMem
  obtain ⟨curr, other, outMemory, state, currLookup, otherLookup, abstractRun, heapEq, allocEq, freeEq, gensEq,
    execution, separated, h2Empty, r4Empty, r3Empty, r2Empty, heapLen, inv, refsOk⟩ :=
    combinedMajor_store_execution conf root root1 roots roots1 heap heap1 a sp sp1 limit a1 n1 gens gens1 limits
      refsStart store memory domain run kind full global limitEq good heapMem
  have stateOk : state.ok = true := by
    have combinedRun := run
    simp only [gcCombined, Bool.false_eq_true, ↓reduceIte, abstractRun, Prod.mk.injEq] at combinedRun
    exact combinedRun.2.2.2.2.2
  have index := genFull_dataIndex (makeGcConf (α := List (WordLocW width)) limit)
    (root :: roots) (root1 :: roots1) heap state abstractRun stateOk h2Empty
  have expandLen : heapLength (heapExpand state.n : List (HeapElement (WordLocW width)
      (HeapTag × List (WordLocW width)))) = state.n := by cases state.n <;> simp [heapExpand, heapLength, elLength]
  have outputLength : heapLength heap1 = heapLength heap := by
    rw [heapEq]
    simp only [heapLength_append, expandLen]
    simp [genLenInv, h2Empty, r4Empty, r3Empty, r2Empty, heapLength] at inv
    simp [heapLength] at heapLen ⊢
    omega
  obtain ⟨k, triggerEq, kBound⟩ := newTrig_wordCount state.n
    (wordSemTheWord (holFapply store .allocSize)) limits good
  have invariant := combinedMajor_store_reconstruct conf heap heap1 a sp sp1 limit (heapLength state.h1) state.n k
    gens limits store memory outMemory domain curr other g heapMem kind outputLength kBound triggerEq currLookup otherLookup separated
  let outStore := store.updateListEq [(.currHeap, .word other), (.otherHeap, .word curr),
    (.nextFree, .word (other + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1))),
    (.genStart, .word ((other + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)) - other)),
    (.triggerGC, .word ((other + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)) +
      newTrig ((other + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1 + state.n)) -
        (other + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1)))
        (wordSemTheWord (holFapply store .allocSize)) limits)),
    (.endOfHeap, .word (other + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1 + state.n))),
    (.globals, .word g), (.globReal, globReal conf other (.word g)),
    (.temp 0, .word 0), (.temp 1, .word 0), (.temp 2, .word 0), (.temp 3, .word 0),
    (.temp 4, .word 0), (.temp 5, .word 0), (.temp 6, .word 0)]
  refine ⟨outMemory, outStore, k, ?_, ?_, by simpa [freeEq] using kBound, ?_⟩
  · simpa [outStore, globalEq] using execution
  · simpa [outStore, allocEq, freeEq, gensEq, index] using invariant
  · simp [outStore, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL, globalEq]

/-- Both generational branches preserve the heap/store invariant and publish
the moved global root. The partial branch also guarantees allocation space;
the source's major-collection allocation bound remains outside this composition. -/
theorem combinedGenerational_store_correct {width : Nat} [NeZero width] (conf : Config)
    (values : List DataSem.Value) (references : Spt (BvlSem.Ref DataSem.Value))
    (root : HeapAddress (WordLocW width)) (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (be : Bool) (a sp sp1 limit next a1 n1 : Nat) (gens gens1 : GenState) (limits : List Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (source : absMlInv conf values references (root :: roots, heap, be, a, sp, sp1, gens) limit next)
    (kind : conf.gcKind = .generational limits) (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit)
    (global : store.lookup .globals = some (wordAddr conf root))
    (run : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits)
      (root :: roots, heap, gens, a + sp + sp1, doPartial conf store) = (roots1, heap1, a1, n1, gens1, true)) :
    ∃ root1 rest outMemory outStore k2 k3,
      roots1 = root1 :: rest ∧
      wordGcFun conf (roots.map (wordAddr conf), memory, domain, store) =
        some (rest.map (wordAddr conf), outMemory, outStore) ∧
      heapInMemoryStore heap1 a1 k2 k3 gens1 conf outStore outMemory domain limit ∧
      k2 + k3 = n1 ∧ outStore.lookup .globals = some (wordAddr conf root1) ∧
      (wordGenGcCanDoPartial limits store → ∃ p t,
        outStore.lookup .nextFree = some (.word p) ∧ outStore.lookup .triggerGC = some (.word t) ∧
          wordSemTheWord (holFapply store .allocSize) ≤ t - p) := by
  classical
  have length := combinedGenerational_rootsLength (makeGcConf (α := List (WordLocW width)) limit) limits
    (root :: roots) roots1 heap heap1 gens gens1 (a + sp + sp1) a1 n1 (doPartial conf store) true run
  cases roots1 with
  | nil => simp at length
  | cons root1 rest =>
    by_cases selected : wordGenGcCanDoPartial limits store
    · have partialRun : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits)
          (root :: roots, heap, gens, a + sp + sp1, true) = (root1 :: rest, heap1, a1, n1, gens1, true) := by
        simpa [doPartial, kind, selected] using run
      obtain ⟨outMemory, outStore, k, execution, invariant, bound, globalOut, space⟩ :=
        combinedPartial_store_correct conf values references root root1 roots rest heap heap1 be a sp sp1 limit next
          a1 n1 gens gens1 limits store memory domain partialRun kind selected global source good heapMem
      exact ⟨root1, rest, outMemory, outStore, k, n1 - k, rfl, execution, invariant,
        Nat.add_sub_of_le bound, globalOut, fun _ => space⟩
    · have fullRun : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits)
          (root :: roots, heap, gens, a + sp + sp1, false) = (root1 :: rest, heap1, a1, n1, gens1, true) := by
        simpa [doPartial, kind, selected] using run
      have limitEq : limit = heapLength heap := source.2.1.1.symm
      obtain ⟨outMemory, outStore, k, execution, invariant, bound, globalOut⟩ :=
        combinedMajor_store_correct conf root root1 roots rest heap heap1 a sp sp1 limit a1 n1 gens gens1
          limits (a + sp + sp1) store memory domain fullRun kind selected global limitEq good heapMem
      exact ⟨root1, rest, outMemory, outStore, k, n1 - k, rfl, execution, invariant,
        Nat.add_sub_of_le bound, globalOut, fun h => False.elim (selected h)⟩

/-- The generational collector preserves the heap/store invariant and the
stack-root encoding, and partial collection leaves room for the allocation.
The source's major-collection allocation bound remains outside this composition. -/
theorem combinedGenerational_stack_correct {width : Nat} [NeZero width] (conf : Config)
    (value : DataSem.Value) (stack : List (DataSem.Value × WordLocW width))
    (references : Spt (BvlSem.Ref DataSem.Value)) (root : HeapAddress (WordLocW width))
    (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (be : Bool) (a sp sp1 limit next a1 n1 : Nat) (gens gens1 : GenState) (limits : List Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (source : absMlInv conf (value :: stack.map Prod.fst) references (root :: roots, heap, be, a, sp, sp1, gens) limit next)
    (kind : conf.gcKind = .generational limits) (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit)
    (global : wordAddr conf root = holFapply store .globals)
    (related : List.Forall₂ (fun v w => wordAddr conf v = w) roots (stack.map Prod.snd))
    (run : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits)
      (root :: roots, heap, gens, a + sp + sp1, doPartial conf store) = (roots1, heap1, a1, n1, gens1, true)) :
    ∃ stack1 outMemory outStore k2 k3 root1 rest,
      wordGcFun conf (stack.map Prod.snd, memory, domain, store) = some (stack1, outMemory, outStore) ∧
      heapInMemoryStore heap1 a1 k2 k3 gens1 conf outStore outMemory domain limit ∧ k2 + k3 = n1 ∧
      roots1 = root1 :: rest ∧ wordAddr conf root1 = holFapply outStore .globals ∧
      List.Forall₂ (fun v w => wordAddr conf v = w) rest (((stack.map Prod.fst).zip stack1).map Prod.snd) ∧
      stack1.length = stack.length ∧ (wordGenGcCanDoPartial limits store → ∃ p t,
        outStore.lookup .nextFree = some (.word p) ∧ outStore.lookup .triggerGC = some (.word t) ∧
          wordSemTheWord (holFapply store .allocSize) ≤ t - p) := by
  have lookupExists := heapMem.2.2.2.2.2.2.1
  obtain ⟨w, lookup⟩ := lookupExists
  have globalLookup : store.lookup .globals = some (wordAddr conf root) := by
    rw [holFapply_of_lookup lookup] at global
    simpa [global] using lookup
  have forallMap {α β : Type} (f : α → β) (xs : List α) (ys : List β) :
      List.Forall₂ (fun x y => f x = y) xs ys ↔ ys = xs.map f := by
    induction xs generalizing ys with
    | nil => cases ys <;> simp
    | cons x xs ih => cases ys <;> simp [List.forall₂_cons_left_iff, ih, and_comm]
  have rootsEq : stack.map Prod.snd = roots.map (wordAddr conf) := (forallMap _ _ _).mp related
  have length := combinedGenerational_rootsLength (makeGcConf (α := List (WordLocW width)) limit) limits
    (root :: roots) roots1 heap heap1 gens gens1 (a + sp + sp1) a1 n1 (doPartial conf store) true run
  obtain ⟨root1, rest, outMemory, outStore, k2, k3, rootsOut, execution, invariant, freeSum, globalOut, space⟩ :=
    combinedGenerational_store_correct conf (value :: stack.map Prod.fst) references root roots roots1 heap heap1
      be a sp sp1 limit next a1 n1 gens gens1 limits store memory domain source kind good heapMem globalLookup run
  have restLength : rest.length = stack.length := by
    have inputLength := congrArg List.length rootsEq
    simp only [List.length_map] at inputLength
    rw [rootsOut] at length
    simp only [List.length_cons] at length
    omega
  refine ⟨rest.map (wordAddr conf), outMemory, outStore, k2, k3, root1, rest, ?_, invariant, freeSum,
    rootsOut, (holFapply_of_lookup globalOut).symm, ?_, by simp [restLength], space⟩
  · simpa [rootsEq] using execution
  · apply (forallMap _ _ _).mpr
    rw [List.map_snd_zip (by simp [restLength])]

/-- Both generational branches execute the combined collector's root result
and publish its first root in the globals store field. -/
theorem combinedGenerational_store_execution {width : Nat} [NeZero width] (conf : Config)
    (values : List DataSem.Value) (references : Spt (BvlSem.Ref DataSem.Value))
    (root : HeapAddress (WordLocW width)) (roots roots1 : List (HeapAddress (WordLocW width)))
    (heap heap1 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (be : Bool) (a sp sp1 limit next a1 n1 : Nat) (gens gens1 : GenState) (limits : List Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (source : absMlInv conf values references (root :: roots, heap, be, a, sp, sp1, gens) limit next)
    (kind : conf.gcKind = .generational limits) (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit)
    (global : store.lookup .globals = some (wordAddr conf root))
    (run : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits)
      (root :: roots, heap, gens, a + sp + sp1, doPartial conf store) = (roots1, heap1, a1, n1, gens1, true)) :
    ∃ root1 rest outMemory outStore,
      roots1 = root1 :: rest ∧
      wordGcFun conf (roots.map (wordAddr conf), memory, domain, store) =
        some (rest.map (wordAddr conf), outMemory, outStore) ∧
      outStore.lookup .globals = some (wordAddr conf root1) := by
  classical
  have length := combinedGenerational_rootsLength (makeGcConf (α := List (WordLocW width)) limit) limits
    (root :: roots) roots1 heap heap1 gens gens1 (a + sp + sp1) a1 n1 (doPartial conf store) true run
  cases roots1 with
  | nil => simp at length
  | cons root1 rest =>
    by_cases selected : wordGenGcCanDoPartial limits store
    · have partialRun : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits)
          (root :: roots, heap, gens, a + sp + sp1, true) = (root1 :: rest, heap1, a1, n1, gens1, true) := by
        simpa [doPartial, kind, selected] using run
      obtain ⟨curr, other, outMemory, state, _, _, _, _, _, _, _, execution, _, _⟩ :=
        combinedPartial_store_execution conf root root1 roots rest heap heap1 values references be next a sp sp1 limit
          a1 n1 gens gens1 limits store memory domain partialRun kind selected global source good heapMem
      refine ⟨root1, rest, outMemory, _, rfl, execution, ?_⟩
      simp [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL]
    · have fullRun : gcCombined (makeGcConf (α := List (WordLocW width)) limit) (.generational limits)
          (root :: roots, heap, gens, a + sp + sp1, false) = (root1 :: rest, heap1, a1, n1, gens1, true) := by
        simpa [doPartial, kind, selected] using run
      have limitEq : limit = heapLength heap := source.2.1.1.symm
      obtain ⟨curr, other, outMemory, state, _, _, _, _, _, _, _, execution, _, _⟩ :=
        combinedMajor_store_execution conf root root1 roots rest heap heap1 a sp sp1 limit a1 n1 gens gens1
          limits (a + sp + sp1) store memory domain fullRun kind selected global limitEq good heapMem
      refine ⟨root1, rest, outMemory, _, rfl, execution, ?_⟩
      simp [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
