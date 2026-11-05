import Flapjack.Compiler.Backend.GenGcPartial.Proofs.Simulation
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalStore

/-! Partial collection and the abstract memory invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.GcCombined
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- Flapjack infrastructure: scanning appends only data elements to a
data-only copied prefix. -/
theorem partialScan_h1Data {α β : Type} (conf : GenGcPartial.Config β) (state : GcState α β)
    (data : List.Forall isDataElement state.h1) :
    List.Forall isDataElement (GenGcPartial.gcMoveData conf state).h1 := by
  classical
  induction state using GenGcPartial.gcMoveData.induct conf with
  | case1 state empty => rw [GenGcPartial.gcMoveData]; simpa [empty] using data
  | case2 state head tail heap over => rw [GenGcPartial.gcMoveData]; simpa [heap, over] using data
  | case3 state tail roots len payload roots1 middle move heap bounded flag ih =>
    have fixed := (partialMoveList_fixedFields conf roots roots1 state middle move).1
    have nextData : List.Forall isDataElement
        (middle.h1 ++ [HeapElement.dataElement roots1 len payload]) := by
      simpa [fixed, isDataElement] using data
    cases state with
    | mk old h1 h2 r4 r3 r2 r1 a n status origHeap heap0 =>
      simp only at heap
      subst h2
      rw [GenGcPartial.gcMoveData]
      simpa only [bounded, ↓reduceIte, move] using ih nextData
  | case4 state head tail heap bounded notData =>
    cases head with
    | unused len => rw [GenGcPartial.gcMoveData]; simpa [heap, bounded] using data
    | forwardPointer ptr value len => rw [GenGcPartial.gcMoveData]; simpa [heap, bounded] using data
    | dataElement roots len payload => exact False.elim (notData roots len payload rfl)

/-- Flapjack infrastructure: every successful partial collection has a
data-only copied prefix and has exhausted its copied-data queue. -/
theorem partialCollection_copiedData {α β : Type} (conf : GenGcPartial.Config β)
    (roots roots1 : List (HeapAddress α)) (heap : List (HeapElement α β)) (state : GcState α β)
    (run : GenGcPartial.partialGc conf (roots, heap) = (roots1, state)) (ok : state.ok = true) :
    List.Forall isDataElement state.h1 ∧ state.h2 = [] := by
  obtain ⟨old, current, refs, middle, refs1, afterRefs, _, rootsRun, _, refsRun, _, dataRun⟩ :=
    partialFull_abstractSteps conf roots roots1 heap state run ok
  have rootH1 := (partialMoveList_fixedFields conf roots roots1 _ middle rootsRun).1
  have refsH1 := (partialFull_refListFixed conf refs refs1 middle afterRefs refsRun).1
  have initialData : List.Forall isDataElement
      ({ afterRefs with r1 := refs1, r2 := [] } : GcState α β).h1 := by
    simp [refsH1, rootH1, emptyGcState]
  have scanData := partialScan_h1Data conf _ initialData
  have scanEmpty := GenGcPartial.gcMoveData_h2 conf { afterRefs with r1 := refs1, r2 := [] }
    (by rw [dataRun]; exact ok)
  rw [dataRun] at scanData scanEmpty
  exact ⟨scanData, scanEmpty⟩

/-- Flapjack infrastructure: appending an arbitrary reference suffix does
not change the free region following a data-only heap prefix. -/
theorem unusedSpaceInv_heapExpand_suffix {α β : Type}
    (before suffix : List (HeapElement α β)) (free : Nat)
    (data : ∀ element ∈ before, isDataElement element) :
    unusedSpaceInv (heapLength before) free (before ++ heapExpand free ++ suffix) := by
  rw [List.append_assoc]
  refine ⟨?_, ?_, ?_⟩
  · intro nonzero
    rw [GenGc.heapLookup_append]
    simp [heapExpand, nonzero, heapLookup]
  · simp [heapLength_append, heapLength_heapExpand]
  · exact ⟨before, heapExpand free ++ suffix, heapSplit_append before (heapExpand free ++ suffix), data⟩

/-- Flapjack infrastructure: a successful partial collection whose old
generation is data-only restores the abstract free-space invariant. -/
theorem partialCollection_unusedSpace {α β : Type} (conf : GenGcPartial.Config β)
    (roots roots1 : List (HeapAddress α)) (heap : List (HeapElement α β)) (state : GcState α β)
    (run : GenGcPartial.partialGc conf (roots, heap) = (roots1, state)) (ok : state.ok = true)
    (oldData : ∀ element ∈ state.old, isDataElement element) :
    unusedSpaceInv state.a (state.n + 0) (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1) := by
  obtain ⟨copiedData, empty⟩ := partialCollection_copiedData conf roots roots1 heap state run ok
  have index := partialFull_dataIndex conf roots roots1 heap state run ok empty
  have prefixData : ∀ element ∈ state.old ++ state.h1, isDataElement element := by
    intro element member
    rcases List.mem_append.mp member with old | copied
    · exact oldData element old
    · exact List.forall_iff_forall_mem.mp copiedData element copied
  simpa [index] using unusedSpaceInv_heapExpand_suffix (state.old ++ state.h1) state.r1 state.n prefixData

/-- Flapjack infrastructure: after collection, the allocation boundary is a
valid reset generation start because no heap pointer targets free space. -/
theorem genStartOk_heapExpand_suffix {α β : Type}
    (before suffix : List (HeapElement α β)) (free limit : Nat)
    (valid : heapOk (before ++ heapExpand free ++ suffix) limit) :
    genStartOk (before ++ heapExpand free ++ suffix) (heapLength before + free) (heapLength before) := by
  rw [List.append_assoc] at valid ⊢
  refine ⟨before, heapExpand free ++ suffix, heapSplit_append before _, ?_⟩
  intro xs len payload ptr value pair
  obtain ⟨element, child⟩ := pair
  have found := valid.2.2 xs len payload ptr value
    ⟨List.mem_append.mpr (Or.inl element), child⟩
  by_contra outside
  have lower : heapLength before ≤ ptr := by omega
  have upper : ptr - heapLength before < free := by omega
  have notData : ¬ isSomeDataElement (heapLookup (ptr - heapLength before) (heapExpand free : List (HeapElement α β))) :=
    GenGcPartial.heapLookup_heapExpand_notData _ _
  rw [GenGc.heapLookup_append, if_neg (Nat.not_lt.mpr lower), GenGc.heapLookup_append,
    heapLength_heapExpand, if_pos upper] at found
  exact notData found

/-- Two ordered, valid heap boundaries form a three-way heap segment. -/
theorem heapSegment_of_ordered_splits {α β : Type}
    (heap old rest before refs : List (HeapElement α β)) (start finish : Nat)
    (first : heapSplit start heap = some (old, rest))
    (second : heapSplit finish heap = some (before, refs)) (ordered : start ≤ finish) :
    ∃ current, heapSegment (start, finish) heap = some (old, current, refs) := by
  obtain ⟨oldLen, _, oldWhole⟩ := heapSplit_heapLength heap old rest start first
  obtain ⟨beforeLen, _, beforeWhole⟩ := heapSplit_heapLength heap before refs finish second
  have oldPrefix : old <+: heap := ⟨rest, oldWhole⟩
  have beforePrefix : before <+: heap := ⟨refs, beforeWhole⟩
  have included : old <+: before := by
    rcases List.prefix_or_prefix_of_prefix oldPrefix beforePrefix with h | h
    · exact h
    · obtain ⟨tail, eq⟩ := h
      have zero : heapLength tail = 0 := by
        have lengths := congrArg heapLength eq
        rw [heapLength_append, beforeLen, oldLen] at lengths
        omega
      have empty : tail = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (by
        have bound := length_le_heapLength tail
        omega))
      simp only [empty, List.append_nil] at eq
      subst old
      exact ⟨[], by simp⟩
  obtain ⟨current, beforeEq⟩ := included
  have restEq : rest = current ++ refs := by
    rw [← beforeEq, List.append_assoc] at beforeWhole
    exact List.append_cancel_left (oldWhole.trans beforeWhole.symm)
  have currentLen : heapLength current = finish - start := by
    rw [← beforeEq, heapLength_append, oldLen] at beforeLen
    omega
  refine ⟨current, ?_⟩
  simp [heapSegment, first, oldLen, Nat.not_lt.mpr ordered, restEq, ← currentLen,
    heapSplit_append]

/-- The abstract generation and free-space invariants imply the collector's
generation partition for the first active generation. -/
theorem partialSource_heapGenOk {α β : Type}
    (conf : Config) (heap : List (HeapElement α (HeapTag × β)))
    (gc : GenGc.Config (HeapTag × β)) (a sp sp1 limit : Nat)
    (count start : Nat) (tail sizes : List Nat)
    (kind : conf.gcKind = .generational sizes)
    (invariant : gcKindInv conf a sp sp1 (.genState count (start :: tail)) heap)
    (unused : unusedSpaceInv a (sp + sp1) heap)
    (bound : heapLength heap = limit) (gcLimit : gc.limit = limit)
    (classify : ∀ tag payload, gc.isRef (tag, payload) = true ↔ isMutTag tag) :
    GenGcPartial.heapGenOk heap (makePartialConf gc (.genState count (start :: tail)) (a + sp + sp1)) := by
  simp only [gcKindInv, kind, genStateOk] at invariant
  obtain ⟨⟨startsBound, startsOk⟩, before, refs, refSplit, beforeNonref, refsRef⟩ := invariant
  have startBound : start ≤ a := startsBound start (by simp)
  obtain ⟨old, rest, oldSplit, pointers⟩ := startsOk start (by simp)
  obtain ⟨current, segment⟩ := heapSegment_of_ordered_splits heap old rest before refs
    start (a + sp + sp1) oldSplit refSplit (by omega)
  obtain ⟨whole, oldLen, beforeLen, _⟩ := heapSegment_imp heap start (a + sp + sp1) old current refs segment
  have beforeEq : old ++ current = before := by
    have split := heapSplit_append (old ++ current) refs
    rw [beforeLen, whole, refSplit] at split
    exact (Prod.mk.inj (Option.some.inj split)).1.symm
  have oldData := partialSource_oldData heap old current refs start (a + sp + sp1) a segment unused.2.2 startBound
  have noRef : ∀ element ∈ old ++ current, ¬ isRef element := by
    simpa [beforeEq] using beforeNonref
  have refsData : List.Forall isDataElement refs := by
    rw [List.forall_iff_forall_mem]
    intro element member
    have ref := refsRef element member
    cases element <;> simp_all [isRef, isDataElement]
  dsimp only [makePartialConf, holHd, GenGcPartial.heapGenOk]
  refine ⟨old, current, refs, by omega, ?_, List.forall_iff_forall_mem.mpr oldData,
    refsData, segment.symm, ?_, ?_, ?_, ?_⟩
  · rw [gcLimit, ← bound]
    have freeBound := unused.2.1
    omega
  · intro ptr xs len payload value member
    exact pointers xs len payload ptr value member
  · intro xs len payload member
    cases payload with
    | mk tag payload =>
      have notRef := noRef (.dataElement xs len (tag, payload)) (List.mem_append_left current member)
      have bad : ¬ isMutTag tag := by simpa [isRef] using notRef
      cases found : gc.isRef (tag, payload) with
      | false => rfl
      | true => exact False.elim (bad ((classify tag payload).mp found))
  · intro xs len payload member
    cases payload with
    | mk tag payload =>
      have notRef := noRef (.dataElement xs len (tag, payload)) (List.mem_append_right old member)
      have bad : ¬ isMutTag tag := by simpa [isRef] using notRef
      cases found : gc.isRef (tag, payload) with
      | false => rfl
      | true => exact False.elim (bad ((classify tag payload).mp found))
  · intro xs len payload member
    cases payload with
    | mk tag payload =>
      apply (classify tag payload).mpr
      simpa [isRef] using refsRef (.dataElement xs len (tag, payload)) member

/-- An abstract ML state with an active generation admits a successful partial
collection with the source heap relation and well-formed output heap. The
remaining abstract memory conditions are established separately. -/
theorem partialGc_source_related {width : Nat} [NeZero width]
    (conf : Config) (stack : List DataSem.Value) (refs : Spt (BvlSem.Ref DataSem.Value))
    (roots : List (HeapAddress (WordLocW width)))
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (be : Bool) (a sp sp1 limit next count start : Nat) (tail sizes : List Nat)
    (valid : absMlInv conf stack refs
      (roots, heap, be, a, sp, sp1, .genState count (start :: tail)) limit next)
    (kind : conf.gcKind = .generational sizes) :
    ∃ (state : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
      (f : HolFiniteMapExact Nat Nat),
      GenGcPartial.partialGc
        (makePartialConf (makeGcConf limit) (.genState count (start :: tail)) (a + sp + sp1))
        (roots, heap) = (addrMap (holFapply f) roots, state) ∧
      (∀ ptr value, .pointer ptr value ∈ roots → f.lookup ptr ≠ none) ∧
      heapOk (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1) limit ∧
      gcRelated f heap (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1) ∧ state.ok = true ∧
      rootsOk (addrMap (holFapply f) roots) (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1) ∧
      bcStackRefInv conf next stack refs
        (addrMap (holFapply f) roots, state.old ++ state.h1 ++ heapExpand state.n ++ state.r1, be) ∧
      unusedSpaceInv state.a (state.n + 0) (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1) ∧
      genStateOk state.a (state.a + state.n + 0) (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1)
        (.genState 0 (sizes.map fun _ => state.a)) := by
  obtain ⟨rootOk, heapGood, gcOk, unused, stackGood⟩ := valid
  have classify : ∀ tag payload, (makeGcConf (α := List (WordLocW width)) limit).isRef (tag, payload) = true ↔ isMutTag tag := by
    intro tag payload
    simp [makeGcConf]
  have generations := partialSource_heapGenOk conf heap (makeGcConf limit) a sp sp1 limit
    count start tail sizes kind gcOk unused heapGood.1 rfl classify
  have result := GenGcPartial.partialGc_related
    (makePartialConf (makeGcConf limit) (.genState count (start :: tail)) (a + sp + sp1))
    roots heap rootOk (by simpa [makePartialConf, makeGcConf] using heapGood) generations
  obtain ⟨state, f, run, domain, heapWell, related, ok⟩ := result
  refine ⟨state, f, run, domain, ?_, related, ok, ?_, ?_, ?_, ?_⟩
  · simpa [makePartialConf, makeGcConf] using heapWell
  · exact rootsOk_gcRelated roots heap _ f related domain
  · exact bcStackRefInv_gcRelated conf next stack refs roots heap _ be f related domain stackGood
  · obtain ⟨old, current, refHeap, _, _, oldData, _, segment, _⟩ := generations
    have oldEq := (GenGcPartial.partialGc_regions
      (makePartialConf (makeGcConf limit) (.genState count (start :: tail)) (a + sp + sp1))
      roots (addrMap (holFapply f) roots) heap old current refHeap state segment.symm run).1
    apply partialCollection_unusedSpace _ _ _ heap state run ok
    rw [oldEq]
    exact List.forall_iff_forall_mem.mp oldData
  · have empty := (partialCollection_copiedData _ _ _ heap state run ok).2
    have index := partialFull_dataIndex _ _ _ heap state run ok empty
    have heapValid : heapOk (state.old ++ state.h1 ++ heapExpand state.n ++ state.r1) limit := by
      simpa [makePartialConf, makeGcConf] using heapWell
    have start := genStartOk_heapExpand_suffix (state.old ++ state.h1) state.r1 state.n limit heapValid
    simp only [genStateOk, List.mem_map, forall_exists_index, and_imp]
    constructor
    · intros; omega
    · intro element _ _ equal
      subst element
      simpa [index] using start

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
