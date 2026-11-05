import Flapjack.Compiler.Backend.GenGcPartial.Proofs.Simulation
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalStore

/-! Partial collection and the abstract memory invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.GcCombined
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

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
        (addrMap (holFapply f) roots, state.old ++ state.h1 ++ heapExpand state.n ++ state.r1, be) := by
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
  refine ⟨state, f, run, domain, ?_, related, ok, ?_, ?_⟩
  · simpa [makePartialConf, makeGcConf] using heapWell
  · exact rootsOk_gcRelated roots heap _ f related domain
  · exact bcStackRefInv_gcRelated conf next stack refs roots heap _ be f related domain stackGood

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
