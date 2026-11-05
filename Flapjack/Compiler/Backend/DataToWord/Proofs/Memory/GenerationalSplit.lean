import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Abstract
import Flapjack.Compiler.Backend.GenGc

/-! Data and reference partition invariants for major collection. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend

/-- Classify the pending data and reference cells during a major collection.
This predicate is Flapjack proof infrastructure. -/
def pendingDataRefsSplit {α β : Type} (state : GcState α (HeapTag × β)) : Prop :=
  (∀ element ∈ state.h2, isDataElement element) ∧
  (∀ element ∈ state.h2, ¬ isRef element) ∧
  ∀ element ∈ state.r4, isRef element

/-- Moving one root preserves the pending-cell partition. -/
theorem gcMove_pendingDataRefsSplit {α β : Type}
    (conf : GenGc.Config (HeapTag × β)) (state : GcState α (HeapTag × β))
    (root : HeapAddress α)
    (classify : ∀ tag payload, conf.isRef (tag, payload) = true ↔ isMutTag tag)
    (invariant : pendingDataRefsSplit state) :
    pendingDataRefsSplit (GenGc.gcMove conf state root).2 := by
  cases root with
  | data value => simpa [GenGc.gcMove] using invariant
  | pointer ptr value =>
    cases found : heapLookup ptr state.heap with
    | none => simpa [GenGc.gcMove, found, pendingDataRefsSplit] using invariant
    | some element =>
      cases element with
      | unused len => simpa [GenGc.gcMove, found, pendingDataRefsSplit] using invariant
      | forwardPointer destination old len => simpa [GenGc.gcMove, found] using invariant
      | dataElement addresses len payload =>
        rcases payload with ⟨tag, payload⟩
        cases ref : conf.isRef (tag, payload) with
        | false =>
          have notRef : ¬ isMutTag tag := by
            intro mutableTag
            have yes := (classify tag payload).mpr mutableTag
            rw [ref] at yes
            contradiction
          simpa [GenGc.gcMove, found, ref, pendingDataRefsSplit, isDataElement, isRef, notRef,
            or_imp, forall_and] using invariant
        | true =>
          have mutableTag : isMutTag tag := (classify tag payload).mp ref
          simpa [GenGc.gcMove, found, ref, pendingDataRefsSplit, isRef, mutableTag] using invariant

/-- A root traversal preserves the pending-cell partition. -/
theorem gcMoveList_pendingDataRefsSplit {α β : Type}
    (conf : GenGc.Config (HeapTag × β)) (state : GcState α (HeapTag × β))
    (roots : List (HeapAddress α))
    (classify : ∀ tag payload, conf.isRef (tag, payload) = true ↔ isMutTag tag)
    (invariant : pendingDataRefsSplit state) :
    pendingDataRefsSplit (GenGc.gcMoveList conf state roots).2 := by
  induction roots generalizing state with
  | nil => simpa [GenGc.gcMoveList] using invariant
  | cons root roots ih =>
    simp only [GenGc.gcMoveList]
    generalize moved : GenGc.gcMove conf state root = result
    rcases result with ⟨root1, state1⟩
    have next := gcMove_pendingDataRefsSplit conf state root classify invariant
    rw [moved] at next
    exact ih state1 next

/-- Root movement does not alter the scanned reference segments. This is
Flapjack infrastructure for the reference-scan partition proof. -/
theorem gcMove_refsUnchanged {α β : Type} (conf : GenGc.Config β)
    (state : GcState α β) (root : HeapAddress α) :
    (GenGc.gcMove conf state root).2.r1 = state.r1 ∧
    (GenGc.gcMove conf state root).2.r2 = state.r2 ∧
    (GenGc.gcMove conf state root).2.r3 = state.r3 := by
  cases root with
  | data value => simp [GenGc.gcMove]
  | pointer ptr value =>
    cases found : heapLookup ptr state.heap with
    | none => simp [GenGc.gcMove, found]
    | some element =>
      cases element with
      | unused len => simp [GenGc.gcMove, found]
      | forwardPointer dest old len => simp [GenGc.gcMove, found]
      | dataElement addresses len payload =>
        cases ref : conf.isRef payload <;> simp [GenGc.gcMove, found, ref]

/-- A root traversal preserves the scanned reference segments. -/
theorem gcMoveList_refsUnchanged {α β : Type} (conf : GenGc.Config β)
    (state : GcState α β) (roots : List (HeapAddress α)) :
    (GenGc.gcMoveList conf state roots).2.r1 = state.r1 ∧
    (GenGc.gcMoveList conf state roots).2.r2 = state.r2 ∧
    (GenGc.gcMoveList conf state roots).2.r3 = state.r3 := by
  induction roots generalizing state with
  | nil => simp [GenGc.gcMoveList]
  | cons root roots ih =>
    simp only [GenGc.gcMoveList]
    generalize moved : GenGc.gcMove conf state root = result
    rcases result with ⟨root1, state1⟩
    have unchanged := gcMove_refsUnchanged conf state root
    rw [moved] at unchanged
    obtain ⟨first, second, third⟩ := ih state1
    exact ⟨first.trans unchanged.1, second.trans unchanged.2.1, third.trans unchanged.2.2⟩

/-- All copied data segments contain data objects with nonmutable tags, and
all reference segments contain mutable objects. This is Flapjack proof
infrastructure for the major collector's partition. -/
def dataRefsSplit {α β : Type} (state : GcState α (HeapTag × β)) : Prop :=
  (∀ element ∈ state.h1, isDataElement element ∧ ¬ isRef element) ∧
  (∀ element ∈ state.h2, isDataElement element ∧ ¬ isRef element) ∧
  (∀ element ∈ state.r1, isRef element) ∧
  (∀ element ∈ state.r2, isRef element) ∧
  (∀ element ∈ state.r3, isRef element) ∧
  ∀ element ∈ state.r4, isRef element

/-- Moving roots preserves every segment of the collector partition. -/
theorem gcMoveList_dataRefsSplit {α β : Type}
    (conf : GenGc.Config (HeapTag × β)) (state : GcState α (HeapTag × β))
    (roots : List (HeapAddress α))
    (classify : ∀ tag payload, conf.isRef (tag, payload) = true ↔ isMutTag tag)
    (invariant : dataRefsSplit state) : dataRefsSplit (GenGc.gcMoveList conf state roots).2 := by
  have pending : pendingDataRefsSplit state :=
    ⟨fun e mem => (invariant.2.1 e mem).1, fun e mem => (invariant.2.1 e mem).2, invariant.2.2.2.2.2⟩
  have next := gcMoveList_pendingDataRefsSplit conf state roots classify pending
  have left := GenGc.gcMoveList_h1 conf state roots
  have unchanged := gcMoveList_refsUnchanged conf state roots
  refine ⟨?_, ?_, ?_, ?_, ?_, next.2.2⟩
  · simpa [left] using invariant.1
  · intro e member
    exact ⟨next.1 e member, next.2.1 e member⟩
  · simpa [unchanged.1] using invariant.2.2.1
  · simpa [unchanged.2.1] using invariant.2.2.2.1
  · simpa [unchanged.2.2] using invariant.2.2.2.2.1

/-- Reference scanning preserves the collector's data/reference partition. -/
theorem gcMoveRefs_dataRefsSplit {α β : Type}
    (conf : GenGc.Config (HeapTag × β)) (state : GcState α (HeapTag × β))
    (classify : ∀ tag payload, conf.isRef (tag, payload) = true ↔ isMutTag tag)
    (invariant : dataRefsSplit state) : dataRefsSplit (GenGc.gcMoveRefs conf state) := by
  induction state using GenGc.gcMoveRefs.induct conf with
  | case1 state empty =>
    cases state with
    | mk old h1 h2 r4 r3 r2 r1 a n status heap heap0 =>
      simp only at empty
      subst r2
      rw [GenGc.gcMoveRefs]
      simpa [dataRefsSplit, List.mem_append, or_imp, forall_and, and_comm, and_left_comm, and_assoc] using invariant
  | case2 state tail roots len payload refs roots1 middle move refsAgain ih =>
    have moved := gcMoveList_dataRefsSplit conf state roots classify invariant
    rw [move] at moved
    have unchanged := gcMoveList_refsUnchanged conf state roots
    rw [move] at unchanged
    have headRef : isRef (.dataElement roots len payload) := by
      apply invariant.2.2.2.1
      rw [refs]
      simp
    have newInv : dataRefsSplit { middle with r2 := tail, r3 := middle.r3 ++ [.dataElement roots1 len payload] } := by
      rcases payload with ⟨tag, payload⟩
      simp only [isRef] at headRef
      simp only [dataRefsSplit] at moved ⊢
      refine ⟨moved.1, moved.2.1, moved.2.2.1, ?_, ?_, moved.2.2.2.2.2⟩
      · intro element member
        apply moved.2.2.2.1 element
        rw [unchanged.2.1, refs]
        simp [member]
      · intro element member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with member | rfl
        · exact moved.2.2.2.2.1 element member
        · simpa [isRef] using headRef
    cases state with
    | mk old h1 h2 r4 r3 r2 r1 a n status heap heap0 =>
      simp only at refs
      subst r2
      rw [GenGc.gcMoveRefs]
      simp only [move]
      exact ih newInv
  | case3 state head tail refs refsAgain notData =>
    have headRef : isRef head := by
      apply invariant.2.2.2.1
      rw [refs]
      simp
    cases head with
    | unused len => simp [isRef] at headRef
    | forwardPointer ptr value len => simp [isRef] at headRef
    | dataElement roots len payload => exact False.elim (notData roots len payload refs rfl (by rfl))

/-- Data scanning preserves the collector's data/reference partition. -/
theorem gcMoveData_dataRefsSplit {α β : Type}
    (conf : GenGc.Config (HeapTag × β)) (state : GcState α (HeapTag × β))
    (classify : ∀ tag payload, conf.isRef (tag, payload) = true ↔ isMutTag tag)
    (invariant : dataRefsSplit state) : dataRefsSplit (GenGc.gcMoveData conf state) := by
  classical
  induction state using GenGc.gcMoveData.induct conf with
  | case1 state empty => rw [GenGc.gcMoveData]; simpa [empty] using invariant
  | case2 state head tail heap over =>
    rw [GenGc.gcMoveData]
    simpa [heap, over, dataRefsSplit] using invariant
  | case3 state tail roots len payload roots1 middle move heap bounded flag ih =>
    have moved := gcMoveList_dataRefsSplit conf state roots classify invariant
    rw [move] at moved
    have headData : isDataElement (.dataElement roots len payload) ∧ ¬ isRef (.dataElement roots len payload) := by
      apply invariant.2.1
      rw [heap]
      simp
    have newInv : dataRefsSplit { middle with h1 := middle.h1 ++ [.dataElement roots1 len payload], h2 := middle.h2.drop 1, ok := flag } := by
      rcases payload with ⟨tag, payload⟩
      simp only [isDataElement, isRef] at headData
      simp only [dataRefsSplit] at moved ⊢
      refine ⟨?_, ?_, moved.2.2.1, moved.2.2.2.1, moved.2.2.2.2.1, moved.2.2.2.2.2⟩
      · intro element member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with member | rfl
        · exact moved.1 element member
        · simpa [isDataElement, isRef] using headData
      · intro element member
        exact moved.2.1 element (List.mem_of_mem_drop member)
    cases state with
    | mk old h1 h2 r4 r3 r2 r1 a n status origHeap heap0 =>
      simp only at heap
      subst h2
      rw [GenGc.gcMoveData]
      simp only [bounded, ↓reduceIte, move]
      exact ih newInv
  | case4 state head tail heap bounded notData =>
    have headData : isDataElement head := by
      exact (invariant.2.1 head (by rw [heap]; simp)).1
    cases head with
    | unused len => simp [isDataElement] at headData
    | forwardPointer ptr value len => simp [isDataElement] at headData
    | dataElement roots len payload => exact False.elim (notData roots len payload rfl)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
