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

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
