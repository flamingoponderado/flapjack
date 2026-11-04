import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialAccumulator
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialSplit

/-! Length invariants for the partial generational collector. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend

/-- A successful partial move transfers words from free space to copied data. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_partial_move_heap_lengths"]
theorem partialMove_heapLengths {α β : Type} (conf : GenGcPartial.Config β)
    (state state1 : GcState α β) (root root1 : HeapAddress α)
    (run : GenGcPartial.gcMove conf state root = (root1, state1)) (ok : state1.ok = true) :
    state.n + heapLength state.h2 = state1.n + heapLength state1.h2 := by
  cases root with
  | data value => simp [GenGcPartial.gcMove, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
  | pointer ptr value =>
    by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
    · simp [GenGcPartial.gcMove, outside, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
    · cases found : heapLookup ptr state.heap with
      | none => simp [GenGcPartial.gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; simp at ok
      | some element =>
        cases element with
        | unused len => simp [GenGcPartial.gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; simp at ok
        | forwardPointer dest old len => simp [GenGcPartial.gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
        | dataElement roots len payload =>
          cases forward : gcForwardPtr ptr state.heap state.a value
              ((state.ok && decide (ptr < heapLength state.heap)) && decide (len + 1 ≤ state.n) && !(conf.isRef payload)) with
          | mk newHeap status =>
            simp only [GenGcPartial.gcMove, outside, ↓reduceIte, found, forward, Prod.mk.injEq] at run
            obtain ⟨_, rfl⟩ := run
            have statusTrue : status = true := ok
            subst status
            have check := gcForwardPtr_ok state.heap ptr state.a value
              ((state.ok && decide (ptr < heapLength state.heap)) && decide (len + 1 ≤ state.n) && !(conf.isRef payload)) newHeap forward
            simp only [Bool.and_eq_true, decide_eq_true_eq] at check
            change state.n + heapLength state.h2 =
              (state.n - (len + 1)) + heapLength (state.h2 ++ [.dataElement roots len payload])
            rw [heapLength_append]
            simp only [heapLength, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, elLength]
            omega

/-- The same free-space accounting holds for a successful root traversal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_partial_move_list_heap_lengths"]
theorem partialMoveList_heapLengths {α β : Type} (roots : List (HeapAddress α))
    (conf : GenGcPartial.Config β) (state : GcState α β) (roots1 : List (HeapAddress α)) (state1 : GcState α β)
    (run : GenGcPartial.gcMoveList conf state roots = (roots1, state1)) (ok : state1.ok = true) :
    state.n + heapLength state.h2 = state1.n + heapLength state1.h2 := by
  induction roots generalizing state roots1 state1 with
  | nil => simp [GenGcPartial.gcMoveList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
  | cons root roots ih =>
    simp only [GenGcPartial.gcMoveList] at run
    generalize headRun : GenGcPartial.gcMove conf state root = result at run
    obtain ⟨rootMid, middle⟩ := result
    generalize tailRun : GenGcPartial.gcMoveList conf middle roots = result at run
    obtain ⟨tail, final⟩ := result
    simp only [Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    have middleOk := partialMoveList_okBefore conf roots middle tail final tailRun ok
    exact (partialMove_heapLengths conf state middle root rootMid headRun middleOk).trans
      (ih middle tail final tailRun ok)

/-- The source partition invariant for minor collection. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "partial_len_inv_def"]
def partialLenInv {α β : Type} (state : GcState α β) : Prop :=
  heapLength state.heap = heapLength (state.h1 ++ state.h2) + state.n +
    heapLength (state.r4 ++ state.r3 ++ state.r2 ++ state.r1 ++ state.old)

/-- A partial root move leaves the scanned data, old region and reference
accumulators unchanged. This is local infrastructure for the scan proof. -/
theorem partialMove_fixedFields {α β : Type} (conf : GenGcPartial.Config β)
    (state state1 : GcState α β) (root root1 : HeapAddress α)
    (run : GenGcPartial.gcMove conf state root = (root1, state1)) :
    state1.h1 = state.h1 ∧ state1.r4 = state.r4 ∧ state1.r3 = state.r3 ∧
      state1.r2 = state.r2 ∧ state1.r1 = state.r1 ∧ state1.old = state.old := by
  cases root with
  | data value => simp [GenGcPartial.gcMove, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | pointer ptr value =>
    by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
    · simp [GenGcPartial.gcMove, outside, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases found : heapLookup ptr state.heap with
      | none => simp [GenGcPartial.gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      | some element =>
        cases element with
        | unused len => simp [GenGcPartial.gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        | forwardPointer dest old len => simp [GenGcPartial.gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        | dataElement roots len payload =>
          cases forward : gcForwardPtr ptr state.heap state.a value
              ((state.ok && decide (ptr < heapLength state.heap)) && decide (len + 1 ≤ state.n) && !(conf.isRef payload)) with
          | mk newHeap status =>
            simp only [GenGcPartial.gcMove, outside, ↓reduceIte, found, forward, Prod.mk.injEq] at run
            obtain ⟨_, rfl⟩ := run
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Root traversal preserves the same fixed collector fields. -/
theorem partialMoveList_fixedFields {α β : Type} (conf : GenGcPartial.Config β)
    (roots roots1 : List (HeapAddress α)) (state state1 : GcState α β)
    (run : GenGcPartial.gcMoveList conf state roots = (roots1, state1)) :
    state1.h1 = state.h1 ∧ state1.r4 = state.r4 ∧ state1.r3 = state.r3 ∧
      state1.r2 = state.r2 ∧ state1.r1 = state.r1 ∧ state1.old = state.old := by
  induction roots generalizing roots1 state state1 with
  | nil => simp [GenGcPartial.gcMoveList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons root roots ih =>
    simp only [GenGcPartial.gcMoveList] at run
    generalize headRun : GenGcPartial.gcMove conf state root = result at run
    obtain ⟨rootMid, middle⟩ := result
    generalize tailRun : GenGcPartial.gcMoveList conf middle roots = result at run
    obtain ⟨tail, final⟩ := result
    simp only [Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := partialMove_fixedFields conf state middle root rootMid headRun
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := ih tail middle final tailRun
    exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
