module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialAccumulator
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialSplit

@[expose] public section

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

/-- Partial root movement advances its allocation index by the size of
newly copied data. -/
theorem partialMove_dataIndex {α β : Type} (conf : GenGcPartial.Config β)
    (state state1 : GcState α β) (root root1 : HeapAddress α)
    (run : GenGcPartial.gcMove conf state root = (root1, state1)) :
    state1.a + heapLength state.h1 + heapLength state.h2 =
      state.a + heapLength state1.h1 + heapLength state1.h2 := by
  cases root with
  | data value => simp [GenGcPartial.gcMove, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
  | pointer ptr value =>
    by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
    · simp [GenGcPartial.gcMove, outside, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
    · cases found : heapLookup ptr state.heap with
      | none => simp [GenGcPartial.gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
      | some element =>
        cases element with
        | unused len => simp [GenGcPartial.gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
        | forwardPointer dest old len => simp [GenGcPartial.gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
        | dataElement roots len payload =>
          simp [GenGcPartial.gcMove, outside, found, Prod.mk.injEq] at run
          obtain ⟨_, rfl⟩ := run
          simp [heapLength, elLength]
          omega

/-- Traversing roots preserves the partial allocation-index relationship. -/
theorem partialMoveList_dataIndex {α β : Type} (conf : GenGcPartial.Config β)
    (roots roots1 : List (HeapAddress α)) (state state1 : GcState α β)
    (run : GenGcPartial.gcMoveList conf state roots = (roots1, state1)) :
    state1.a + heapLength state.h1 + heapLength state.h2 =
      state.a + heapLength state1.h1 + heapLength state1.h2 := by
  induction roots generalizing roots1 state state1 with
  | nil => simp [GenGcPartial.gcMoveList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
  | cons root roots ih =>
    simp only [GenGcPartial.gcMoveList] at run
    generalize headRun : GenGcPartial.gcMove conf state root = headResult at run
    obtain ⟨root1, middle⟩ := headResult
    generalize tailRun : GenGcPartial.gcMoveList conf middle roots = tailResult at run
    obtain ⟨tail, final⟩ := tailResult
    simp only [Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    have first := partialMove_dataIndex conf state middle root root1 headRun
    have second := ih tail middle final tailRun
    omega

/-- Reference traversal preserves the partial allocation-index relationship. -/
theorem partialMoveRefList_dataIndex {α β γ : Type} (conf : GenGcPartial.Config γ)
    (refs refs1 : List (HeapElement α β)) (state state1 : GcState α γ)
    (run : GenGcPartial.gcMoveRefList conf state refs = (refs1, state1)) :
    state1.a + heapLength state.h1 + heapLength state.h2 =
      state.a + heapLength state1.h1 + heapLength state1.h2 := by
  induction refs generalizing refs1 state state1 with
  | nil => simp [GenGcPartial.gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
  | cons head tail ih =>
    cases head with
    | unused len => simp [GenGcPartial.gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
    | forwardPointer ptr value len => simp [GenGcPartial.gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
    | dataElement roots len payload =>
      simp only [GenGcPartial.gcMoveRefList] at run
      generalize headRun : GenGcPartial.gcMoveList conf state roots = headResult at run
      obtain ⟨roots1, middle⟩ := headResult
      generalize tailRun : GenGcPartial.gcMoveRefList conf middle tail = tailResult at run
      obtain ⟨tail1, final⟩ := tailResult
      simp only [Prod.mk.injEq] at run
      obtain ⟨_, rfl⟩ := run
      have first := partialMoveList_dataIndex conf roots roots1 state middle headRun
      have second := ih tail1 middle final tailRun
      omega

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
