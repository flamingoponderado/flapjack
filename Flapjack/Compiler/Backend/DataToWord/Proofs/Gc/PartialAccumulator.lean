import Flapjack.Compiler.Backend.GenGcPartial.Proofs.Accumulator
import Flapjack.Compiler.Backend.GcShared.ForwardPtr

/-! Success and accumulator laws for partial collection. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend

/-- A successful partial root move started from a successful state. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_partial_move_ok_before"]
theorem partialMove_okBefore {α β : Type} (conf : GenGcPartial.Config β)
    (state state1 : GcState α β) (root root1 : HeapAddress α)
    (run : GenGcPartial.gcMove conf state root = (root1, state1))
    (ok : state1.ok = true) : state.ok = true := by
  cases root with
  | data value =>
    simp only [GenGcPartial.gcMove, Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    exact ok
  | pointer ptr value =>
    by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
    · simp [GenGcPartial.gcMove, outside, Prod.mk.injEq] at run
      obtain ⟨_, rfl⟩ := run
      simp only [Bool.and_eq_true] at ok
      exact ok.1
    · cases found : heapLookup ptr state.heap with
      | none => simp [GenGcPartial.gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; simp at ok
      | some element =>
        cases element with
        | unused len => simp [GenGcPartial.gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; simp at ok
        | forwardPointer dest old len =>
          simp [GenGcPartial.gcMove, outside, found, Prod.mk.injEq] at run
          obtain ⟨_, rfl⟩ := run
          exact ok
        | dataElement xs len payload =>
          cases forward : gcForwardPtr ptr state.heap state.a value
              ((state.ok && decide (ptr < heapLength state.heap)) && decide (len + 1 ≤ state.n) && !(conf.isRef payload)) with
          | mk newHeap status =>
            simp only [GenGcPartial.gcMove, outside, ↓reduceIte, found, forward, Prod.mk.injEq] at run
            obtain ⟨_, rfl⟩ := run
            have statusTrue : status = true := ok
            subst status
            have check := gcForwardPtr_ok state.heap ptr state.a value
              ((state.ok && decide (ptr < heapLength state.heap)) && decide (len + 1 ≤ state.n) && !(conf.isRef payload)) newHeap forward
            simp only [Bool.and_eq_true] at check
            exact check.1.1.1

/-- A successful partial root traversal started from a successful state. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_partial_move_list_ok_before"]
theorem partialMoveList_okBefore {α β : Type} (conf : GenGcPartial.Config β)
    (roots : List (HeapAddress α)) (state : GcState α β) (roots1 : List (HeapAddress α)) (state1 : GcState α β)
    (run : GenGcPartial.gcMoveList conf state roots = (roots1, state1))
    (ok : state1.ok = true) : state.ok = true := by
  induction roots generalizing state state1 roots1 with
  | nil =>
    simp only [GenGcPartial.gcMoveList, Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    exact ok
  | cons root roots ih =>
    simp only [GenGcPartial.gcMoveList] at run
    generalize headRun : GenGcPartial.gcMove conf state root = result at run
    obtain ⟨rootMid, middle⟩ := result
    generalize tailRun : GenGcPartial.gcMoveList conf middle roots = result at run
    obtain ⟨tail, final⟩ := result
    simp only [Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    exact partialMove_okBefore conf state middle root rootMid headRun
      (ih (state := middle) (state1 := final) (roots1 := tail) tailRun ok)

/-- A successful root move factors through empty accumulators. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_partial_move_with_NIL"]
theorem partialMove_withNil {α β : Type} (conf : GenGcPartial.Config β) (root : HeapAddress α)
    (state : GcState α β) (output : HeapAddress α) (result : GcState α β)
    (run : GenGcPartial.gcMove conf state root = (output, result))
    (_ok : result.ok = true) :
    (let (out, state1) := GenGcPartial.gcMove conf { state with h2 := [], r4 := [] } root
     (out, { state1 with h2 := state.h2 ++ state1.h2, r4 := state1.r4 ++ state.r4 })) = (output, result) := by
  have h := GenGcPartial.gcMove_accumulate conf { state with h2 := [], r4 := [] } root state.h2 state.r4
  simp only [List.append_nil, List.nil_append] at h
  cases state
  exact h.symm.trans run

/-- A successful root traversal factors through empty accumulators. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_partial_move_list_with_NIL"]
theorem partialMoveList_withNil {α β : Type} (conf : GenGcPartial.Config β) (roots : List (HeapAddress α))
    (state : GcState α β) (output : List (HeapAddress α)) (result : GcState α β)
    (run : GenGcPartial.gcMoveList conf state roots = (output, result))
    (_ok : result.ok = true) :
    (let (out, state1) := GenGcPartial.gcMoveList conf { state with h2 := [], r4 := [] } roots
     (out, { state1 with h2 := state.h2 ++ state1.h2, r4 := state1.r4 ++ state.r4 })) = (output, result) := by
  have h := GenGcPartial.gcMoveList_accumulate conf { state with h2 := [], r4 := [] } roots state.h2 state.r4
  simp only [List.append_nil, List.nil_append] at h
  cases state
  exact h.symm.trans run

/-- A successful traversal separates the newly accumulated heap fragments. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_partial_move_list_with_NIL_LEMMA"]
theorem partialMoveList_withNilLemma {α β : Type} (conf : GenGcPartial.Config β)
    (roots : List (HeapAddress α)) (state : GcState α β) (output : List (HeapAddress α))
    (result : GcState α β) (run : GenGcPartial.gcMoveList conf state roots = (output, result))
    (ok : result.ok = true) :
    ∃ left right,
      result.h2 = state.h2 ++ left ∧ result.r4 = right ++ state.r4 ∧
      GenGcPartial.gcMoveList conf { state with h2 := [], r4 := [] } roots =
        (output, { result with h2 := left, r4 := right }) := by
  have factored := partialMoveList_withNil conf roots state output result run ok
  cases clearRun : GenGcPartial.gcMoveList conf { state with h2 := [], r4 := [] } roots with
  | mk moved newState =>
    simp only [clearRun, Prod.mk.injEq] at factored
    obtain ⟨rfl, rfl⟩ := factored
    refine ⟨newState.h2, newState.r4, rfl, rfl, ?_⟩
    cases newState
    rfl

/-- A successful partial data scan started from a successful state. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_partial_move_data_ok_before"]
theorem partialMoveData_okBefore {α β : Type} (conf : GenGcPartial.Config β) (state state1 : GcState α β)
    (run : GenGcPartial.gcMoveData conf state = state1) (ok : state1.ok = true) : state.ok = true := by
  classical
  subst state1
  induction state using GenGcPartial.gcMoveData.induct conf with
  | case1 state empty => rw [GenGcPartial.gcMoveData] at ok; simpa [empty] using ok
  | case2 state head tail heap over => rw [GenGcPartial.gcMoveData] at ok; simp [heap, over] at ok
  | case3 state tail roots len payload roots1 middle move heap bounded flag ih =>
    cases state with
    | mk old h1 h2 r4 r3 r2 r1 a n status origHeap heap0 =>
      simp only at heap
      subst h2
      rw [GenGcPartial.gcMoveData] at ok
      simp only [bounded, ↓reduceIte, move] at ok
      have check := ih ok
      dsimp only [flag] at check
      simp only [Bool.and_eq_true] at check
      exact partialMoveList_okBefore conf roots _ roots1 middle move check.1.1
  | case4 state head tail heap bounded notData =>
    cases head with
    | unused len => rw [GenGcPartial.gcMoveData] at ok; simp [heap, bounded] at ok
    | forwardPointer ptr value len => rw [GenGcPartial.gcMoveData] at ok; simp [heap, bounded] at ok
    | dataElement roots len payload => exact False.elim (notData roots len payload rfl)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
