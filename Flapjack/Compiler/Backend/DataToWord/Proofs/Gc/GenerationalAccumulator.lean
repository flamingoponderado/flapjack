import Flapjack.Compiler.Backend.GenGc.Proofs.Accumulator

/-! Source accumulator lemmas for the major collector. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend

/-- Moving a successful root can be factored through empty accumulators. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_move_with_NIL"]
theorem gcMove_withNil {α β : Type} (conf : GenGc.Config β) (root output : HeapAddress α)
    (state result : GcState α β) (run : GenGc.gcMove conf state root = (output, result))
    (_ok : result.ok = true) :
    (let (out, state1) := GenGc.gcMove conf { state with h2 := [], r4 := [] } root
     (out, { state1 with h2 := state.h2 ++ state1.h2, r4 := state1.r4 ++ state.r4 })) = (output, result) := by
  have h := GenGc.gcMove_accumulate conf { state with h2 := [], r4 := [] } root state.h2 state.r4
  simp only [List.append_nil, List.nil_append] at h
  cases state
  exact h.symm.trans run

/-- The successful root-list traversal factors through empty accumulators. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_move_list_with_NIL"]
theorem gcMoveList_withNil {α β : Type} (conf : GenGc.Config β) (roots output : List (HeapAddress α))
    (state result : GcState α β) (run : GenGc.gcMoveList conf state roots = (output, result))
    (_ok : result.ok = true) :
    (let (out, state1) := GenGc.gcMoveList conf { state with h2 := [], r4 := [] } roots
     (out, { state1 with h2 := state.h2 ++ state1.h2, r4 := state1.r4 ++ state.r4 })) = (output, result) := by
  have h := GenGc.gcMoveList_accumulate conf { state with h2 := [], r4 := [] } roots state.h2 state.r4
  simp only [List.append_nil, List.nil_append] at h
  cases state
  exact h.symm.trans run

/-- A successful root-list traversal splits off the newly accumulated heaps. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_move_list_with_NIL_LEMMA"]
theorem gcMoveList_withNilLemma {α β : Type} (conf : GenGc.Config β) (roots output : List (HeapAddress α))
    (state result : GcState α β) (run : GenGc.gcMoveList conf state roots = (output, result))
    (ok : result.ok = true) :
    ∃ left right,
      result.h2 = state.h2 ++ left ∧ result.r4 = right ++ state.r4 ∧
      GenGc.gcMoveList conf { state with h2 := [], r4 := [] } roots =
        (output, { result with h2 := left, r4 := right }) := by
  have factored := gcMoveList_withNil conf roots output state result run ok
  cases clearRun : GenGc.gcMoveList conf { state with h2 := [], r4 := [] } roots with
  | mk moved newState =>
    simp only [clearRun, Prod.mk.injEq] at factored
    obtain ⟨rfl, rfl⟩ := factored
    refine ⟨newState.h2, newState.r4, rfl, rfl, ?_⟩
    cases newState
    rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
