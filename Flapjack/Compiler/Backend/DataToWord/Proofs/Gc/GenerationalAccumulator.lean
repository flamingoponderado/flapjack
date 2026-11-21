module

public import Flapjack.Compiler.Backend.GenGc.Proofs.Accumulator

@[expose] public section

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

/-- Moving a root from any accumulators factors through empty accumulators.
Flapjack proof infrastructure derived from `GenGc.gcMove_accumulate`; no HOL
counterpart. -/
private theorem gcMove_anyAccumulators {α β : Type} (conf : GenGc.Config β)
    (s : GcState α β) (x : HeapAddress α) (left right : List (HeapElement α β)) :
    GenGc.gcMove conf { s with h2 := left, r4 := right } x =
      let (y0, t0) := GenGc.gcMove conf { s with h2 := [], r4 := [] } x
      (y0, { t0 with h2 := left ++ t0.h2, r4 := t0.r4 ++ right }) := by
  have h := GenGc.gcMove_accumulate conf { s with h2 := [], r4 := [] } x left right
  simp only [List.append_nil, List.nil_append] at h
  exact h

/-- Moving a root list from any accumulators factors through empty
accumulators. Flapjack proof infrastructure; no HOL counterpart. -/
private theorem gcMoveList_anyAccumulators {α β : Type} (conf : GenGc.Config β)
    (s : GcState α β) (x : List (HeapAddress α)) (left right : List (HeapElement α β)) :
    GenGc.gcMoveList conf { s with h2 := left, r4 := right } x =
      let (y0, t0) := GenGc.gcMoveList conf { s with h2 := [], r4 := [] } x
      (y0, { t0 with h2 := left ++ t0.h2, r4 := t0.r4 ++ right }) := by
  have h := GenGc.gcMoveList_accumulate conf { s with h2 := [], r4 := [] } x left right
  simp only [List.append_nil, List.nil_append] at h
  exact h

/-- Exact HOL `gc_move_with_NIL_LEMMA` (`data_to_word_gcProofScript.sml:1435-1452`).
The typed capture shows four unused universally quantified binders `y t h2 r4`
of independent types; they are retained. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_move_with_NIL_LEMMA"]
theorem gcMove_withNilLemma {α β γ δ ε ζ : Type} {conf : GenGc.Config β} :
    ∀ (x : HeapAddress α) (s : GcState α β) (_y : γ) (_t : δ) (_h2 : ε) (_r4 : ζ)
      (y1 : HeapAddress α) (t1 : GcState α β),
      GenGc.gcMove conf s x = (y1, t1) ∧ t1.ok = true →
        ∃ x1 x2 : List (HeapElement α β),
          t1.h2 = s.h2 ++ x1 ∧ t1.r4 = x2 ++ s.r4 ∧
          GenGc.gcMove conf { s with h2 := [], r4 := [] } x =
            (y1, { t1 with h2 := x1, r4 := x2 }) := by
  intro x s _ _ _ _ y1 t1 ⟨run, _⟩
  have h := gcMove_anyAccumulators conf s x s.h2 s.r4
  have hs : ({ s with h2 := s.h2, r4 := s.r4 } : GcState α β) = s := rfl
  rw [hs, run] at h
  generalize GenGc.gcMove conf { s with h2 := [], r4 := [] } x = m at h ⊢
  obtain ⟨y0, t0⟩ := m
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨t0.h2, t0.r4, rfl, rfl, rfl⟩

/-- Exact HOL `gc_move_list_ok_irr0` (`data_to_word_gcProofScript.sml:1454-1464`,
a `[local]` theorem about a single move). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_move_list_ok_irr0"]
theorem gcMove_okIrr0 {α β : Type} {conf : GenGc.Config β} :
    ∀ (x : HeapAddress α) (s : GcState α β) (y1 y2 : HeapAddress α) (t1 t2 : GcState α β)
      (h2 r4 : List (HeapElement α β)),
      GenGc.gcMove conf s x = (y1, t1) ∧
          GenGc.gcMove conf { s with h2 := h2, r4 := r4 } x = (y2, t2) →
        y1 = y2 ∧ ∃ x1 x2 : List (HeapElement α β), t2 = { t1 with h2 := x1, r4 := x2 } := by
  intro x s y1 y2 t1 t2 h2 r4 ⟨run1, run2⟩
  have e1 := gcMove_anyAccumulators conf s x s.h2 s.r4
  have e2 := gcMove_anyAccumulators conf s x h2 r4
  have hs : ({ s with h2 := s.h2, r4 := s.r4 } : GcState α β) = s := rfl
  rw [hs, run1] at e1
  rw [run2] at e2
  generalize GenGc.gcMove conf { s with h2 := [], r4 := [] } x = m at e1 e2
  obtain ⟨y0, t0⟩ := m
  simp only [Prod.mk.injEq] at e1 e2
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨rfl, rfl⟩ := e2
  exact ⟨rfl, h2 ++ t0.h2, t0.r4 ++ r4, rfl⟩

/-- Exact HOL `gc_move_list_ok_irr` (`data_to_word_gcProofScript.sml:1466-1481`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_move_list_ok_irr"]
theorem gcMoveList_okIrr {α β : Type} {conf : GenGc.Config β} :
    ∀ (x : List (HeapAddress α)) (s : GcState α β) (y1 y2 : List (HeapAddress α))
      (t1 t2 : GcState α β) (h2 r4 : List (HeapElement α β)),
      GenGc.gcMoveList conf s x = (y1, t1) ∧ t1.ok = true ∧
          GenGc.gcMoveList conf { s with h2 := h2, r4 := r4 } x = (y2, t2) →
        t2.ok = true := by
  intro x s y1 y2 t1 t2 h2 r4 ⟨run1, ok, run2⟩
  have e1 := gcMoveList_anyAccumulators conf s x s.h2 s.r4
  have e2 := gcMoveList_anyAccumulators conf s x h2 r4
  have hs : ({ s with h2 := s.h2, r4 := s.r4 } : GcState α β) = s := rfl
  rw [hs, run1] at e1
  rw [run2] at e2
  generalize GenGc.gcMoveList conf { s with h2 := [], r4 := [] } x = m at e1 e2
  obtain ⟨y0, t0⟩ := m
  simp only [Prod.mk.injEq] at e1 e2
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨rfl, rfl⟩ := e2
  exact ok

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
