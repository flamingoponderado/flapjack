module

public import Flapjack.Compiler.Backend.GenGcPartial.Proofs.Accumulator
public import Flapjack.Compiler.Backend.GcShared.ForwardPtr
public import Flapjack.Compiler.Backend.GenGcPartial.Proofs.Similarity

@[expose] public section

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

/-- A successful reference-list traversal started from a successful state. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_partial_move_ref_list_ok_before"]
theorem partialMoveRefList_okBefore {α β γ : Type} (conf : GenGcPartial.Config γ)
    (refs : List (HeapElement α β)) (state : GcState α γ)
    (refs1 : List (HeapElement α β)) (state1 : GcState α γ)
    (run : GenGcPartial.gcMoveRefList conf state refs = (refs1, state1))
    (ok : state1.ok = true) : state.ok = true := by
  induction refs generalizing state state1 refs1 with
  | nil =>
    simp only [GenGcPartial.gcMoveRefList, Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    exact ok
  | cons head refs ih =>
    cases head with
    | unused len => simp [GenGcPartial.gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; simp at ok
    | forwardPointer ptr value len => simp [GenGcPartial.gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; simp at ok
    | dataElement roots len payload =>
      simp only [GenGcPartial.gcMoveRefList] at run
      generalize headRun : GenGcPartial.gcMoveList conf state roots = result at run
      obtain ⟨rootsMid, middle⟩ := result
      generalize tailRun : GenGcPartial.gcMoveRefList conf middle refs = result at run
      obtain ⟨tail, final⟩ := result
      simp only [Prod.mk.injEq] at run
      obtain ⟨_, rfl⟩ := run
      exact partialMoveList_okBefore conf roots state rootsMid middle headRun
        (ih (state := middle) (state1 := final) (refs1 := tail) tailRun ok)

/-- A successful reference-list traversal factors through empty accumulators. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_partial_move_ref_list_with_NIL"]
theorem partialMoveRefList_withNil {α β γ : Type} (conf : GenGcPartial.Config γ)
    (refs : List (HeapElement α β)) (state : GcState α γ) (output : List (HeapElement α β))
    (result : GcState α γ) (run : GenGcPartial.gcMoveRefList conf state refs = (output, result))
    (_ok : result.ok = true) :
    (let (out, state1) := GenGcPartial.gcMoveRefList conf { state with h2 := [], r4 := [] } refs
     (out, { state1 with h2 := state.h2 ++ state1.h2, r4 := state1.r4 ++ state.r4 })) = (output, result) := by
  have h := GenGcPartial.gcMoveRefList_accumulate conf { state with h2 := [], r4 := [] } refs state.h2 state.r4
  simp only [List.append_nil, List.nil_append] at h
  cases state
  exact h.symm.trans run

/-- A successful reference-list traversal separates its newly accumulated heap. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_partial_move_ref_list_with_NIL_LEMMA"]
theorem partialMoveRefList_withNilLemma {α β γ : Type} (conf : GenGcPartial.Config γ)
    (refs : List (HeapElement α β)) (state : GcState α γ) (output : List (HeapElement α β))
    (result : GcState α γ) (run : GenGcPartial.gcMoveRefList conf state refs = (output, result))
    (ok : result.ok = true) :
    ∃ left right,
      result.h2 = state.h2 ++ left ∧ result.r4 = right ++ state.r4 ∧
      GenGcPartial.gcMoveRefList conf { state with h2 := [], r4 := [] } refs =
        (output, { result with h2 := left, r4 := right }) := by
  have factored := partialMoveRefList_withNil conf refs state output result run ok
  cases clearRun : GenGcPartial.gcMoveRefList conf { state with h2 := [], r4 := [] } refs with
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

/-- Moving a root from any accumulators factors through empty accumulators.
Flapjack proof infrastructure derived from `GenGcPartial.gcMove_accumulate`; no HOL
counterpart. -/
private theorem partialMove_anyAccumulators {α β : Type} (conf : GenGcPartial.Config β)
    (s : GcState α β) (x : HeapAddress α) (left right : List (HeapElement α β)) :
    GenGcPartial.gcMove conf { s with h2 := left, r4 := right } x =
      let (y0, t0) := GenGcPartial.gcMove conf { s with h2 := [], r4 := [] } x
      (y0, { t0 with h2 := left ++ t0.h2, r4 := t0.r4 ++ right }) := by
  have h := GenGcPartial.gcMove_accumulate conf { s with h2 := [], r4 := [] } x left right
  simp only [List.append_nil, List.nil_append] at h
  exact h

/-- Moving a root list from any accumulators factors through empty
accumulators. Flapjack proof infrastructure; no HOL counterpart. -/
private theorem partialMoveList_anyAccumulators {α β : Type} (conf : GenGcPartial.Config β)
    (s : GcState α β) (x : List (HeapAddress α)) (left right : List (HeapElement α β)) :
    GenGcPartial.gcMoveList conf { s with h2 := left, r4 := right } x =
      let (y0, t0) := GenGcPartial.gcMoveList conf { s with h2 := [], r4 := [] } x
      (y0, { t0 with h2 := left ++ t0.h2, r4 := t0.r4 ++ right }) := by
  have h := GenGcPartial.gcMoveList_accumulate conf { s with h2 := [], r4 := [] } x left right
  simp only [List.append_nil, List.nil_append] at h
  exact h

/-- Exact HOL `gc_partial_move_with_NIL_LEMMA` (`data_to_word_gcProofScript.sml:2917-2933`).
The typed capture shows four unused universally quantified binders `y t h2 r4`
of independent types; they are retained. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_partial_move_with_NIL_LEMMA"]
theorem partialMove_withNilLemma {α β γ δ ε ζ : Type} {conf : GenGcPartial.Config β} :
    ∀ (x : HeapAddress α) (s : GcState α β) (_y : γ) (_t : δ) (_h2 : ε) (_r4 : ζ)
      (y1 : HeapAddress α) (t1 : GcState α β),
      GenGcPartial.gcMove conf s x = (y1, t1) ∧ t1.ok = true →
        ∃ x1 x2 : List (HeapElement α β),
          t1.h2 = s.h2 ++ x1 ∧ t1.r4 = x2 ++ s.r4 ∧
          GenGcPartial.gcMove conf { s with h2 := [], r4 := [] } x =
            (y1, { t1 with h2 := x1, r4 := x2 }) := by
  intro x s _ _ _ _ y1 t1 ⟨run, _⟩
  have h := partialMove_anyAccumulators conf s x s.h2 s.r4
  have hs : ({ s with h2 := s.h2, r4 := s.r4 } : GcState α β) = s := rfl
  rw [hs, run] at h
  generalize GenGcPartial.gcMove conf { s with h2 := [], r4 := [] } x = m at h ⊢
  obtain ⟨y0, t0⟩ := m
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨t0.h2, t0.r4, rfl, rfl, rfl⟩

/-- Exact HOL `gc_partial_move_ok_irr` (`data_to_word_gcProofScript.sml:2780-2790`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_partial_move_ok_irr"]
theorem partialMove_okIrr {α β : Type} {conf : GenGcPartial.Config β} :
    ∀ (x : HeapAddress α) (s : GcState α β) (y1 y2 : HeapAddress α) (t1 t2 : GcState α β)
      (h2 r4 : List (HeapElement α β)),
      GenGcPartial.gcMove conf s x = (y1, t1) ∧
          GenGcPartial.gcMove conf { s with h2 := h2, r4 := r4 } x = (y2, t2) →
        y1 = y2 ∧ ∃ x1 x2 : List (HeapElement α β), t2 = { t1 with h2 := x1, r4 := x2 } := by
  intro x s y1 y2 t1 t2 h2 r4 ⟨run1, run2⟩
  have e1 := partialMove_anyAccumulators conf s x s.h2 s.r4
  have e2 := partialMove_anyAccumulators conf s x h2 r4
  have hs : ({ s with h2 := s.h2, r4 := s.r4 } : GcState α β) = s := rfl
  rw [hs, run1] at e1
  rw [run2] at e2
  generalize GenGcPartial.gcMove conf { s with h2 := [], r4 := [] } x = m at e1 e2
  obtain ⟨y0, t0⟩ := m
  simp only [Prod.mk.injEq] at e1 e2
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨rfl, rfl⟩ := e2
  exact ⟨rfl, h2 ++ t0.h2, t0.r4 ++ r4, rfl⟩

/-- Exact HOL `gc_partial_move_list_ok_irr` (`data_to_word_gcProofScript.sml:2835-2859`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_partial_move_list_ok_irr"]
theorem partialMoveList_okIrr {α β : Type} {conf : GenGcPartial.Config β} :
    ∀ (x : List (HeapAddress α)) (s : GcState α β) (y1 y2 : List (HeapAddress α))
      (t1 t2 : GcState α β) (h2 r4 : List (HeapElement α β)),
      GenGcPartial.gcMoveList conf s x = (y1, t1) ∧ t1.ok = true ∧
          GenGcPartial.gcMoveList conf { s with h2 := h2, r4 := r4 } x = (y2, t2) →
        t2.ok = true := by
  intro x s y1 y2 t1 t2 h2 r4 ⟨run1, ok, run2⟩
  have e1 := partialMoveList_anyAccumulators conf s x s.h2 s.r4
  have e2 := partialMoveList_anyAccumulators conf s x h2 r4
  have hs : ({ s with h2 := s.h2, r4 := s.r4 } : GcState α β) = s := rfl
  rw [hs, run1] at e1
  rw [run2] at e2
  generalize GenGcPartial.gcMoveList conf { s with h2 := [], r4 := [] } x = m at e1 e2
  obtain ⟨y0, t0⟩ := m
  simp only [Prod.mk.injEq] at e1 e2
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨rfl, rfl⟩ := e2
  exact ok

/-- Exact HOL `gc_partial_move_list_ok_irr'` (`data_to_word_gcProofScript.sml:2861-2873`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_partial_move_list_ok_irr'"]
theorem partialMoveList_okIrr' {α β : Type} {conf : GenGcPartial.Config β} :
    ∀ (x : List (HeapAddress α)) (s : GcState α β) (y1 y2 : List (HeapAddress α))
      (t1 t2 : GcState α β) (h2 r4 : List (HeapElement α β)),
      GenGcPartial.gcMoveList conf s x = (y1, t1) ∧
          GenGcPartial.gcMoveList conf { s with h2 := h2, r4 := r4 } x = (y2, t2) →
        y1 = y2 ∧ ∃ x1 x2 : List (HeapElement α β), t2 = { t1 with h2 := x1, r4 := x2 } := by
  intro x s y1 y2 t1 t2 h2 r4 ⟨run1, run2⟩
  have e1 := partialMoveList_anyAccumulators conf s x s.h2 s.r4
  have e2 := partialMoveList_anyAccumulators conf s x h2 r4
  have hs : ({ s with h2 := s.h2, r4 := s.r4 } : GcState α β) = s := rfl
  rw [hs, run1] at e1
  rw [run2] at e2
  generalize GenGcPartial.gcMoveList conf { s with h2 := [], r4 := [] } x = m at e1 e2
  obtain ⟨y0, t0⟩ := m
  simp only [Prod.mk.injEq] at e1 e2
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨rfl, rfl⟩ := e2
  exact ⟨rfl, h2 ++ t0.h2, t0.r4 ++ r4, rfl⟩

/-- Exact HOL `gc_partial_move_ref_list_ok_irr` (`data_to_word_gcProofScript.sml:2875-2900`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_partial_move_ref_list_ok_irr"]
theorem partialMoveRefList_okIrr {α β γ : Type} {conf : GenGcPartial.Config γ} :
    ∀ (x : List (HeapElement α β)) (s : GcState α γ) (y1 y2 : List (HeapElement α β))
      (t1 t2 : GcState α γ) (h2 r4 : List (HeapElement α γ)),
      GenGcPartial.gcMoveRefList conf s x = (y1, t1) ∧ t1.ok = true ∧
          GenGcPartial.gcMoveRefList conf { s with h2 := h2, r4 := r4 } x = (y2, t2) →
        t2.ok = true := by
  intro x s y1 y2 t1 t2 h2 r4 ⟨run1, ok, run2⟩
  have e1 := GenGcPartial.gcMoveRefList_accumulate conf { s with h2 := [], r4 := [] } x s.h2 s.r4
  have e2 := GenGcPartial.gcMoveRefList_accumulate conf { s with h2 := [], r4 := [] } x h2 r4
  simp only [List.append_nil, List.nil_append] at e1 e2
  have hs : ({ s with h2 := s.h2, r4 := s.r4 } : GcState α γ) = s := rfl
  rw [hs, run1] at e1
  rw [run2] at e2
  generalize GenGcPartial.gcMoveRefList conf { s with h2 := [], r4 := [] } x = m at e1 e2
  obtain ⟨y0, t0⟩ := m
  simp only [Prod.mk.injEq] at e1 e2
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨rfl, rfl⟩ := e2
  exact ok

/-- A partial root move only changes the `h2`, `n`, `a`, `heap` and `ok`
fields. Flapjack proof infrastructure; no HOL counterpart. -/
private theorem partialMove_frame {α β : Type} (conf : GenGcPartial.Config β)
    (s : GcState α β) (x : HeapAddress α) :
    (GenGcPartial.gcMove conf s x).2.old = s.old ∧ (GenGcPartial.gcMove conf s x).2.h1 = s.h1 ∧
      (GenGcPartial.gcMove conf s x).2.r1 = s.r1 ∧ (GenGcPartial.gcMove conf s x).2.r2 = s.r2 ∧
      (GenGcPartial.gcMove conf s x).2.r3 = s.r3 ∧ (GenGcPartial.gcMove conf s x).2.r4 = s.r4 := by
  cases x with
  | data d => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | pointer ptr d =>
    by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
    · simp [GenGcPartial.gcMove, outside]
    · cases h : heapLookup ptr s.heap with
      | none => simp [GenGcPartial.gcMove, outside, h]
      | some element => cases element <;> simp [GenGcPartial.gcMove, outside, h]

/-- The partial root-list traversal preserves the same fields. Flapjack proof
infrastructure; no HOL counterpart. -/
private theorem partialMoveList_frame {α β : Type} (conf : GenGcPartial.Config β)
    (s : GcState α β) (xs : List (HeapAddress α)) :
    (GenGcPartial.gcMoveList conf s xs).2.old = s.old ∧
      (GenGcPartial.gcMoveList conf s xs).2.h1 = s.h1 ∧
      (GenGcPartial.gcMoveList conf s xs).2.r1 = s.r1 ∧
      (GenGcPartial.gcMoveList conf s xs).2.r2 = s.r2 ∧
      (GenGcPartial.gcMoveList conf s xs).2.r3 = s.r3 ∧
      (GenGcPartial.gcMoveList conf s xs).2.r4 = s.r4 := by
  induction xs generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons x xs ih =>
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := partialMove_frame conf s x
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := ih (GenGcPartial.gcMove conf s x).2
    simp only [GenGcPartial.gcMoveList]
    exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6⟩

/-- Lookups in similar heaps find data elements at the same offsets. Flapjack
proof infrastructure; no HOL counterpart. -/
private theorem similar_isSomeDataElement {α β σ : Type} (conf : σ)
    (xs ys : List (HeapElement α β)) (related : List.Forall₂ (GenGcPartial.similarData conf) xs ys) :
    ∀ ptr, isSomeDataElement (heapLookup ptr xs) → isSomeDataElement (heapLookup ptr ys) := by
  induction related with
  | nil => intro ptr h; exact h
  | @cons x y xs ys head tail ih =>
    intro ptr h
    have hlen : elLength x = elLength y := by
      cases x <;> cases y <;> simp_all [GenGcPartial.similarData, elLength]
    simp only [heapLookup, hlen] at h ⊢
    by_cases h0 : ptr = 0
    · simp only [h0, if_true] at h ⊢
      obtain ⟨xs1, len, data, hx⟩ := h
      cases hx
      cases y <;> simp_all [GenGcPartial.similarData, isSomeDataElement]
    · simp only [h0, if_false] at h ⊢
      by_cases hl : ptr < elLength y
      · simp only [hl, if_true] at h
        obtain ⟨_, _, _, h⟩ := h
        cases h
      · simp only [hl, if_false] at h ⊢
        exact ih _ h

/-- Exact HOL `gc_move_ref_list_IMP` (`data_to_word_gcProofScript.sml:3496-3527`,
a `[local]` theorem about the partial collector's reference traversal). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_move_ref_list_IMP"]
theorem partialMoveRefList_imp {α β γ : Type} :
    ∀ (conf : GenGcPartial.Config α) (state : GcState β α) (refs : List (HeapElement β γ))
      (state1 : GcState β α) (refs1 : List (HeapElement β γ)),
      GenGcPartial.gcMoveRefList conf state refs = (refs1, state1) →
        state1.old = state.old ∧ state1.h1 = state.h1 ∧ state1.r1 = state.r1 ∧
          state1.r2 = state.r2 ∧ state1.r3 = state.r3 ∧ state1.r4 = state.r4 ∧
          heapLength refs = heapLength refs1 ∧
          ∀ ptr, isSomeDataElement (heapLookup ptr refs) →
            isSomeDataElement (heapLookup ptr refs1) := by
  intro conf state refs state1 refs1 run
  have similar := GenGcPartial.gcMoveRefList_similar conf refs refs1 state state1 run
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, (GenGcPartial.similarData_lengths conf refs refs1 similar).1,
    similar_isSomeDataElement conf refs refs1 similar⟩ <;>
  · clear similar
    induction refs generalizing state refs1 state1 with
    | nil =>
      simp only [GenGcPartial.gcMoveRefList, Prod.mk.injEq] at run
      obtain ⟨_, rfl⟩ := run
      rfl
    | cons head tail ih =>
      cases head with
      | unused len =>
        simp only [GenGcPartial.gcMoveRefList, Prod.mk.injEq] at run
        obtain ⟨_, rfl⟩ := run
        rfl
      | forwardPointer ptr value len =>
        simp only [GenGcPartial.gcMoveRefList, Prod.mk.injEq] at run
        obtain ⟨_, rfl⟩ := run
        rfl
      | dataElement pointers len payload =>
        simp only [GenGcPartial.gcMoveRefList] at run
        generalize hl : GenGcPartial.gcMoveList conf state pointers = r1 at run
        obtain ⟨pointers1, mid⟩ := r1
        generalize hr : GenGcPartial.gcMoveRefList conf mid tail = r2 at run
        obtain ⟨tail1, fin⟩ := r2
        simp only [Prod.mk.injEq] at run
        obtain ⟨_, rfl⟩ := run
        have fr := partialMoveList_frame conf state pointers
        rw [hl] at fr
        have := ih mid fin tail1 hr
        simp_all

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
