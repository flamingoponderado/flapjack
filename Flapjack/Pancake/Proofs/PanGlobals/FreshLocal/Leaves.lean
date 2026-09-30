import Flapjack.Pancake.Proofs.PanGlobals

/-! Genuine leaf cases of `evaluate_fresh_local` (pan_globalsProofScript:1045).
The original existential post-locals and conditional update are retained.
These constructors have no recursive evaluation induction hypotheses. -/

namespace Flapjack.PanGlobalsFreshLocal

open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Canonical finite state roundtrip for the representation qualifier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Flapjack-specific proof factoring for state-preserving leaves. Its evaluator
equation is discharged by the actual constructor equation in each case. -/
private theorem unchangedLeaf {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (result : Option (PanSemResultExact width))
    (equation : ∀ state : PanSemStateFiniteExact width σ,
      evaluateHOLFiniteState state program = (result, state))
    (name : MlS) (value : ValueHOL width) (state post : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width))
    (h : ¬ name ∈ freeVarIdsHOL program ∧ evaluateHOLFiniteState state program = (res, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)} program =
        (res, {post with locals := locals}) ∧
      (goodResHOL res = true ∧ res ≠ some .error →
        locals = post.locals.updateEq (name, value)) := by
  rw [equation] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h.2
  exact ⟨state.locals.updateEq (name, value), equation _, fun _ => rfl⟩

/-- `Skip` induction case of the original fresh-local evaluation theorem. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_Skip {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : ¬ name ∈ freeVarIdsHOL (.skip : ProgHOL width) ∧
      evaluateHOLFiniteState state .skip = (res, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)} .skip =
        (res, {post with locals := locals}) ∧
      (goodResHOL res = true ∧ res ≠ some .error →
        locals = post.locals.updateEq (name, value)) :=
  unchangedLeaf .skip none evaluateHOLFiniteState_skip name value state post res h

/-- `Break` induction case of the original fresh-local evaluation theorem. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_Break {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : ¬ name ∈ freeVarIdsHOL (.break : ProgHOL width) ∧
      evaluateHOLFiniteState state .break = (res, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)} .break =
        (res, {post with locals := locals}) ∧
      (goodResHOL res = true ∧ res ≠ some .error →
        locals = post.locals.updateEq (name, value)) :=
  unchangedLeaf .break (some .break) evaluateHOLFiniteState_break name value state post res h

/-- `Continue` induction case of the original fresh-local evaluation theorem. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_Continue {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : ¬ name ∈ freeVarIdsHOL (.continue : ProgHOL width) ∧
      evaluateHOLFiniteState state .continue = (res, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)} .continue =
        (res, {post with locals := locals}) ∧
      (goodResHOL res = true ∧ res ≠ some .error →
        locals = post.locals.updateEq (name, value)) :=
  unchangedLeaf .continue (some .continue) evaluateHOLFiniteState_continue name value state post res h

/-- `Annot` induction case of the original fresh-local evaluation theorem. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_Annot {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (tag text : MlS)
    (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : ¬ name ∈ freeVarIdsHOL (.annot tag text : ProgHOL width) ∧
      evaluateHOLFiniteState state (.annot tag text) = (res, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)} (.annot tag text) =
        (res, {post with locals := locals}) ∧
      (goodResHOL res = true ∧ res ≠ some .error →
        locals = post.locals.updateEq (name, value)) :=
  unchangedLeaf (.annot tag text) none (fun s => evaluateHOLFiniteState_annot s tag text)
    name value state post res h

/-- `Tick` induction case: timeout clears locals; a successful tick preserves
the fresh update while decrementing the original clock. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFreshLocal_Tick {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (h : ¬ name ∈ freeVarIdsHOL (.tick : ProgHOL width) ∧
      evaluateHOLFiniteState state .tick = (res, post)) :
    ∃ locals,
      evaluateHOLFiniteState {state with locals := state.locals.updateEq (name, value)} .tick =
        (res, {post with locals := locals}) ∧
      (goodResHOL res = true ∧ res ≠ some .error →
        locals = post.locals.updateEq (name, value)) := by
  have hev := h.2
  rw [evaluateHOLFiniteState_tick] at hev
  by_cases hz : state.clock = 0
  · rw [if_pos hz] at hev
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
    refine ⟨HolFiniteMapExact.empty, ?_, ?_⟩
    · rw [evaluateHOLFiniteState_tick, if_pos hz]
      rfl
    · simp [goodResHOL]
  · rw [if_neg hz] at hev
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
    refine ⟨state.locals.updateEq (name, value), ?_, fun _ => rfl⟩
    rw [evaluateHOLFiniteState_tick, if_neg hz]
    rfl

end Flapjack.PanGlobalsFreshLocal
