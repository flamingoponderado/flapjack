module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveAlloc

@[expose] public section

/-! Thunk operations in the generic closure primitive simulation. -/
namespace Flapjack.Compiler.Backend.ClosProps.PrimitiveThunk
open ClosSem Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.ClosProps.PrimitiveMemory
open Flapjack.Compiler.Backend.ClosProps.PrimitiveAlloc

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Related values and stores agree on the validity of a thunk update. This
is Flapjack proof infrastructure. -/
theorem badThunkUpdateRelated {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValRel vr) (stateProps : simpleStateRel vr sr)
    (s : State C F) (t : State D F) (states : sr s t) (mode : Flapjack.AstHOL.ThunkMode)
    (x y : Value) (related : vr x y) : badThunkUpdate mode x s.refs = badThunkUpdate mode y t.refs := by
  have view := simpleValRel_view vr simple x y related
  cases view with
  | refPtr flag ptr =>
    have lookup := relatedRefs vr sr stateProps s t states ptr
    cases left : s.refs.lookup ptr <;> cases right : t.refs.lookup ptr <;>
      simp_all [optionRel, badThunkUpdate, destThunk]
    rename_i a b
    cases a <;> cases b <;> simp_all [refRel]
    cases flag <;> simp
  | number | word64 | byteVector | block | closureClosure | closureRec | recClosure | recRec =>
    simp [badThunkUpdate, destThunk]

/-- Thunk allocation case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevAllocThunk {C D F : Type} (mode : Flapjack.AstHOL.ThunkMode)
    (vr : Value → Value → Prop) (sr : State C F → State D F → Prop)
    (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.thunkOp (.allocThunk mode)) ys t with
    | .err err2 => ∃ err1, doApp (.thunkOp (.allocThunk mode)) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.thunkOp (.allocThunk mode)) xs s = .val (x, s1) := by
  obtain ⟨simple, stateProps, states, values⟩ := h
  cases values with
  | nil => simp [doApp, excRel]
  | @cons x y _ _ head tail =>
    cases tail with
    | cons next rest => simp [doApp, excRel]
    | nil =>
      have same := badThunkUpdateRelated vr sr simple stateProps s t states mode x y head
      cases bad : badThunkUpdate mode x s.refs with
      | true => simp [doApp, ← same, bad, excRel]
      | false =>
        have addressEq := leastUnusedRefRelated vr sr stateProps s t states
        have updated := stateProps.2.2.2.2.2.2.2.2.1 s t (leastUnusedRef s.refs) mode x y ⟨states, head⟩
        have pointerRel : vr (.refPtr false (leastUnusedRef s.refs)) (.refPtr false (leastUnusedRef s.refs)) :=
          (simple.2.2.2.2.1 _ _ _).2 rfl
        simp [doApp, ← same, bad, ← addressEq, pointerRel, updated]

/-- Thunk update case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevUpdateThunk {C D F : Type} (mode : Flapjack.AstHOL.ThunkMode)
    (vr : Value → Value → Prop) (sr : State C F → State D F → Prop)
    (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.thunkOp (.updateThunk mode)) ys t with
    | .err err2 => ∃ err1, doApp (.thunkOp (.updateThunk mode)) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.thunkOp (.updateThunk mode)) xs s = .val (x, s1) := by
  obtain ⟨simple, stateProps, states, values⟩ := h
  cases values with
  | nil => simp [doApp, excRel]
  | @cons x1 y1 _ _ first tail =>
    cases tail with
    | nil => simp [doApp, excRel]
    | @cons x2 y2 _ _ second tail =>
      cases tail with
      | cons third rest => simp [doApp, excRel]
      | nil =>
        have view := simpleValRel_view vr simple x1 y1 first
        cases view with
        | refPtr flag ptr =>
          cases flag with
          | true => simp [doApp, excRel]
          | false =>
            have same := badThunkUpdateRelated vr sr simple stateProps s t states mode x2 y2 second
            cases bad : badThunkUpdate mode x2 s.refs with
            | true => simp [doApp, ← same, bad, excRel]
            | false =>
              have lookup := relatedRefs vr sr stateProps s t states ptr
              cases l : s.refs.lookup ptr <;> cases r : t.refs.lookup ptr <;>
                simp_all [optionRel, doApp, excRel]
              rename_i a b
              cases a <;> cases b <;> simp_all [refRel]
              rename_i previousA old previous next
              cases previous with
              | evaluated => simp
              | notEvaluated =>
                have updated := stateProps.2.2.2.2.2.2.2.2.1 s t ptr mode x2 y2 ⟨states, second⟩
                have unit : vr unitValue unitValue := (simple.2.1 _ [] _).2 ⟨[], rfl, .nil⟩
                simp [unit, updated]
        | number | word64 | byteVector | block | closureClosure | closureRec | recClosure | recRec =>
          simp [doApp, excRel]

end Flapjack.Compiler.Backend.ClosProps.PrimitiveThunk
