import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

namespace Flapjack.PanGlobalsShapeValueEval
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Flapjack proof factoring of the mutual shape/list induction, with no
    separate HOL declaration. Shape-generated expressions use only constants
    and records, so successful evaluation is independent of the state. -/
private theorem shapeValueSuccess {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs] :
    (∀ shape, ∃ value, evalHOLExact state (shapeValHOL shape) = some value) ∧
    (∀ shapes, ∃ values, evalListHOLExact state (shapeValsHOL shapes) = some values) := by
  have hs : ∀ shape, ∃ value, evalHOLExact state (shapeValHOL shape) = some value := by
    intro shape
    induction shape using ShapeHOL.rec (motive_2 := fun shapes =>
      ∃ values, evalListHOLExact state (shapeValsHOL shapes) = some values) with
    | one => exact ⟨.val (.word 0), by simp only [shapeValHOL, evalHOLExact]⟩
    | named name => exact ⟨.val (.word 0), by simp only [shapeValHOL, evalHOLExact]⟩
    | comb shapes ih =>
      obtain ⟨values, hv⟩ := ih
      exact ⟨.rStruct values, by simp only [shapeValHOL, evalHOLExact, hv, Option.map_some]⟩
    | nil => exact ⟨[], by simp only [shapeValsHOL, evalListHOLExact]⟩
    | cons shape shapes ihHead ihTail =>
      obtain ⟨value, hv⟩ := ihHead
      obtain ⟨values, hvs⟩ := ihTail
      exact ⟨value :: values, by simp only [shapeValsHOL, evalListHOLExact, hv, hvs]⟩
  refine ⟨hs, ?_⟩
  intro shapes
  induction shapes with
  | nil => exact ⟨[], by simp only [shapeValsHOL, evalListHOLExact]⟩
  | cons shape shapes ih =>
    obtain ⟨value, hv⟩ := hs shape
    obtain ⟨values, hvs⟩ := ih
    exact ⟨value :: values, by simp only [shapeValsHOL, evalListHOLExact, hv, hvs]⟩

/-- Same-module canonical state roundtrip for the finite-map qualifier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- HOL `pan_globalsProofScript.sml:968-978`, retaining both universally
    quantified scalar/list clauses and the source `NONE ⇔ False` statements.
    Classical memory-domain decisions are internal, not a logical premise;
    the generated expressions never inspect the memory domain. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "eval_shape_val_NONE"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evalShapeValNone {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    letI : DecidablePred state.memaddrs := fun a => Classical.propDecidable (state.memaddrs a)
    (∀ shape, evalHOLFinite state (shapeValHOL shape) = none ↔ False) ∧
    (∀ shapes, evalListHOLFinite state (shapeValsHOL shapes) = none ↔ False) := by
  classical
  obtain ⟨hs, hss⟩ := shapeValueSuccess state.toExact
  constructor
  · intro shape
    obtain ⟨value, hv⟩ := hs shape
    change evalHOLExact state.toExact (shapeValHOL shape) = none ↔ False
    rw [hv]
    simp
  · intro shapes
    obtain ⟨values, hvs⟩ := hss shapes
    change evalListHOLExact state.toExact (shapeValsHOL shapes) = none ↔ False
    rw [hvs]
    simp

/-- Flapjack list-predicate factoring; no separate HOL original. -/
private theorem wfShapesEqAll (shapes : List ShapeHOL) :
    isWfShapesExactHOL ([] : StructContextExact) shapes = shapes.all (isWfShapeExactHOL ([] : StructContextExact)) := by
  induction shapes with
  | nil => rfl
  | cons shape shapes ih => simp only [isWfShapesExactHOL, List.all_cons, ih]

/-- Flapjack mutual induction factoring for shape recovery, without a
    separate HOL original. Named shapes are excluded by empty-context wf. -/
private theorem shapeValueShape {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs] :
    ∀ shape value, evalHOLExact state (shapeValHOL shape) = some value →
      isWfShapeExactHOL ([] : StructContextExact) shape = true → shape = shapeOfHOLExact value := by
  intro shape
  induction shape using ShapeHOL.rec (motive_2 := fun shapes =>
    ∀ values, evalListHOLExact state (shapeValsHOL shapes) = some values →
      shapes.all (isWfShapeExactHOL ([] : StructContextExact)) = true → shapes = values.map shapeOfHOLExact) with
  | one =>
    intro value he _
    simp only [shapeValHOL, evalHOLExact, Option.some.injEq] at he
    subst value
    simp only [shapeOfHOLExact]
  | named name =>
    intro value he hw
    simp [isWfShapeExactHOL, structContextLookupHOL] at hw
  | comb shapes ih =>
    intro value he hw
    simp only [shapeValHOL, evalHOLExact] at he
    cases hl : evalListHOLExact state (shapeValsHOL shapes) with
    | none => simp only [hl, Option.map_none, reduceCtorEq] at he
    | some values =>
      have hv : ValueHOL.rStruct values = value := by
        simpa only [hl, Option.map_some, Option.some.injEq] using he
      subst value
      have hw' : shapes.all (isWfShapeExactHOL ([] : StructContextExact)) = true := by
        simpa only [isWfShapeExactHOL, wfShapesEqAll] using hw
      rw [shapeOfHOLExact, ih values hl hw']
  | nil =>
    rename_i values he hw
    simp only [shapeValsHOL, evalListHOLExact, Option.some.injEq] at he
    subst values
    rfl
  | cons shape shapes ihHead ihTail =>
    rename_i values he hw
    cases hh : evalHOLExact state (shapeValHOL shape) with
    | none => simp only [shapeValsHOL, evalListHOLExact, hh] at he; cases he
    | some head =>
      cases ht : evalListHOLExact state (shapeValsHOL shapes) with
      | none => simp only [shapeValsHOL, evalListHOLExact, hh, ht] at he; cases he
      | some tail =>
        have hv : head :: tail = values := by
          simpa only [shapeValsHOL, evalListHOLExact, hh, ht, Option.some.injEq] using he
        subst values
        simp only [List.all_cons, Bool.and_eq_true] at hw
        rw [List.map_cons, ← ihHead head hh hw.1, ← ihTail tail ht hw.2]

/-- Flapjack list induction factoring; no separate HOL original. -/
private theorem shapeValuesShape {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (shapes : List ShapeHOL) (values : List (ValueHOL width))
    (he : evalListHOLExact state (shapeValsHOL shapes) = some values)
    (hw : shapes.all (isWfShapeExactHOL ([] : StructContextExact)) = true) :
    shapes = values.map shapeOfHOLExact := by
  induction shapes generalizing values with
  | nil =>
    simp only [shapeValsHOL, evalListHOLExact, Option.some.injEq] at he
    subst values
    rfl
  | cons shape shapes ih =>
    cases hh : evalHOLExact state (shapeValHOL shape) with
    | none => simp only [shapeValsHOL, evalListHOLExact, hh] at he; cases he
    | some head =>
      cases ht : evalListHOLExact state (shapeValsHOL shapes) with
      | none => simp only [shapeValsHOL, evalListHOLExact, hh, ht] at he; cases he
      | some tail =>
        have hv : head :: tail = values := by
          simpa only [shapeValsHOL, evalListHOLExact, hh, ht, Option.some.injEq] using he
        subst values
        simp only [List.all_cons, Bool.and_eq_true] at hw
        rw [List.map_cons, ← shapeValueShape state shape head hh hw.1, ← ih tail ht hw.2]

/-- HOL `pan_globalsProofScript.sml:980-991`: successful evaluation of
    canonical shape expressions recovers their original shapes under the
    source empty-context well-formedness test. Both scalar and list clauses,
    their successful-evaluation/wf conjunctions and equality directions are
    retained. `is_wf_shape_nil` is exactly `isWfShapeExactHOL ([] : StructContextExact)`; `EVERY`
    is the literal list `all` predicate. No successful target fact is assumed. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "eval_shape_val_thm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evalShapeValShape {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    letI : DecidablePred state.memaddrs := fun a => Classical.propDecidable (state.memaddrs a)
    (∀ shape value, evalHOLFinite state (shapeValHOL shape) = some value ∧
      isWfShapeExactHOL ([] : StructContextExact) shape = true → shape = shapeOfHOLExact value) ∧
    (∀ shapes values, evalListHOLFinite state (shapeValsHOL shapes) = some values ∧
      shapes.all (isWfShapeExactHOL ([] : StructContextExact)) = true → shapes = values.map shapeOfHOLExact) := by
  classical
  constructor
  · intro shape value h
    exact shapeValueShape state.toExact shape value h.1 h.2
  · intro shapes values h
    exact shapeValuesShape state.toExact shapes values h.1 h.2

end Flapjack.PanGlobalsShapeValueEval
