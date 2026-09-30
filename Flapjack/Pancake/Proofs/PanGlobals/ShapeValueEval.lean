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

end Flapjack.PanGlobalsShapeValueEval
