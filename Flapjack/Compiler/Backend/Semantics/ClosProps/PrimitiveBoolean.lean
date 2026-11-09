module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.Equality
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Apply
public import Flapjack.SemanticPrimitivesProps.ResultRelation

@[expose] public section

/-! Boolean cases of the generic closure primitive simulation. -/
namespace Flapjack.Compiler.Backend.ClosProps.PrimitiveBoolean
open ClosSem Flapjack.SemanticPrimitivesProps

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Related values decode to the same Boolean or both fail to decode.
This is Flapjack proof infrastructure. -/
theorem simpleValRel_asBool (vr : Value → Value → Prop) (simple : simpleValRel vr)
    (x y : Value) (related : vr x y) : asBool x = asBool y := by
  have view := simpleValRel_view vr simple x y related
  cases view with
  | block tag xs ys fields =>
    cases fields with
    | nil => rfl
    | cons head tail =>
      cases tag <;> simp [asBool]
  | number | word64 | byteVector | refPtr | closureClosure | closureRec | recClosure | recRec => rfl

/-- A simple value relation relates identical Boolean values. This is
Flapjack proof infrastructure. -/
theorem simpleValRel_boolValue (vr : Value → Value → Prop) (simple : simpleValRel vr)
    (b : Bool) : vr (boolValue b) (boolValue b) := by
  cases b <;> apply (simple.2.1 _ [] _).mpr <;> exact ⟨[], rfl, .nil⟩

/-- Boolean-test case of the reverse primitive-operation simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevBoolTest {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (test : Flapjack.AstHOL.Test)
    (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.blockOp (.boolTest test)) ys t with
    | .err err2 => ∃ err1, doApp (.blockOp (.boolTest test)) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.blockOp (.boolTest test)) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | @cons x1 y1 _ _ first rest =>
    cases rest with
    | nil => simp [doApp, applyBlock, excRel]
    | @cons x2 y2 _ _ second rest =>
      cases rest with
      | cons third rest => simp [doApp, applyBlock, excRel]
      | nil =>
        have a := simpleValRel_asBool vr simple _ _ first
        have b := simpleValRel_asBool vr simple _ _ second
        cases ha : asBool y1 <;> cases hb : asBool y2 <;>
          simp_all [doApp, applyBlock, excRel, simpleValRel_boolValue]

/-- Boolean-negation case of the reverse primitive-operation simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevBoolNot {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.blockOp .boolNot) ys t with
    | .err err2 => ∃ err1, doApp (.blockOp .boolNot) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.blockOp .boolNot) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | @cons x y _ _ first rest =>
    cases rest with
    | cons second rest => simp [doApp, applyBlock, excRel]
    | nil =>
      have a := simpleValRel_asBool vr simple x y first
      cases ha : asBool y <;> simp_all [doApp, applyBlock, excRel, simpleValRel_boolValue]

end Flapjack.Compiler.Backend.ClosProps.PrimitiveBoolean
