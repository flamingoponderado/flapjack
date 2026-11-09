module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveBoolean

@[expose] public section

/-! List and equality cases of the generic closure primitive simulation. -/
namespace Flapjack.Compiler.Backend.ClosProps.PrimitiveLists
open ClosSem Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.ClosProps.PrimitiveBoolean

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Structural-equality case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevEqual {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.blockOp .equal) ys t with
    | .err err2 => ∃ err1, doApp (.blockOp .equal) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.blockOp .equal) xs s = .val (x, s1) := by
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
        have same := doEq_related vr simple x1 x2 y1 y2 first second
        cases he : doEq y1 y2 <;> simp_all [doApp, applyBlock, excRel, simpleValRel_boolValue]

/-- Converting an encoded list to a block preserves the reverse simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevFromList {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (tag : Nat) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.blockOp (.fromList tag)) ys t with
    | .err err2 => ∃ err1, doApp (.blockOp (.fromList tag)) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.blockOp (.fromList tag)) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | @cons x y _ _ head rest =>
    cases rest with
    | cons a rest => simp [doApp, applyBlock, excRel]
    | nil =>
      have related := valueToList_related vr simple x y head
      cases hx : valueToList x <;> cases hy : valueToList y <;>
        simp_all [doApp, applyBlock, excRel, simpleValRel]

/-- Encoded-list append case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevListAppend {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.blockOp .listAppend) ys t with
    | .err err2 => ∃ err1, doApp (.blockOp .listAppend) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.blockOp .listAppend) xs s = .val (x, s1) := by
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
        have one := valueToList_related vr simple x1 y1 first
        have two := valueToList_related vr simple x2 y2 second
        cases h1 : valueToList x1 <;> cases h2 : valueToList y1 <;>
          cases h3 : valueToList x2 <;> cases h4 : valueToList y2 <;>
          simp_all [doApp, applyBlock, excRel]
        rename_i a b c d
        exact (valueRel_listToValue vr (b ++ d) (listToValue (a ++ c)) simple).2
          ⟨_, rfl, List.rel_append one two⟩

end Flapjack.Compiler.Backend.ClosProps.PrimitiveLists
