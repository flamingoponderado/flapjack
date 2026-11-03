import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveBoolean

/-! Block construction and inspection in the generic primitive simulation. -/
namespace Flapjack.Compiler.Backend.ClosProps.PrimitiveBlock
open ClosSem Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.ClosProps.PrimitiveBoolean

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Block construction case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevCons {C D F : Type} (tag : Nat) (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.blockOp (.cons tag)) ys t with
    | .err err2 => ∃ err1, doApp (.blockOp (.cons tag)) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.blockOp (.cons tag)) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
  have blocks : vr (.block tag xs) (.block tag ys) :=
    (simple.2.1 _ ys tag).2 ⟨xs, rfl, values⟩
  simp [doApp, applyBlock, blocks, states]

/-- Block tag-test case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevTagEq {C D F : Type} (tag : Nat) (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.blockOp (.tagEq tag)) ys t with
    | .err err2 => ∃ err1, doApp (.blockOp (.tagEq tag)) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.blockOp (.tagEq tag)) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | @cons x y _ _ head tail =>
    cases tail with
    | cons next rest => simp [doApp, applyBlock, excRel]
    | nil =>
      have view := simpleValRel_view vr simple x y head
      cases view <;> simp [doApp, applyBlock, excRel, states, simpleValRel_boolValue, simple]

/-- Block length-test case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevLenEq {C D F : Type} (length : Nat) (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.blockOp (.lenEq length)) ys t with
    | .err err2 => ∃ err1, doApp (.blockOp (.lenEq length)) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.blockOp (.lenEq length)) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | @cons x y _ _ head tail =>
    cases tail with
    | cons next rest => simp [doApp, applyBlock, excRel]
    | nil =>
      have view := simpleValRel_view vr simple x y head
      cases view with
      | block tag as_ bs rel =>
        have lengths := rel.length_eq
        simp [doApp, applyBlock, ← lengths, states, simpleValRel_boolValue, simple]
      | number | word64 | byteVector | refPtr | closureClosure | closureRec | recClosure | recRec =>
        simp [doApp, applyBlock, excRel]

/-- Combined block tag and length-test case. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevTagLenEq {C D F : Type} (tag length : Nat) (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.blockOp (.tagLenEq tag length)) ys t with
    | .err err2 => ∃ err1, doApp (.blockOp (.tagLenEq tag length)) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.blockOp (.tagLenEq tag length)) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | @cons x y _ _ head tail =>
    cases tail with
    | cons next rest => simp [doApp, applyBlock, excRel]
    | nil =>
      have view := simpleValRel_view vr simple x y head
      cases view with
      | block actual as_ bs rel =>
        have lengths := rel.length_eq
        simp [doApp, applyBlock, ← lengths, states, simpleValRel_boolValue, simple]
      | number | word64 | byteVector | refPtr | closureClosure | closureRec | recClosure | recRec =>
        simp [doApp, applyBlock, excRel]

/-- Block length case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevLength {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.blockOp .lengthBlock) ys t with
    | .err err2 => ∃ err1, doApp (.blockOp .lengthBlock) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.blockOp .lengthBlock) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | @cons x y _ _ head tail =>
    cases tail with
    | cons next rest => simp [doApp, applyBlock, excRel]
    | nil =>
      have view := simpleValRel_view vr simple x y head
      cases view with
      | block tag as_ bs rel =>
        have lengths := rel.length_eq
        have number : vr (.number as_.length) (.number as_.length) := (simple.1 _ _).2 rfl
        simp [doApp, applyBlock, ← lengths, states, number]
      | number | word64 | byteVector | refPtr | closureClosure | closureRec | recClosure | recRec =>
        simp [doApp, applyBlock, excRel]

/-- Pointwise-related lists have related optional lookups. This is Flapjack
proof infrastructure. -/
private theorem relatedLookup {A B : Type} {r : A → B → Prop} {xs : List A} {ys : List B}
    (related : List.Forall₂ r xs ys) (index : Nat) :
    match xs[index]?, ys[index]? with
    | none, none => True
    | some x, some y => r x y
    | _, _ => False := by
  induction related generalizing index with
  | nil => simp
  | cons head tail ih =>
    cases index with
    | zero => exact head
    | succ index => exact ih index

/-- Block element lookup case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevElemAt {C D F : Type} (index : Nat) (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.blockOp (.elemAt index)) ys t with
    | .err err2 => ∃ err1, doApp (.blockOp (.elemAt index)) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.blockOp (.elemAt index)) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | @cons x y _ _ head tail =>
    cases tail with
    | cons next rest => simp [doApp, applyBlock, excRel]
    | nil =>
      have view := simpleValRel_view vr simple x y head
      cases view with
      | block tag as_ bs rel =>
        have lookup := relatedLookup rel index
        cases ha : as_[index]? <;> cases hb : bs[index]? <;>
          simp_all [doApp, applyBlock, excRel]
      | number | word64 | byteVector | refPtr | closureClosure | closureRec | recClosure | recRec =>
        simp [doApp, applyBlock, excRel]

end Flapjack.Compiler.Backend.ClosProps.PrimitiveBlock
