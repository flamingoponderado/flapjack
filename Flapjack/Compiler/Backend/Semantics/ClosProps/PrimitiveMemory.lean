import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveBoolean
import Flapjack.Compiler.Backend.Semantics.ClosProps.RefRelations

/-! Reference inspection in the generic closure primitive simulation. -/
namespace Flapjack.Compiler.Backend.ClosProps.PrimitiveMemory
open ClosSem Flapjack.SemanticPrimitivesProps

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Simple state relations expose related reference entries. This is Flapjack
proof infrastructure. -/
theorem relatedRefs {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleStateRel vr sr)
    (s : State C F) (t : State D F) (states : sr s t) (ptr : Nat) :
    optionRel (refRel vr) (s.refs.lookup ptr) (t.refs.lookup ptr) := by
  cases target : t.refs.lookup ptr with
  | none =>
    have source := simple.1 s t ptr ⟨target, states⟩
    simp [source, optionRel]
  | some ref =>
    cases ref with
    | byteArray bytes =>
      have source := simple.2.1 bytes t s ptr ⟨target, states⟩
      simp [source, optionRel, refRel]
    | valueArray values =>
      obtain ⟨left, source, related⟩ := simple.2.2.1 values t s ptr ⟨target, states⟩
      simpa [target, source, optionRel, refRel] using related
    | thunk mode value =>
      obtain ⟨left, source, related⟩ := simple.2.2.2.1 mode value t s ptr ⟨target, states⟩
      simpa [target, source, optionRel, refRel] using related

/-- Value-array length case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevLength {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.memOp .length) ys t with
    | .err err2 => ∃ err1, doApp (.memOp .length) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.memOp .length) xs s = .val (x, s1) := by
  obtain ⟨simple, stateProps, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | @cons x y _ _ head tail =>
    cases tail with
    | cons next rest => simp [doApp, applyMemory, excRel]
    | nil =>
      have view := simpleValRel_view vr simple x y head
      cases view with
      | refPtr flag ptr =>
        have lookup := relatedRefs vr sr stateProps s t states ptr
        cases left : s.refs.lookup ptr <;> cases right : t.refs.lookup ptr <;>
          simp_all [optionRel, doApp, applyMemory, excRel]
        rename_i a b
        cases a <;> cases b <;> simp_all [refRel]
        rename_i fields nextFields
        have lengths := lookup.length_eq
        have number : vr (.number fields.length) (.number fields.length) := (simple.1 _ _).2 rfl
        simp [← lengths, number]
      | number | word64 | byteVector | block | closureClosure | closureRec | recClosure | recRec =>
        simp [doApp, applyMemory, excRel]

/-- Byte-array length case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevLengthByte {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.memOp .lengthByte) ys t with
    | .err err2 => ∃ err1, doApp (.memOp .lengthByte) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.memOp .lengthByte) xs s = .val (x, s1) := by
  obtain ⟨simple, stateProps, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | @cons x y _ _ head tail =>
    cases tail with
    | cons next rest => simp [doApp, applyMemory, excRel]
    | nil =>
      have view := simpleValRel_view vr simple x y head
      cases view with
      | refPtr flag ptr =>
        have lookup := relatedRefs vr sr stateProps s t states ptr
        cases left : s.refs.lookup ptr <;> cases right : t.refs.lookup ptr <;>
          simp_all [optionRel, doApp, applyMemory, excRel]
        rename_i a b
        cases a <;> cases b <;> simp_all [refRel]
        rename_i bytes
        have number : vr (.number bytes.length) (.number bytes.length) := (simple.1 _ _).2 rfl
        simp [number]
      | number | word64 | byteVector | block | closureClosure | closureRec | recClosure | recRec =>
        simp [doApp, applyMemory, excRel]

/-- Byte-array indexing case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevDerefByte {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.memOp .derefByte) ys t with
    | .err err2 => ∃ err1, doApp (.memOp .derefByte) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.memOp .derefByte) xs s = .val (x, s1) := by
  obtain ⟨simple, stateProps, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | @cons x1 y1 _ _ first tail =>
    cases tail with
    | nil => simp [doApp, applyMemory, excRel]
    | @cons x2 y2 _ _ second tail =>
      cases tail with
      | cons third rest => simp [doApp, applyMemory, excRel]
      | nil =>
        have firstView := simpleValRel_view vr simple x1 y1 first
        have secondView := simpleValRel_view vr simple x2 y2 second
        cases firstView <;> cases secondView <;> simp_all [doApp, applyMemory, excRel]
        rename_i flag ptr index
        have lookup := relatedRefs vr sr stateProps s t states ptr
        cases left : s.refs.lookup ptr <;> cases right : t.refs.lookup ptr <;>
          simp_all [optionRel]
        rename_i a b
        cases a <;> cases b <;> simp_all [refRel]
        rename_i bytes
        by_cases negative : index < 0
        · simp [negative]
        · cases found : bytes[index.toNat]? with
          | none => simp [negative]
          | some byte =>
            have number : vr (.number byte.toNat) (.number byte.toNat) := (simple.1 _ _).2 rfl
            simp [negative, number, states]

end Flapjack.Compiler.Backend.ClosProps.PrimitiveMemory
