module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveBoolean

@[expose] public section

/-! Byte-vector cases of the generic closure primitive simulation. -/
namespace Flapjack.Compiler.Backend.ClosProps.PrimitiveBytes
open ClosSem Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.ClosProps.PrimitiveBoolean

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Related lists decode to identical byte-vector sequences. This is Flapjack
proof infrastructure. -/
private theorem byteVectorsRelated (vr : Value → Value → Prop) (simple : simpleValRel vr)
    {xs ys : List Value} (related : List.Forall₂ vr xs ys) : byteVectors xs = byteVectors ys := by
  induction related with
  | nil => rfl
  | @cons a b _ _ head tail ih =>
    have view := simpleValRel_view vr simple a b head
    cases view <;> simp [byteVectors, ih]

/-- Related lists decode to identical byte-number sequences. This is Flapjack
proof infrastructure. -/
private theorem byteNumbersRelated (vr : Value → Value → Prop) (simple : simpleValRel vr)
    {xs ys : List Value} (related : List.Forall₂ vr xs ys) : byteNumbers xs = byteNumbers ys := by
  induction related with
  | nil => rfl
  | @cons a b _ _ head tail ih =>
    have view := simpleValRel_view vr simple a b head
    cases view <;> simp [byteNumbers, ih]

/-- Byte-list decoding case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevFromListByte {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.memOp .fromListByte) ys t with
    | .err err2 => ∃ err1, doApp (.memOp .fromListByte) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.memOp .fromListByte) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | @cons x y _ _ head tail =>
    cases tail with
    | cons next rest => simp [doApp, applyMemory, excRel]
    | nil =>
      have decoded := valueToList_related vr simple x y head
      cases l : valueToList x <;> cases r : valueToList y <;>
        simp_all [doApp, applyMemory, excRel]
      have same := byteNumbersRelated vr simple decoded
      rw [← same]
      cases numbers : byteNumbers _ with
      | none => simp
      | some bytes =>
        have valueRel : vr (.byteVector bytes) (.byteVector bytes) := (simple.2.2.2.1 _ _).2 rfl
        simp [valueRel, states]

/-- Byte-vector concatenation case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevConcatByteVec {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.memOp .concatByteVec) ys t with
    | .err err2 => ∃ err1, doApp (.memOp .concatByteVec) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.memOp .concatByteVec) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | @cons x y _ _ head tail =>
    cases tail with
    | cons next rest => simp [doApp, applyMemory, excRel]
    | nil =>
      have decoded := valueToList_related vr simple x y head
      cases l : valueToList x <;> cases r : valueToList y <;>
        simp_all [doApp, applyMemory, excRel]
      have same := byteVectorsRelated vr simple decoded
      rw [← same]
      cases vectors : byteVectors _ with
      | none => simp
      | some chunks =>
        have valueRel : vr (.byteVector chunks.flatten) (.byteVector chunks.flatten) := (simple.2.2.2.1 _ _).2 rfl
        simp [valueRel, states]

/-- Byte-vector length case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevLengthByteVec {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.memOp .lengthByteVec) ys t with
    | .err err2 => ∃ err1, doApp (.memOp .lengthByteVec) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.memOp .lengthByteVec) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | @cons x y _ _ head tail =>
    cases tail with
    | cons next rest => simp [doApp, applyMemory, excRel]
    | nil =>
      have view := simpleValRel_view vr simple x y head
      cases view with
      | byteVector bytes =>
        have valueRel : vr (.number bytes.length) (.number bytes.length) := (simple.1 _ _).2 rfl
        simp [doApp, applyMemory, valueRel, states]
      | number | word64 | refPtr | block | closureClosure | closureRec | recClosure | recRec =>
        simp [doApp, applyMemory, excRel]

/-- Byte-vector encoding case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevToListByte {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.memOp .toListByte) ys t with
    | .err err2 => ∃ err1, doApp (.memOp .toListByte) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.memOp .toListByte) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | @cons x y _ _ head tail =>
    cases tail with
    | cons next rest => simp [doApp, applyMemory, excRel]
    | nil =>
      have view := simpleValRel_view vr simple x y head
      cases view with
      | byteVector bytes =>
        clear head
        have elements : List.Forall₂ vr (bytes.map (fun b => .number b.toNat))
            (bytes.map (fun b => .number b.toNat)) := by
          induction bytes with
          | nil => exact .nil
          | cons byte rest ih => exact .cons ((simple.1 _ _).2 rfl) ih
        have valueRel := (valueRel_listToValue vr _ _ simple).2 ⟨_, rfl, elements⟩
        simp [doApp, applyMemory, valueRel, states]
      | number | word64 | refPtr | block | closureClosure | closureRec | recClosure | recRec =>
        simp [doApp, applyMemory, excRel]

/-- Byte-vector indexing case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevDerefByteVec {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.memOp .derefByteVec) ys t with
    | .err err2 => ∃ err1, doApp (.memOp .derefByteVec) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.memOp .derefByteVec) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
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
        rename_i bytes index
        by_cases negative : index < 0
        · simp [negative]
        · cases found : bytes[index.toNat]? with
          | none => simp [negative]
          | some byte =>
            have related : vr (.number byte.toNat) (.number byte.toNat) := (simple.1 _ _).2 rfl
            simp [negative, related, states]

/-- Byte-string comparison case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevStringCmp {C D F : Type} (fast : Bool) (op : Flapjack.Opb)
    (vr : Value → Value → Prop) (sr : State C F → State D F → Prop)
    (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.memOp (.stringCmp fast op)) ys t with
    | .err err2 => ∃ err1, doApp (.memOp (.stringCmp fast op)) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.memOp (.stringCmp fast op)) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
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
        cases firstView <;> cases secondView <;>
          simp [doApp, applyMemory, excRel, simpleValRel_boolValue, simple, states]

end Flapjack.Compiler.Backend.ClosProps.PrimitiveBytes
