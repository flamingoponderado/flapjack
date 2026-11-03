import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveMemory

/-! Byte copying and XOR in the generic closure primitive simulation. -/
namespace Flapjack.Compiler.Backend.ClosProps.PrimitiveCopy
open ClosSem Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.ClosProps.PrimitiveMemory

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Byte-array XOR case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevXorByte {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.memOp .xorByte) ys t with
    | .err err2 => ∃ err1, doApp (.memOp .xorByte) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.memOp .xorByte) xs s = .val (x, s1) := by
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
        rename_i flag ptr input
        have lookup := relatedRefs vr sr stateProps s t states ptr
        cases l : s.refs.lookup ptr <;> cases r : t.refs.lookup ptr <;> simp_all [optionRel]
        rename_i a b
        cases a <;> cases b <;> simp_all [refRel]
        rename_i bytes
        cases run : Flapjack.SemanticPrimitivesHOL.xorBytes input bytes with
        | none => simp
        | some result =>
          have updated := stateProps.2.2.2.2.2.2.1 result s t ptr states
          have unit : vr unitValue unitValue := (simple.2.1 _ [] _).2 ⟨[], rfl, .nil⟩
          simp [unit, updated]

/-- Copying into a new byte vector preserves the result and failures for both
vector and reference sources. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevCopyByteNew {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.memOp (.copyByte true)) ys t with
    | .err err2 => ∃ err1, doApp (.memOp (.copyByte true)) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.memOp (.copyByte true)) xs s = .val (x, s1) := by
  obtain ⟨simple, stateProps, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | @cons x1 y1 _ _ first tail =>
    cases tail with
    | nil => simp [doApp, applyMemory, excRel]
    | @cons x2 y2 _ _ second tail =>
      cases tail with
      | nil => simp [doApp, applyMemory, excRel]
      | @cons x3 y3 _ _ third tail =>
        cases tail with
        | cons fourth rest => simp [doApp, applyMemory, excRel]
        | nil =>
          have firstView := simpleValRel_view vr simple x1 y1 first
          have secondView := simpleValRel_view vr simple x2 y2 second
          cases firstView <;> cases secondView <;> simp_all [doApp, applyMemory, excRel]
          all_goals
            have thirdView := simpleValRel_view vr simple x3 y3 third
            cases thirdView <;> simp_all
          case byteVector.number.number bytes offset length =>
            cases run : Flapjack.SemanticPrimitivesHOL.copyArray (bytes, offset) length none with
            | none => simp
            | some copied =>
              have rel : vr (.byteVector copied) (.byteVector copied) := (simple.2.2.2.1 _ _).2 rfl
              simp [rel, states]

          case refPtr.number.number flag ptr offset length =>
            have lookup := relatedRefs vr sr stateProps s t states ptr
            cases l : s.refs.lookup ptr <;> cases r : t.refs.lookup ptr <;> simp_all [optionRel]
            rename_i a b
            cases a <;> cases b <;> simp_all [refRel]
            rename_i bytes
            cases run : Flapjack.SemanticPrimitivesHOL.copyArray (bytes, offset) length none with
            | none => simp
            | some copied =>
              have rel : vr (.byteVector copied) (.byteVector copied) := (simple.2.2.2.1 _ _).2 rfl
              simp [rel, states]


/-- In-place copying from a vector preserves related states. This is Flapjack
proof infrastructure for the CopyByte case. -/
private theorem copyByteWriteVector {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValRel vr) (stateProps : simpleStateRel vr sr)
    (s : State C F) (t : State D F) (states : sr s t) (input : List (BitVec 8))
    (offset length dstOffset : Int) (flag : Bool) (dst : Nat) :
    match doApp (.memOp (.copyByte false))
      [.byteVector input, .number offset, .number length, .refPtr flag dst, .number dstOffset] t with
    | .err err2 => ∃ err1, doApp (.memOp (.copyByte false))
        [.byteVector input, .number offset, .number length, .refPtr flag dst, .number dstOffset] s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.memOp (.copyByte false))
        [.byteVector input, .number offset, .number length, .refPtr flag dst, .number dstOffset] s = .val (x, s1) := by
  have lookup := relatedRefs vr sr stateProps s t states dst
  cases l : s.refs.lookup dst <;> cases r : t.refs.lookup dst <;> simp_all [optionRel, doApp, applyMemory, excRel]
  rename_i a b
  cases a <;> cases b <;> simp_all [refRel]
  rename_i bytes
  cases run : Flapjack.SemanticPrimitivesHOL.copyArray (input, offset) length (some (bytes, dstOffset)) with
  | none => simp
  | some copied =>
    have updated := stateProps.2.2.2.2.2.2.1 copied s t dst states
    have unit : vr unitValue unitValue := (simple.2.1 _ [] _).2 ⟨[], rfl, .nil⟩
    simp [unit, updated]

/-- Copying from a reference also covers overlapping source and destination.
This is Flapjack proof infrastructure for the CopyByte case. -/
private theorem copyByteWriteRef {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValRel vr) (stateProps : simpleStateRel vr sr)
    (s : State C F) (t : State D F) (states : sr s t) (srcFlag : Bool) (src : Nat)
    (offset length dstOffset : Int) (dstFlag : Bool) (dst : Nat) :
    match doApp (.memOp (.copyByte false))
      [.refPtr srcFlag src, .number offset, .number length, .refPtr dstFlag dst, .number dstOffset] t with
    | .err err2 => ∃ err1, doApp (.memOp (.copyByte false))
        [.refPtr srcFlag src, .number offset, .number length, .refPtr dstFlag dst, .number dstOffset] s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.memOp (.copyByte false))
        [.refPtr srcFlag src, .number offset, .number length, .refPtr dstFlag dst, .number dstOffset] s = .val (x, s1) := by
  have lookup := relatedRefs vr sr stateProps s t states src
  cases l : s.refs.lookup src <;> cases r : t.refs.lookup src <;> simp_all [optionRel, doApp, applyMemory, excRel]
  rename_i a b
  cases a <;> cases b <;> simp_all [refRel]
  rename_i bytes
  have vector := copyByteWriteVector vr sr simple stateProps s t states bytes offset length dstOffset dstFlag dst
  simpa [doApp, applyMemory, excRel] using vector

/-- In-place byte copying case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevCopyByteWrite {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.memOp (.copyByte false)) ys t with
    | .err err2 => ∃ err1, doApp (.memOp (.copyByte false)) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.memOp (.copyByte false)) xs s = .val (x, s1) := by
  obtain ⟨simple, stateProps, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | @cons x1 y1 _ _ first tail =>
    cases tail with
    | nil => simp [doApp, applyMemory, excRel]
    | @cons x2 y2 _ _ second tail =>
      cases tail with
      | nil => simp [doApp, applyMemory, excRel]
      | @cons x3 y3 _ _ third tail =>
        cases tail with
        | nil => simp [doApp, applyMemory, excRel]
        | @cons x4 y4 _ _ fourth tail =>
          cases tail with
          | nil => simp [doApp, applyMemory, excRel]
          | @cons x5 y5 _ _ fifth tail =>
            cases tail with
            | cons sixth rest => simp [doApp, applyMemory, excRel]
            | nil =>
              have v1 := simpleValRel_view vr simple x1 y1 first
              have v2 := simpleValRel_view vr simple x2 y2 second
              have v3 := simpleValRel_view vr simple x3 y3 third
              have v4 := simpleValRel_view vr simple x4 y4 fourth
              have v5 := simpleValRel_view vr simple x5 y5 fifth
              cases v2 with
              | number offset =>
                cases v3 with
                | number length =>
                  cases v4 with
                  | refPtr flag dst =>
                    cases v5 with
                    | number dstOffset =>
                      cases v1 with
                      | byteVector input => exact copyByteWriteVector vr sr simple stateProps s t states input offset length dstOffset flag dst
                      | refPtr srcFlag src => exact copyByteWriteRef vr sr simple stateProps s t states srcFlag src offset length dstOffset flag dst
                      | number | word64 | block | closureClosure | closureRec | recClosure | recRec => simp [doApp, applyMemory, excRel]
                    | word64 | byteVector | refPtr | block | closureClosure | closureRec | recClosure | recRec =>
                      cases v1 <;> simp [doApp, applyMemory, excRel]
                  | number | word64 | byteVector | block | closureClosure | closureRec | recClosure | recRec =>
                    cases v1 <;> simp [doApp, applyMemory, excRel]
                | word64 | byteVector | refPtr | block | closureClosure | closureRec | recClosure | recRec =>
                  cases v1 <;> simp [doApp, applyMemory, excRel]
              | word64 | byteVector | refPtr | block | closureClosure | closureRec | recClosure | recRec =>
                cases v1 <;> simp [doApp, applyMemory, excRel]

end Flapjack.Compiler.Backend.ClosProps.PrimitiveCopy
