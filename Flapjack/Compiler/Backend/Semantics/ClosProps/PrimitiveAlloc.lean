module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveMemory

@[expose] public section

/-! Reference allocation in the generic closure primitive simulation. -/
namespace Flapjack.Compiler.Backend.ClosProps.PrimitiveAlloc
open ClosSem Flapjack.SemanticPrimitivesProps

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Related states choose the same least unused reference. This is Flapjack
proof infrastructure. -/
theorem leastUnusedRefRelated {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleStateRel vr sr)
    (s : State C F) (t : State D F) (states : sr s t) : leastUnusedRef s.refs = leastUnusedRef t.refs := by
  have domain := (simple.2.2.2.2.1 s t states).2.1
  have free : ∀ i, s.refs.lookup i = none ↔ t.refs.lookup i = none := by
    intro i
    have same := domain i
    cases a : s.refs.lookup i <;> cases b : t.refs.lookup i <;> simp_all
  apply Nat.le_antisymm
  · by_contra notLe
    have smaller : leastUnusedRef t.refs < leastUnusedRef s.refs := by omega
    have occupied := leastUnusedRef_minimal s.refs _ smaller
    exact occupied ((free _).2 (leastUnusedRef_unused t.refs))
  · by_contra notLe
    have smaller : leastUnusedRef s.refs < leastUnusedRef t.refs := by omega
    have occupied := leastUnusedRef_minimal t.refs _ smaller
    exact occupied ((free _).1 (leastUnusedRef_unused s.refs))

/-- Reference allocation case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevRef {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.memOp .ref) ys t with
    | .err err2 => ∃ err1, doApp (.memOp .ref) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.memOp .ref) xs s = .val (x, s1) := by
  obtain ⟨simple, stateProps, states, values⟩ := h
  have addressEq := leastUnusedRefRelated vr sr stateProps s t states
  have updated := stateProps.2.2.2.2.2.2.2.1 s t (leastUnusedRef s.refs) xs ys ⟨states, values⟩
  have pointerRel : vr (.refPtr true (leastUnusedRef s.refs)) (.refPtr true (leastUnusedRef s.refs)) :=
    (simple.2.2.2.2.1 _ _ _).2 rfl
  simp [doApp, applyMemory, ← addressEq, pointerRel, updated]

/-- Value-array allocation case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevRefArray {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.memOp .refArray) ys t with
    | .err err2 => ∃ err1, doApp (.memOp .refArray) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.memOp .refArray) xs s = .val (x, s1) := by
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
        have view := simpleValRel_view vr simple x1 y1 first
        cases view with
        | number count =>
          by_cases negative : count < 0
          · simp [doApp, applyMemory, negative, excRel]
          · have repeated : List.Forall₂ vr (List.replicate count.toNat x2) (List.replicate count.toNat y2) := by
              generalize count.toNat = n
              induction n with
              | zero => exact .nil
              | succ n ih => exact .cons second ih
            have addressEq := leastUnusedRefRelated vr sr stateProps s t states
            have updated := stateProps.2.2.2.2.2.2.2.1 s t (leastUnusedRef s.refs) _ _ ⟨states, repeated⟩
            have pointerRel : vr (.refPtr true (leastUnusedRef s.refs)) (.refPtr true (leastUnusedRef s.refs)) :=
              (simple.2.2.2.2.1 _ _ _).2 rfl
            simp [doApp, applyMemory, negative, ← addressEq, pointerRel, updated]
        | word64 | byteVector | refPtr | block | closureClosure | closureRec | recClosure | recRec =>
          simp [doApp, applyMemory, excRel]

/-- Byte-array allocation case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevRefByte {C D F : Type} (flag : Bool) (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.memOp (.refByte flag)) ys t with
    | .err err2 => ∃ err1, doApp (.memOp (.refByte flag)) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.memOp (.refByte flag)) xs s = .val (x, s1) := by
  obtain ⟨simple, stateProps, states, values⟩ := h
  cases flag with
  | true => simp [doApp, applyMemory, excRel]
  | false =>
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
          rename_i count byte
          by_cases negative : count < 0
          · simp [negative]
          · cases converted : intToByte byte with
            | none => simp [negative]
            | some value =>
              have addressEq := leastUnusedRefRelated vr sr stateProps s t states
              have updated := stateProps.2.2.2.2.2.2.1 (List.replicate count.toNat value)
                s t (leastUnusedRef s.refs) states
              have pointerRel : vr (.refPtr true (leastUnusedRef s.refs)) (.refPtr true (leastUnusedRef s.refs)) :=
                (simple.2.2.2.2.1 _ _ _).2 rfl
              simp [negative, ← addressEq, pointerRel, updated]

end Flapjack.Compiler.Backend.ClosProps.PrimitiveAlloc
