module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveBoolean

@[expose] public section

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

/-- Constant values are related to themselves under a simple relation. This
is Flapjack proof infrastructure. -/
theorem makeConstRelated (vr : Value → Value → Prop) (simple : simpleValRel vr)
    (constant : ClosLang.Const) : vr (makeConst constant) (makeConst constant) := by
  cases constant with
  | constInt value => simpa [makeConst] using (simple.1 (.number value) value).2 rfl
  | constWord64 value => simpa [makeConst] using (simple.2.2.1 (.word64 value) value).2 rfl
  | constStr value => simpa [makeConst] using (simple.2.2.2.1 (.byteVector value.explode) value.explode).2 rfl
  | constCons tag constants =>
    simp only [makeConst]
    apply (simple.2.1 _ _ _).2
    refine ⟨_, rfl, ?_⟩
    have worker : ∀ xs : List ClosLang.Const, (∀ x ∈ xs, x ∈ constants) →
        List.Forall₂ vr (xs.map makeConst) (xs.map makeConst) := by
      intro xs member
      induction xs with
      | nil => exact .nil
      | cons first rest ih =>
        apply List.Forall₂.cons
        · have contained : first ∈ constants := member first (by simp)
          exact makeConstRelated vr simple first
        · apply ih
          intro x hx
          exact member x (by simp [hx])
    exact worker constants (by intro x hx; exact hx)
termination_by sizeOf constant
decreasing_by
  simp_wf
  have bound := List.sizeOf_lt_of_mem contained
  omega

/-- Constant-construction case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevConstant {C D F : Type} (constant : ClosLang.Const)
    (vr : Value → Value → Prop) (sr : State C F → State D F → Prop)
    (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.blockOp (.constant constant)) ys t with
    | .err err2 => ∃ err1, doApp (.blockOp (.constant constant)) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.blockOp (.constant constant)) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyBlock, makeConstRelated vr simple, states]
  | cons head tail => simp [doApp, applyBlock, excRel]

/-- Constant-comparison case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevEqualConst {C D F : Type} (constant : ClosLang.ConstPart)
    (vr : Value → Value → Prop) (sr : State C F → State D F → Prop)
    (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.blockOp (.equalConst constant)) ys t with
    | .err err2 => ∃ err1, doApp (.blockOp (.equalConst constant)) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.blockOp (.equalConst constant)) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | @cons x y _ _ head tail =>
    cases tail with
    | cons next rest => simp [doApp, applyBlock, excRel]
    | nil =>
      have view := simpleValRel_view vr simple x y head
      cases constant <;> cases view <;>
        simp [doApp, applyBlock, excRel, states, simpleValRel_boolValue, simple]

/-- Block bounds-check case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevBounds {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.blockOp .boundsCheckBlock) ys t with
    | .err err2 => ∃ err1, doApp (.blockOp .boundsCheckBlock) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.blockOp .boundsCheckBlock) xs s = .val (x, s1) := by
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
        have view1 := simpleValRel_view vr simple x1 y1 first
        have view2 := simpleValRel_view vr simple x2 y2 second
        cases view1 <;> cases view2 <;> simp_all [doApp, applyBlock, excRel]
        rename_i tag left right rel index
        have lengths := rel.length_eq
        simp [← lengths, simpleValRel_boolValue, simple]

/-- The unsupported Build primitive fails on both sides. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevBuild {C D F : Type} (parts : List ClosLang.ConstPart)
    (vr : Value → Value → Prop) (sr : State C F → State D F → Prop)
    (s : State C F) (t : State D F) (xs ys : List Value)
    (_h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.blockOp (.build parts)) ys t with
    | .err err2 => ∃ err1, doApp (.blockOp (.build parts)) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.blockOp (.build parts)) xs s = .val (x, s1) := by
  simp [doApp_build_fallback, excRel]

/-- Block extension case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevConsExtend {C D F : Type} (tag : Nat) (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.blockOp (.consExtend tag)) ys t with
    | .err err2 => ∃ err1, doApp (.blockOp (.consExtend tag)) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.blockOp (.consExtend tag)) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | @cons x1 y1 _ _ first rest =>
    have firstView := simpleValRel_view vr simple x1 y1 first
    cases firstView with
    | block original fields nextFields fieldsRel =>
      cases rest with
      | nil => simp [doApp, applyBlock, excRel]
      | @cons x2 y2 _ _ lowerRel rest =>
        have lowerView := simpleValRel_view vr simple x2 y2 lowerRel
        cases lowerView with
        | number lower =>
          cases rest with
          | nil => simp [doApp, applyBlock, excRel]
          | @cons x3 y3 _ _ lenRel rest =>
            have lenView := simpleValRel_view vr simple x3 y3 lenRel
            cases lenView with
            | number len =>
              cases rest with
              | nil => simp [doApp, applyBlock, excRel]
              | @cons x4 y4 initial nextInitial totalRel initialRel =>
                have totalView := simpleValRel_view vr simple x4 y4 totalRel
                cases totalView with
                | number total =>
                  have fieldsLength := fieldsRel.length_eq
                  have initialLength := initialRel.length_eq
                  have sliceRel := List.forall₂_take len.toNat (List.forall₂_drop lower.toNat fieldsRel)
                  have resultRel : vr (.block tag (initial ++ (fields.drop lower.toNat).take len.toNat))
                      (.block tag (nextInitial ++ (nextFields.drop lower.toNat).take len.toNat)) :=
                    (simple.2.1 _ _ _).2 ⟨_, rfl, List.rel_append initialRel sliceRel⟩
                  by_cases invalid : lower < 0 ∨ len < 0 ∨ Int.ofNat fields.length < lower + len ∨
                      total = 0 ∨ total ≠ Int.ofNat initial.length + len
                  · simp only [doApp, applyBlock, ← fieldsLength, ← initialLength]
                    rw [if_pos invalid, if_pos invalid]
                    exact ⟨_, rfl, rfl⟩
                  · simp only [doApp, applyBlock, ← fieldsLength, ← initialLength]
                    rw [if_neg invalid, if_neg invalid]
                    exact ⟨_, _, resultRel, states, rfl⟩
                | word64 | block | byteVector | refPtr | closureClosure | closureRec | recClosure | recRec =>
                  simp [doApp, applyBlock, excRel]
            | word64 | block | byteVector | refPtr | closureClosure | closureRec | recClosure | recRec =>
              cases rest <;> simp [doApp, applyBlock, excRel]
        | word64 | block | byteVector | refPtr | closureClosure | closureRec | recClosure | recRec =>
          cases rest <;> simp [doApp, applyBlock, excRel]
    | number | word64 | byteVector | refPtr | closureClosure | closureRec | recClosure | recRec =>
      cases rest <;> simp [doApp, applyBlock, excRel]

end Flapjack.Compiler.Backend.ClosProps.PrimitiveBlock
