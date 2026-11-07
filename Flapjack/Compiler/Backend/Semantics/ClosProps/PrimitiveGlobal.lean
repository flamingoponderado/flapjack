import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveBoolean

/-! Global-variable cases of the generic closure primitive simulation. -/
namespace Flapjack.Compiler.Backend.ClosProps.PrimitiveGlobal
open ClosSem Flapjack.SemanticPrimitivesProps

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Corresponding global slots remain related, including missing slots.
This is Flapjack proof infrastructure. -/
private theorem globalLookup (vr : Value → Value → Prop) {xs ys : List (Option Value)}
    (related : List.Forall₂ (optionRel vr) xs ys) (index : Nat) :
    optionRel (optionRel vr) (getGlobal index xs) (getGlobal index ys) := by
  induction related generalizing index with
  | nil => simp [getGlobal, optionRel]
  | cons head tail ih =>
    cases index with
    | zero => simpa [getGlobal, optionRel] using head
    | succ index => simpa [getGlobal] using ih index

/-- Replacing corresponding global slots preserves their relation. This is
Flapjack proof infrastructure. -/
private theorem relatedSet {A B : Type} {rel : A → B → Prop} {xs : List A} {ys : List B}
    (related : List.Forall₂ rel xs ys) (index : Nat) (x : A) (y : B) (h : rel x y) :
    List.Forall₂ rel (xs.set index x) (ys.set index y) := by
  induction related generalizing index with
  | nil => simp
  | cons head tail ih =>
    cases index with
    | zero => exact .cons h tail
    | succ index => exact .cons head (ih index)

/-- Simple value relations relate the unit value to itself. This is Flapjack
proof infrastructure. -/
private theorem unitRelated (vr : Value → Value → Prop) (simple : simpleValRel vr) :
    vr unitValue unitValue := (simple.2.1 _ [] _).2 ⟨[], rfl, .nil⟩

/-- Global-read case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevGlobal {C D F : Type} (index : Nat) (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.globOp (.global index)) ys t with
    | .err err2 => ∃ err1, doApp (.globOp (.global index)) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.globOp (.global index)) xs s = .val (x, s1) := by
  obtain ⟨simple, stateProps, states, values⟩ := h
  have globals := (stateProps.2.2.2.2.1 s t states).2.2
  cases values with
  | nil =>
    have lookup := globalLookup vr globals index
    cases l : getGlobal index s.globals <;> cases r : getGlobal index t.globals <;>
      simp_all [optionRel, doApp, applyGlobal, excRel]
    all_goals rename_i a b; cases a <;> cases b <;> simp_all
  | @cons x y _ _ head tail =>
    cases tail with
    | cons next rest => simp [doApp, applyGlobal, excRel]
    | nil =>
      have view := simpleValRel_view vr simple x y head
      cases view with
      | number n =>
        by_cases neg : n < 0
        · simp [doApp, applyGlobal, neg, excRel]
        · have lookup := globalLookup vr globals n.toNat
          cases l : getGlobal n.toNat s.globals <;> cases r : getGlobal n.toNat t.globals <;>
            simp_all [optionRel, doApp, applyGlobal, excRel]
          all_goals rename_i a b; cases a <;> cases b <;> simp_all
          all_goals simp [show ¬ n < 0 by omega, lookup, states]
      | word64 | byteVector | refPtr | block | closureClosure | closureRec | recClosure | recRec =>
        simp [doApp, applyGlobal, excRel]

/-- Global-initialization case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevSetGlobal {C D F : Type} (index : Nat) (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.globOp (.setGlobal index)) ys t with
    | .err err2 => ∃ err1, doApp (.globOp (.setGlobal index)) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.globOp (.setGlobal index)) xs s = .val (x, s1) := by
  obtain ⟨simple, stateProps, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyGlobal, excRel]
  | @cons x y _ _ head tail =>
    cases tail with
    | cons next rest => simp [doApp, applyGlobal, excRel]
    | nil =>
      have globals := (stateProps.2.2.2.2.1 s t states).2.2
      have slots := globalLookup vr globals index
      have updated : sr { s with globals := s.globals.set index (some x) }
          { t with globals := t.globals.set index (some y) } :=
        stateProps.2.2.2.2.2.2.2.2.2 s t _ _ ⟨states, relatedSet globals index _ _ head⟩
      have unit := unitRelated vr simple
      cases l : getGlobal index s.globals <;> cases r : getGlobal index t.globals <;>
        simp_all [optionRel, doApp, applyGlobal, excRel]
      all_goals rename_i a b; cases a <;> cases b <;> simp_all

/-- Global-allocation case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevAllocGlobal {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.globOp .allocGlobal) ys t with
    | .err err2 => ∃ err1, doApp (.globOp .allocGlobal) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.globOp .allocGlobal) xs s = .val (x, s1) := by
  obtain ⟨simple, stateProps, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyGlobal, excRel]
  | @cons x y _ _ head tail =>
    cases tail with
    | cons next rest => simp [doApp, applyGlobal, excRel]
    | nil =>
      have view := simpleValRel_view vr simple x y head
      cases view with
      | number n =>
        by_cases neg : n < 0
        · simp [doApp, applyGlobal, neg, excRel]
        · have globals := (stateProps.2.2.2.2.1 s t states).2.2
          have blanks : List.Forall₂ (optionRel vr) (List.replicate n.toNat none)
              (List.replicate n.toNat none) := by
            induction n.toNat with
            | zero => exact .nil
            | succ k ih => exact .cons trivial ih
          have updated := stateProps.2.2.2.2.2.2.2.2.2 s t _ _
            ⟨states, List.rel_append globals blanks⟩
          have unit := unitRelated vr simple
          simp [doApp, applyGlobal, neg, updated, unit]
      | word64 | byteVector | refPtr | block | closureClosure | closureRec | recClosure | recRec =>
        simp [doApp, applyGlobal, excRel]

end Flapjack.Compiler.Backend.ClosProps.PrimitiveGlobal
