module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveMemory

@[expose] public section

/-! Foreign-function calls in the generic closure primitive simulation. -/
namespace Flapjack.Compiler.Backend.ClosProps.PrimitiveFfi
open ClosSem Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.ClosProps.PrimitiveMemory

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- FFI case of the reverse primitive simulation. Related states call the
same external function with the same configuration and bytes. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevFfi {C D F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (vr : Value → Value → Prop) (sr : State C F → State D F → Prop)
    (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.ffi name) ys t with
    | .err err2 => ∃ err1, doApp (.ffi name) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.ffi name) xs s = .val (x, s1) := by
  obtain ⟨simple, stateProps, states, values⟩ := h
  cases values with
  | nil => simp [doApp, excRel]
  | @cons x1 y1 _ _ first tail =>
    cases tail with
    | nil => simp [doApp, excRel]
    | @cons x2 y2 _ _ second tail =>
      cases tail with
      | cons third rest => simp [doApp, excRel]
      | nil =>
        have firstView := simpleValRel_view vr simple x1 y1 first
        have secondView := simpleValRel_view vr simple x2 y2 second
        cases firstView <;> cases secondView <;> simp_all [doApp, excRel]
        rename_i configuration flag ptr
        have lookup := relatedRefs vr sr stateProps s t states ptr
        cases l : s.refs.lookup ptr <;> cases r : t.refs.lookup ptr <;> simp_all [optionRel]
        rename_i a b
        cases a <;> cases b <;> simp_all [refRel]
        rename_i bytes
        have ffiEq := (stateProps.2.2.2.2.1 s t states).1
        rw [← ffiEq]
        cases ffiRun : callFFIHOL s.ffi (.extCall name) configuration bytes with
        | final event => simp
        | ret ffi updated =>
          have refs := stateProps.2.2.2.2.2.2.1 updated s t ptr states
          have next := stateProps.2.2.2.2.2.1 ffi _ _ refs
          have unit : vr unitValue unitValue := (simple.2.1 _ [] _).2 ⟨[], rfl, .nil⟩
          simpa using And.intro unit next

end Flapjack.Compiler.Backend.ClosProps.PrimitiveFfi
