module

public import Flapjack.Compiler.Backend.FlatProps.ValueBasics
public import Flapjack.SemanticPrimitivesProps.StoreRelation
public import Flapjack.Misc.Option.Rel

@[expose] public section

/-! Generic value and state relations used by flat-semantics proofs. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack Flapjack.Compiler.Backend.FlatSem Flapjack.SemanticPrimitivesProps

/-- A simple value relation preserves closure status and decomposes non-closures. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_val_rel_def"]
def simpleValueRel (relation : Value → Value → Prop) : Prop :=
  (∀ left right, relation left right → (isClosure left ↔ isClosure right)) ∧
  ∀ left right, ¬ isClosure left →
    (relation left right ↔ simpleBasicValRel left right ∧
      List.Forall₂ relation (valueContainerXs left) (valueContainerXs right))

/-- For a non-closure, a simple relation decomposes into its basic shape and contents.
HOL stores `simple_val_rel vr` as an assumption of this theorem; it is
discharged as a premise here and in the typed probe. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_val_rel_rew"]
theorem simpleValueRel_rewrite (relation : Value → Value → Prop)
    (simple : simpleValueRel relation) :
    ∀ left right, ¬ isClosure left →
      (relation left right ↔ simpleBasicValRel left right ∧
        List.Forall₂ relation (valueContainerXs left) (valueContainerXs right)) :=
  simple.2

/-- The non-closure cases of a simple value relation. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_val_rel_simps"]
theorem simpleValueRel_simps (relation : Value → Value → Prop) (lit : Flapjack.AstHOL.Lit)
    (stamp : Option (FlatLang.CtorId × FlatLang.TypeId)) (values : List Value)
    (flag : Bool) (index : Nat) :
    (simpleValueRel relation → ∀ right,
      relation (.litv lit) right ↔ simpleBasicValRel (.litv lit) right ∧
        List.Forall₂ relation (valueContainerXs (.litv lit)) (valueContainerXs right)) ∧
    (simpleValueRel relation → ∀ right,
      relation (.conv stamp values) right ↔ simpleBasicValRel (.conv stamp values) right ∧
        List.Forall₂ relation (valueContainerXs (.conv stamp values)) (valueContainerXs right)) ∧
    (simpleValueRel relation → ∀ right,
      relation (.loc flag index) right ↔ simpleBasicValRel (.loc flag index) right ∧
        List.Forall₂ relation (valueContainerXs (.loc flag index)) (valueContainerXs right)) ∧
    (simpleValueRel relation → ∀ right,
      relation (.vectorv values) right ↔ simpleBasicValRel (.vectorv values) right ∧
        List.Forall₂ relation (valueContainerXs (.vectorv values)) (valueContainerXs right)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro simple right <;>
    apply simpleValueRel_rewrite relation simple <;> simp [isClosure]

/-- Related values have the same closure status under a simple relation. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_val_rel_isClosure"]
theorem simpleValueRel_isClosure (relation : Value → Value → Prop) (left right : Value)
    (premises : simpleValueRel relation ∧ relation left right) :
    isClosure left ↔ isClosure right :=
  premises.1.1 left right premises.2

/-- A simple state relation is stable under related store and global updates
and equal FFI updates. Compiler-state types may differ across the relation. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_state_rel_def"]
def simpleStateRel {C D F : Type} (valueRel : Value → Value → Prop)
    (stateRel : State C F → State D F → Prop) : Prop :=
  (∀ source target, stateRel source target → List.Forall₂ (storeValueRel valueRel) source.refs target.refs) ∧
  (∀ source target sourceRefs targetRefs, stateRel source target ∧
    List.Forall₂ (storeValueRel valueRel) sourceRefs targetRefs →
    stateRel { source with refs := sourceRefs } { target with refs := targetRefs }) ∧
  (∀ source target, stateRel source target → List.Forall₂ (optionRel valueRel) source.globals target.globals) ∧
  (∀ source target sourceGlobals targetGlobals, stateRel source target ∧
    List.Forall₂ (optionRel valueRel) sourceGlobals targetGlobals →
    stateRel { source with globals := sourceGlobals } { target with globals := targetGlobals }) ∧
  (∀ source target, stateRel source target → source.ffi = target.ffi) ∧
  (∀ source target sourceFfi targetFfi, stateRel source target ∧ sourceFfi = targetFfi →
    stateRel { source with ffi := sourceFfi } { target with ffi := targetFfi })

end Flapjack.Compiler.Backend.FlatProps
