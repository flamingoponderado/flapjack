import Flapjack.Compiler.Backend.FlatProps.ValueBasics
import Flapjack.SemanticPrimitivesProps.StoreRelation
import Flapjack.Misc.Option.Rel

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

/-- A simple state relation is stable under related store and global updates
and equal FFI updates. Compiler-state types may differ across the relation. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_state_rel_def"]
def simpleStateRel {C D F : Type} (valueRel : Value → Value → Prop)
    (stateRel : State C F → State D F → Prop) : Prop :=
  (∀ source target, stateRel source target → List.Forall₂ (storeValueRel valueRel) source.refs target.refs) ∧
  (∀ source target sourceRefs targetRefs, stateRel source target →
    List.Forall₂ (storeValueRel valueRel) sourceRefs targetRefs →
    stateRel { source with refs := sourceRefs } { target with refs := targetRefs }) ∧
  (∀ source target, stateRel source target → List.Forall₂ (optionRel valueRel) source.globals target.globals) ∧
  (∀ source target sourceGlobals targetGlobals, stateRel source target →
    List.Forall₂ (optionRel valueRel) sourceGlobals targetGlobals →
    stateRel { source with globals := sourceGlobals } { target with globals := targetGlobals }) ∧
  (∀ source target, stateRel source target → source.ffi = target.ffi) ∧
  (∀ source target sourceFfi targetFfi, stateRel source target → sourceFfi = targetFfi →
    stateRel { source with ffi := sourceFfi } { target with ffi := targetFfi })

end Flapjack.Compiler.Backend.FlatProps
