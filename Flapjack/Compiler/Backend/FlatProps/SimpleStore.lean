import Flapjack.Compiler.Backend.FlatProps.SimpleRelations
import Mathlib.Data.List.Forall2

/-! Store operations under simple flat state relations. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.SemanticPrimitivesHOL (Store StoreValue storeLookup storeAssign storeAlloc storeValueSameType)
open Flapjack.SemanticPrimitivesProps

/-- Successful assignment is simulated by any simple state relation. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_state_rel_store_assign"]
theorem simpleStateRel_storeAssign {C D F : Type} (valueRel : FlatSem.Value → FlatSem.Value → Prop)
    (stateRel : FlatSem.State C F → FlatSem.State D F → Prop)
    (index : Nat) (x : StoreValue FlatSem.Value) (source : FlatSem.State C F)
    (sourceRefs : Store FlatSem.Value) (target : FlatSem.State D F) (y : StoreValue FlatSem.Value)
    (premises : simpleStateRel valueRel stateRel ∧
      storeAssign index x source.refs = some sourceRefs ∧
      stateRel source target ∧ storeValueRel valueRel x y) :
    ∃ targetRefs, storeAssign index y target.refs = some targetRefs ∧
      stateRel { source with refs := sourceRefs } { target with refs := targetRefs } := by
  obtain ⟨simple, assigned, states, values⟩ := premises
  obtain ⟨targetRefs, assigned', refs⟩ := storeAssign_related (simple.1 source target states) index values assigned
  exact ⟨targetRefs, assigned', simple.2.1 source target sourceRefs targetRefs ⟨states, refs⟩⟩

/-- Allocation preserves a simple state relation and the allocated index. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_state_rel_store_alloc"]
theorem simpleStateRel_storeAlloc {C D F : Type} (valueRel : FlatSem.Value → FlatSem.Value → Prop)
    (stateRel : FlatSem.State C F → FlatSem.State D F → Prop)
    (x : StoreValue FlatSem.Value) (source : FlatSem.State C F)
    (sourceRefs : Store FlatSem.Value) (index : Nat) (target : FlatSem.State D F) (y : StoreValue FlatSem.Value)
    (premises : simpleStateRel valueRel stateRel ∧
      storeAlloc x source.refs = (sourceRefs, index) ∧
      stateRel source target ∧ storeValueRel valueRel x y) :
    ∃ targetRefs, storeAlloc y target.refs = (targetRefs, index) ∧
      stateRel { source with refs := sourceRefs } { target with refs := targetRefs } := by
  obtain ⟨simple, allocated, states, values⟩ := premises
  have eq : source.refs ++ [x] = sourceRefs ∧ source.refs.length = index := by
    simpa [storeAlloc] using allocated
  obtain ⟨rfl, rfl⟩ := eq
  have refs := simple.1 source target states
  refine ⟨target.refs ++ [y], ?_, ?_⟩
  · simp [storeAlloc, ← List.Forall₂.length_eq refs]
  · exact simple.2.1 source target _ _ ⟨states, List.rel_append refs (.cons values .nil)⟩

/-- Store lookup in related states yields related entries at the same index. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_state_rel_store_lookup"]
theorem simpleStateRel_storeLookup {C D F : Type} (valueRel : FlatSem.Value → FlatSem.Value → Prop)
    (stateRel : FlatSem.State C F → FlatSem.State D F → Prop)
    (index : Nat) (source : FlatSem.State C F) (x : StoreValue FlatSem.Value)
    (target : FlatSem.State D F)
    (premises : simpleStateRel valueRel stateRel ∧
      storeLookup index source.refs = some x ∧ stateRel source target) :
    ∃ y, storeLookup index target.refs = some y ∧ storeValueRel valueRel x y := by
  obtain ⟨simple, found, states⟩ := premises
  exact storeValueRel_lookup (simple.1 source target states) index x found

end Flapjack.Compiler.Backend.FlatProps
