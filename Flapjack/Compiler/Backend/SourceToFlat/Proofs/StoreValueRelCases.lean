import Flapjack.Compiler.Backend.SourceToFlat.Proofs.StateRel

/-! Case equations for the factored source-to-flat store relation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.SemanticPrimitivesHOL

/-- A non-inductive view of the four store-value cases in the original
source-to-flat proof. The value relation is still preliminary, so this view
is Flapjack infrastructure rather than a reviewed HOL declaration. -/
def StoreValueRelShape (genv : GlobalEnv) : StoreValue Value → StoreValue FlatSem.Value → Prop
  | .refv source, .refv flat => ValueRel genv source flat
  | .w8array source, .w8array flat => source = flat
  | .varray source, .varray flat => List.Forall₂ (ValueRel genv) source flat
  | .thunk sourceMode source, .thunk flatMode flat =>
      sourceMode = flatMode ∧ ValueRel genv source flat
  | _, _ => False

/-- The factored inductive relation has exactly the four store-value cases,
including rejection of unlike constructors and unequal thunk modes. -/
theorem storeValueRel_iff_shape (genv : GlobalEnv) (source : StoreValue Value)
    (flat : StoreValue FlatSem.Value) :
    StoreValueRel genv source flat ↔ StoreValueRelShape genv source flat := by
  constructor
  · intro related
    cases related <;> simp_all [StoreValueRelShape]
  · cases source <;> cases flat <;> simp only [StoreValueRelShape]
    all_goals intro related
    all_goals first
      | contradiction
      | exact StoreValueRel.refv related
      | exact StoreValueRel.varray related
      | cases related; exact StoreValueRel.w8array _
      | obtain ⟨rfl, h⟩ := related; exact StoreValueRel.thunk _ h

/-- Pointwise lifting of the case equations to the source and flat stores. -/
theorem storeValueRel_list_iff_shape (genv : GlobalEnv)
    (source : List (StoreValue Value)) (flat : List (StoreValue FlatSem.Value)) :
    List.Forall₂ (StoreValueRel genv) source flat ↔
      List.Forall₂ (StoreValueRelShape genv) source flat := by
  constructor
  · intro related
    induction related with
    | nil => exact .nil
    | cons head _ ih => exact .cons ((storeValueRel_iff_shape genv _ _).mp head) ih
  · intro related
    induction related with
    | nil => exact .nil
    | cons head _ ih => exact .cons ((storeValueRel_iff_shape genv _ _).mpr head) ih

/-- The state relation can be read directly using the original four store
cases, the reserved first flat entry, equal clocks, and equal FFI states. -/
theorem stateRel_iff_store_shape {C F : Type} (genv : GlobalEnv)
    (source : State F) (flat : FlatSem.State C F) :
    StateRel genv source flat ↔
      flat.refs ≠ [] ∧ List.Forall₂ (StoreValueRelShape genv) source.refs flat.refs.tail ∧
        source.clock = flat.clock ∧ source.ffi = flat.ffi := by
  rw [stateRel_iff, storeValueRel_list_iff_shape]

end Flapjack.Compiler.Backend.SourceToFlat
