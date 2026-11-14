module

public import Flapjack.FiniteMap.BroadCodec
public import Flapjack.Compiler.Backend.ClosNumber.Proofs.EvaluateCases

@[expose] public section

/-! Source-shaped thunk-update prerequisite for closure numbering. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open Flapjack Flapjack.Compiler.Backend.ClosSem

namespace ThunkUpdatePort
/-- The closure state has the canonical finite-map representation. -/
theorem holFmapAsFiniteSupportRelationWitness_State {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Canonical codec for the existential reference-map witness. -/
theorem holFmapAsFiniteSupportExistentialWitness_rel_update_thunk_targetRefs
    (targetRefs : HolFiniteMapExact Nat (Ref Value)) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad targetRefs)).lookup = targetRefs.lookup ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad targetRefs)).finiteSupport = targetRefs.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad targetRefs) = targetRefs := by
  cases targetRefs
  exact ⟨rfl, rfl, rfl⟩

/-- Related states and thunk results produce related updated stores. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "rel_update_thunk"
  (fmap_as_finite_support_relation := [State.refs, State.code, sourceRefs])
  (fmap_as_finite_support_existentials := [targetRefs])]
theorem rel_update_thunk {C F : Type}
    (source : Flapjack.Compiler.Backend.ClosSem.State (Nat × C) F)
    (target : Flapjack.Compiler.Backend.ClosSem.State C F)
    (flag : Bool) (ptr : Nat) (values nextValues : List Value)
    (sourceRefs : HolFiniteMapExact Nat (Ref Value))
    (h : StateRel source target ∧ List.Forall₂ (ValueRel source.maxApp) values nextValues ∧
      updateThunk [.refPtr flag ptr] source.refs values = some sourceRefs) :
    ∃ targetRefs : HolFiniteMapExact Nat (Ref Value),
      updateThunk [.refPtr flag ptr] target.refs nextValues = some targetRefs ∧
      StateRel { source with refs := sourceRefs } { target with refs := targetRefs } := by
  have pointers : List.Forall₂ (ValueRel source.maxApp) [.refPtr flag ptr] [.refPtr flag ptr] :=
    .cons (.refPtr flag ptr) .nil
  have result := updateThunk_related source target _ _ values nextValues pointers h.2.1 h.1
  simpa only [h.2.2] using result
end ThunkUpdatePort
end Flapjack.Compiler.Backend.ClosNumber
