module

public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.RefRelocate

@[expose] public section

/-! State-relation preservation for the original allocation cases. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value Ref)

namespace AllocationCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_State {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness

/-- Canonical BVI reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end AllocationCarrier

/-- Fresh paired cells preserve the relation under the source's explicit
function update. This is shared Flapjack infrastructure for the two source
allocation lemmas below. -/
private theorem stateRel_insertUpdated {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (pp qq : Nat) (cell : Ref Value)
    (related : stateRel relocate source target) (ok : stateOk source)
    (sourceFresh : source.refs.lookup pp = none) (targetFresh : target.refs.lookup qq = none) :
    stateRel (Function.update relocate pp qq)
      { source with refs := source.refs.updateEq (pp, cell) }
      { target with refs := target.refs.updateEq (qq, adjustRef (Function.update relocate pp qq) cell) } := by
  have agree : ∀ key, source.refs.lookup key ≠ none →
      relocate key = Function.update relocate pp qq key := by
    intro key present
    have ne : key ≠ pp := by
      intro eq
      subst key
      exact present sourceFresh
    simp [Function.update, ne]
  have relocated := stateRel_relocate relocate (Function.update relocate pp qq) source target related ok agree
  have fresh : target.refs.lookup (Function.update relocate pp qq pp) = none := by
    simpa using targetFresh
  have inserted := stateRel_insertFresh (Function.update relocate pp qq) source target pp cell relocated fresh
  simpa using inserted

/-- Fresh byte arrays extend related states with the updated relocation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "state_rel_add_bytearray"
  (fmap_as_finite_support_relation := [State.refs, BviState.refs])]
theorem stateRel_addByteArray {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (pp qq : Nat) (flag : Bool) (bytes : List (BitVec 8))
    (premises : stateRel relocate source target ∧ stateOk source ∧
      source.refs.lookup pp = none ∧ target.refs.lookup qq = none) :
    stateRel (Function.update relocate pp qq)
      { source with refs := source.refs.updateEq (pp, .byteArray flag bytes) }
      { target with refs := target.refs.updateEq (qq, .byteArray flag bytes) } := by
  rcases premises with ⟨related, ok, sourceFresh, targetFresh⟩
  simpa [adjustRef] using stateRel_insertUpdated relocate source target pp qq
    (.byteArray flag bytes) related ok sourceFresh targetFresh

/-- Fresh thunks extend related states with the updated relocation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "state_rel_add_thunk"
  (fmap_as_finite_support_relation := [State.refs, BviState.refs])]
theorem stateRel_addThunk {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (pp qq : Nat) (mode : AstHOL.ThunkMode) (value : Value)
    (premises : stateRel relocate source target ∧ stateOk source ∧
      source.refs.lookup pp = none ∧ target.refs.lookup qq = none) :
    stateRel (Function.update relocate pp qq)
      { source with refs := source.refs.updateEq (pp, .thunk mode value) }
      { target with refs := target.refs.updateEq (qq, .thunk mode (adjustBv (Function.update relocate pp qq) value)) } := by
  rcases premises with ⟨related, ok, sourceFresh, targetFresh⟩
  simpa [adjustRef] using stateRel_insertUpdated relocate source target pp qq
    (.thunk mode value) related ok sourceFresh targetFresh

/-- Updating an allocated thunk preserves the state relation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "state_rel_update_thunk"
  (fmap_as_finite_support_relation := [State.refs, BviState.refs])]
theorem stateRel_updateThunk {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (ptr : Nat) (mode : AstHOL.ThunkMode) (value : Value)
    (premises : stateRel relocate source target ∧ stateOk source ∧ source.refs.lookup ptr ≠ none) :
    stateRel relocate
      { source with refs := source.refs.updateEq (ptr, .thunk mode value) }
      { target with refs := target.refs.updateEq (relocate ptr, .thunk mode (adjustBv relocate value)) } := by
  rcases premises with ⟨related, _, present⟩
  simpa [adjustRef] using stateRel_updateExisting relocate source target ptr (.thunk mode value) related present

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
