import Flapjack.Compiler.Backend.BvlToBvi.Proofs.ApplyOk

/-! Thunk-operation cases of BVL well-formedness preservation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value Ref State doApp)

namespace ThunkCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end ThunkCarrier

/-- Replacing or allocating a thunk holding a valid value preserves the
source state invariant. -/
theorem stateOk_updateThunk {C F : Type} (s : State C F) (key : Nat)
    (mode : AstHOL.ThunkMode) (value : Value) (ok : stateOk s)
    (valueOk : bvOk s.refs value) :
    stateOk { s with refs := s.refs.updateEq (key, .thunk mode value) } := by
  let refs := s.refs.updateEq (key, .thunk mode value)
  have subset : ∀ k, s.refs.lookup k ≠ none → refs.lookup k ≠ none := by
    intro k present
    exact BvlProps.refs_update_mono s.refs key k (.thunk mode value) present
  constructor
  · intro item member
    have original := ok.1 item member
    cases item with
    | none => trivial
    | some value => exact bvOk_domain_mono s.refs value refs original subset
  · intro k
    by_cases eq : k = key
    · simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq, if_true]
      exact bvOk_domain_mono s.refs value refs valueOk subset
    · have prior := ok.2 k
      have lookup : refs.lookup k = s.refs.lookup k := by
        simp [refs, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq]
      rw [lookup]
      cases h : s.refs.lookup k with
      | none => trivial
      | some ref =>
        cases ref with
        | valueArray values =>
          simp only [h] at prior
          exact bvOkList_domain_mono s.refs values refs prior subset
        | thunk _ value =>
          simp only [h] at prior
          exact bvOk_domain_mono s.refs value refs prior subset
        | _ => trivial

/-- Thunk-allocation and update cases of primitive application. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_app_ok"
  (fmap_as_finite_support := [refs])]
theorem doApp_ok_thunk {C F : Type} (op : AstHOL.ThunkOp)
    (args env : List Value) (s t : Flapjack.Compiler.Backend.BvlSem.State C F) (result : Value)
    (ok : stateOk s) (argsOk : bvOkList s.refs args)
    (run : doApp (.thunkOp op) args s = .val (result, t)) :
    stateOk t ∧ bvOk t.refs result ∧ (bvOkList s.refs env → bvOkList t.refs env) := by
  have subset := BvlProps.doApp_refs_mono (.thunkOp op) args s t result run
  have preserve := fun envOk => bvOkList_domain_mono s.refs env t.refs envOk subset
  simp only [doApp] at run
  repeat' first | split at run | contradiction
  all_goals simp_all [bvOk, bvOkList, BvlSem.unitValue]
  all_goals rcases run with ⟨rfl, rfl⟩
  all_goals constructor
  all_goals try exact stateOk_updateThunk s _ _ _ ok argsOk
  all_goals simp [bvOk, bvOkList, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
