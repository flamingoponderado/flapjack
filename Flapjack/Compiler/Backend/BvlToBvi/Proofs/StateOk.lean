import Flapjack.Compiler.Backend.BvlToBvi.Proofs.Refs

/-! Source-value well-formedness for BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs

/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness

/-- All globals and values inside value arrays or thunks refer to allocated
source cells. Mutable blocks and byte arrays have no additional condition. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "state_ok_def"
  (fmap_as_finite_support := [refs])]
def stateOk {C F : Type} (s : Flapjack.Compiler.Backend.BvlSem.State C F) : Prop :=
  (∀ item ∈ s.globals, match item with
    | none => True
    | some value => bvOk s.refs value) ∧
  ∀ key, match s.refs.lookup key with
    | some (.valueArray values) => bvOkList s.refs values
    | some (.thunk _ value) => bvOk s.refs value
    | _ => True

/-- Clock decrement does not affect source value well-formedness. This is the
well-formedness part of the source's local clock lemma. -/
theorem stateOk_decClock {C F : Type} (n : Nat) (s : BvlSem.State C F) :
    stateOk (BvlSem.decClock n s) ↔ stateOk s := Iff.rfl

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
