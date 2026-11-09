import Flapjack.Compiler.Backend.ClosKnown.Proofs.ValueRelation

/-! Boolean values in the known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Relations
open ClosSem

/-- A related target block has the same source tag and related fields. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "v_rel_Block"]
theorem valueRelBlockTarget (c : Config) (g : Spt ValApprox) (v : ClosSem.Value)
    (tag : Nat) (ys : List ClosSem.Value) :
    ValueRel c g v (.block tag ys) ↔
      ∃ xs, v = .block tag xs ∧ List.Forall₂ (ValueRel c g) xs ys := by
  constructor
  · intro rel
    cases rel with
    | block _ xs _ fields => exact ⟨xs, rfl, fields⟩
  · rintro ⟨xs, rfl, fields⟩
    exact .block tag xs ys fields

/-- A Boolean value relates only to the same Boolean in either direction. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "v_rel_Boolv"]
theorem valueRelBool (c : Config) (g : Spt ValApprox) (b : Bool) (v : ClosSem.Value) :
    (ValueRel c g (boolValue b) v ↔ v = boolValue b) ∧
      (ValueRel c g v (boolValue b) ↔ v = boolValue b) := by
  cases b <;> simp [boolValue, valueRelBlock, valueRelBlockTarget, BackendCommon.trueTag, BackendCommon.falseTag]

/-- The unit value relates only to unit in either direction. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "v_rel_Unit"]
theorem valueRelUnit (c : Config) (g : Spt ValApprox) (v : ClosSem.Value) :
    (ValueRel c g unitValue v ↔ v = unitValue) ∧
      (ValueRel c g v unitValue ↔ v = unitValue) := by
  simp [unitValue, valueRelBlock, valueRelBlockTarget]

end Flapjack.Compiler.Backend.ClosKnown.Relations
