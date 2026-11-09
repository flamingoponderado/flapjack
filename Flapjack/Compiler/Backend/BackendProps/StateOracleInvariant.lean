module

public import Flapjack.Compiler.Backend.BackendProps.StateCompiler

@[expose] public section

/-! Invariants of the incremental compiler's oracle-state sequence. -/
namespace Flapjack.Compiler.Backend.BackendProps

/-- An invariant preserved by each incremental step holds at every oracle state. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "state_orac_states_inv"]
theorem stateOracStates_inv {S Program Output : Type} (P : S → Prop)
    (st : S) (fInc : S → Program → S × Output) (orac : Nat → Program) (i : Nat)
    (premises : P st ∧ ∀ st prog st' prog', fInc st prog = (st', prog') ∧ P st → P st') :
    P (stateOracStates fInc st orac i) := by
  induction i with
  | zero => exact premises.1
  | succ n ih =>
    exact premises.2 _ _ _ _ ⟨Prod.eta _, ih⟩

end Flapjack.Compiler.Backend.BackendProps
