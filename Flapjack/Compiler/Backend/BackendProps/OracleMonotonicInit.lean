module

public import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic

@[expose] public section

/-! Oracle monotonicity after an initial compilation step. -/
namespace Flapjack.Compiler.Backend.BackendProps

/-- An initial compilation step supplies the initial identifier bound. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "oracle_monotonic_state_with_inv_init"]
theorem oracleMonotonic_stateWithInvInit {S C P Q : Type}
    (compile : S → P → S × Q) (st0 : S) (prog0 : P) (st : S) (prog : Q)
    (initial : Set Nat) (names : C × Q → Set Nat) (cfg : C)
    (oracle : Nat → (S × C) × P) (Pstate : S → Prop) (bound : S → Nat)
    (premises : compile st0 prog0 = (st, prog) ∧ Pstate st0 ∧
      initial ⊆ names (cfg, prog) ∧ (oracle 0).1.1 = st ∧
      (∀ st prog st' prog', compile st prog = (st', prog') ∧ Pstate st →
        Pstate st' ∧ bound st ≤ bound st' ∧
          ∀ cfg x, x ∈ names (cfg, prog') → bound st ≤ x ∧ x < bound st') ∧
      isStateOracle compile oracle) :
    oracleMonotonic names (· < ·) initial (stateCo compile oracle) := by
  obtain ⟨compiled, invariant, subset, initialState, step, oracleState⟩ := premises
  have initialStep := step st0 prog0 st prog ⟨compiled, invariant⟩
  apply oracleMonotonic_stateWithInv Pstate bound names initial compile oracle
  refine ⟨?_, ?_, step, oracleState⟩
  · simpa [initialState] using initialStep.1
  · intro x member
    simpa [initialState] using (initialStep.2.2 cfg x (subset member)).2

end Flapjack.Compiler.Backend.BackendProps
