module

public import Flapjack.Compiler.Backend.BackendProps.OracleMonotonicInit

@[expose] public section

/-! Oracle monotonicity when no state invariant is needed. -/
namespace Flapjack.Compiler.Backend.BackendProps

/-- State-bound growth orders the identifiers emitted by an oracle. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "oracle_monotonic_state"]
theorem oracleMonotonic_state {S C P Q : Type}
    (initial : Set Nat) (oracle : Nat → (S × C) × P)
    (compile : S → P → S × Q) (names : C × Q → Set Nat) (bound : S → Nat)
    (premises : (∀ x ∈ initial, x < bound (oracle 0).1.1) ∧
      (∀ st prog st' prog', compile st prog = (st', prog') →
        bound st ≤ bound st' ∧ ∀ cfg x, x ∈ names (cfg, prog') →
          bound st ≤ x ∧ x < bound st') ∧
      isStateOracle compile oracle) :
    oracleMonotonic names (· < ·) initial (stateCo compile oracle) := by
  obtain ⟨initialBound, step, oracleState⟩ := premises
  apply oracleMonotonic_stateWithInv (fun _ => True) bound names initial compile oracle
  refine ⟨trivial, initialBound, ?_, oracleState⟩
  intro st prog st' prog' h
  exact ⟨trivial, step st prog st' prog' h.1⟩

/-- An initial compilation step supplies the initial identifier bound. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "oracle_monotonic_state_init"]
theorem oracleMonotonic_stateInit {S C P Q : Type}
    (compile : S → P → S × Q) (st0 : S) (prog0 : P) (st : S) (prog : Q)
    (initial : Set Nat) (names : C × Q → Set Nat) (cfg : C)
    (oracle : Nat → (S × C) × P) (bound : S → Nat)
    (premises : compile st0 prog0 = (st, prog) ∧ initial ⊆ names (cfg, prog) ∧
      (oracle 0).1.1 = st ∧
      (∀ st prog st' prog', compile st prog = (st', prog') →
        bound st ≤ bound st' ∧ ∀ cfg x, x ∈ names (cfg, prog') →
          bound st ≤ x ∧ x < bound st') ∧
      isStateOracle compile oracle) :
    oracleMonotonic names (· < ·) initial (stateCo compile oracle) := by
  obtain ⟨compiled, subset, initialState, step, oracleState⟩ := premises
  apply oracleMonotonic_stateWithInvInit compile st0 prog0 st prog initial names cfg oracle
    (fun _ => True) bound
  refine ⟨compiled, trivial, subset, initialState, ?_, oracleState⟩
  intro st prog st' prog' h
  exact ⟨trivial, step st prog st' prog' h.1⟩

end Flapjack.Compiler.Backend.BackendProps
