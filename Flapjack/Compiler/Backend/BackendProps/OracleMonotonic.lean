import Flapjack.Compiler.Backend.BackendProps.StateCompiler
import Mathlib.Data.Set.Lattice

/-! Stateful compiler-oracle ordering properties. -/
namespace Flapjack.Compiler.Backend.BackendProps

/-- All identifiers in later oracle entries exceed those in earlier entries. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "oracle_monotonic_def"]
def oracleMonotonic {A B : Type} (names : A → Set B) (relation : B → B → Prop)
    (initial : Set B) (oracle : Nat → A) : Prop :=
  (∀ i j x y, i < j → x ∈ names (oracle i) → y ∈ names (oracle j) → relation x y) ∧
  (∀ i x y, x ∈ initial → y ∈ names (oracle i) → relation x y)

/-- Each entry's next compiler state equals the next oracle entry's state. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "is_state_oracle_def"]
def isStateOracle {S C P Q : Type} (compile : S → P → S × Q)
    (oracle : Nat → (S × C) × P) : Prop :=
  ∀ n, (oracle (n + 1)).1.1 = (compile (oracle n).1.1 (oracle n).2).1

/-- An invariant and a monotone state bound order generated oracle identifiers. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "oracle_monotonic_state_with_inv"]
theorem oracleMonotonic_stateWithInv {S C P Q : Type}
    (Pstate : S → Prop) (bound : S → Nat) (names : C × Q → Set Nat)
    (initial : Set Nat) (compile : S → P → S × Q) (oracle : Nat → (S × C) × P)
    (premises : Pstate (oracle 0).1.1 ∧
      (∀ x ∈ initial, x < bound (oracle 0).1.1) ∧
      (∀ st prog st' prog', compile st prog = (st', prog') ∧ Pstate st →
        Pstate st' ∧ bound st ≤ bound st' ∧
          ∀ cfg x, x ∈ names (cfg, prog') → bound st ≤ x ∧ x < bound st') ∧
      isStateOracle compile oracle) :
    oracleMonotonic names (· < ·) initial (stateCo compile oracle) := by
  obtain ⟨init, initialBound, step, state⟩ := premises
  let current : Nat → S := fun i => (oracle i).1.1
  have stage : ∀ i, Pstate (current i) ∧ bound (current i) ≤ bound (current (i + 1)) ∧
      ∀ x ∈ names (stateCo compile oracle i), bound (current i) ≤ x ∧ x < bound (current (i + 1)) := by
    have inv : ∀ i, Pstate (current i) := by
      intro i
      induction i with
      | zero => exact init
      | succ i ih =>
        have h := step (current i) (oracle i).2 (compile (current i) (oracle i).2).1
          (compile (current i) (oracle i).2).2 ⟨by cases compile (current i) (oracle i).2; rfl, ih⟩
        simpa [current, isStateOracle] using (state i ▸ h.1)
    intro i
    have h := step (current i) (oracle i).2 (compile (current i) (oracle i).2).1
      (compile (current i) (oracle i).2).2 ⟨by cases compile (current i) (oracle i).2; rfl, inv i⟩
    have nextEq : current (i + 1) = (compile (current i) (oracle i).2).1 := state i
    refine ⟨inv i, ?_, ?_⟩
    · simpa [nextEq] using h.2.1
    · intro x mem
      have bounds := h.2.2 (oracle i).1.2 x mem
      simpa [stateCo, current, nextEq] using bounds
  have monotone : ∀ i j, i ≤ j → bound (current i) ≤ bound (current j) := by
    intro i j le
    induction le with
    | refl => exact Nat.le_refl _
    | @step j le ih => exact Nat.le_trans ih (stage j).2.1
  constructor
  · intro i j x y lt xmem ymem
    have xbound := (stage i).2.2 x xmem
    have ybound := (stage j).2.2 y ymem
    have middle := monotone (i + 1) j (by omega)
    omega
  · intro i x y xmem ymem
    have xbound := initialBound x xmem
    change x < bound (current 0) at xbound
    have ybound := (stage i).2.2 y ymem
    have middle := monotone 0 i (Nat.zero_le i)
    omega

end Flapjack.Compiler.Backend.BackendProps
