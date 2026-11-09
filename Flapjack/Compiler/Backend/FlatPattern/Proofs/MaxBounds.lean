module

public import Flapjack.HolRef

@[expose] public section

/-! Arithmetic bounds used in the flat-pattern correctness proof. -/
namespace Flapjack.Compiler.Backend.FlatPattern

/-- Adding a common offset to a maximum preserves a strict upper bound. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "MAX_ADD_LESS"]
theorem maxAddLess (i j k l : Nat) :
    max i j + k < l ↔ i + k < l ∧ j + k < l := by
  omega

/-- A strict lower bound on an offset maximum holds on at least one side. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "LESS_MAX_ADD"]
theorem lessMaxAdd (i j k l : Nat) :
    l < max i j + k ↔ l < i + k ∨ l < j + k := by
  omega

/-- Adding a common offset to a maximum preserves an upper bound. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "MAX_ADD_LE"]
theorem maxAddLe (i j k l : Nat) :
    max i j + k ≤ l ↔ i + k ≤ l ∧ j + k ≤ l := by
  omega

end Flapjack.Compiler.Backend.FlatPattern
