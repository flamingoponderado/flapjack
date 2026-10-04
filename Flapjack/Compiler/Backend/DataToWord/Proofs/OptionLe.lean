import Flapjack.Compiler.Backend.BackendProps

/-!
# `data_to_wordProof`: `option_le_SOME`

Counterpart of `cakeml/compiler/backend/proofs/data_to_wordProofScript.sml`'s
`option_le_SOME` (lines 1779-1783), the `option_le` inversion cited by the Pancake
top-level theorem's resource-bound reasoning.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs

open Flapjack.Compiler.Backend.BackendProps

/-- Full original `option_le_SOME`:
`option_le x (SOME n) ⇔ ∃m. x = SOME m ∧ m ≤ n`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "option_le_SOME"]
theorem optionLe_SOME (x : Option Nat) (n : Nat) :
    optionLe x (some n) ↔ ∃ m, x = some m ∧ m ≤ n := by
  rcases x with _ | m <;> simp [optionLe]

end Flapjack.Compiler.Backend.DataToWord.Proofs
