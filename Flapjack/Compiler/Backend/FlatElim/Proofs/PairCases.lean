module

public import Flapjack.HolRef

@[expose] public section

/-! Pair equations used in the HOL primitive-application case conversion. -/
namespace Flapjack.Compiler.Backend.FlatElim

@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "pair_case_eq"]
theorem pairCase_eq {α β γ : Type} (x : α × β) (f : α → β → γ) (v : γ) :
    Prod.casesOn x f = v ↔ ∃ x1 x2, x = (x1, x2) ∧ f x1 x2 = v := by
  cases x with
  | mk a b =>
    constructor
    · intro h; exact ⟨a, b, rfl, h⟩
    · rintro ⟨_, _, h, hf⟩; cases h; exact hf

@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "pair_lam_lem"]
theorem pairLet_eq {α β γ : Type} (f : α → β → γ) (v : γ) (z : α × β) :
    (let (x, y) := z; f x y) = v ↔ ∃ x1 x2, z = (x1, x2) ∧ f x1 x2 = v := by
  cases z with
  | mk a b =>
    constructor
    · intro h; exact ⟨a, b, rfl, h⟩
    · rintro ⟨_, _, h, hf⟩; cases h; exact hf

end Flapjack.Compiler.Backend.FlatElim
