module

public import Flapjack.HolRef

@[expose] public section

/-! # `join_lemma` of `data_to_word_assignProofScript.sml` -/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

/-- Two implications with a common conclusion combine over a disjunction. HOL's
Boolean variables are Lean propositions. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "join_lemma"]
theorem join_lemma (b1 b2 x : Prop) : (b1 → x) ∧ (b2 → x) → (b1 ∨ b2 → x) := by
  rintro ⟨h1, h2⟩ (h | h)
  · exact h1 h
  · exact h2 h

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
