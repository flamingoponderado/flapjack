import Flapjack.Misc.Alignment

/-! `data_to_word_gcProofScript.sml` opening word lemmas (lines 38-115). Only
`lsr_lsl`, cited by the Pancake-to-target proof, is ported so far. HOL's `>>>`
and `<<` on words are Lean's `BitVec` logical shifts `>>>` and `<<<`. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

open Flapjack

/-- Full original `lsr_lsl` (`data_to_word_gcProofScript.sml:77-81`):
`∀w n. aligned n w ⇒ (w >>> n << n = w)`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "lsr_lsl"
  (words_as_type_indexed_bitvec)]
theorem lsrLsl {width : Nat} [NeZero width] :
    ∀ (w : BitVec width) (n : Nat), holAligned n w = true → (w >>> n) <<< n = w := by
  intro w n h
  simp only [holAligned, decide_eq_true_eq] at h
  rw [← holAlign_eq_shift, h]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
