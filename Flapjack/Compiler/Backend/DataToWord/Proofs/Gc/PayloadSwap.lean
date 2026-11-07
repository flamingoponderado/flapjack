import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Representation

/-! Payload replacement used by the copying collector's scan loop. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Replacing the address list by an equally long list preserves a successful
header and produces the corresponding mapped word payload. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_payload_swap"
  (words_as_type_indexed_bitvec)]
theorem wordPayload_swap {headerWidth : Nat} {payloadWidth : Nat}
    [NeZero headerWidth] [NeZero payloadWidth]
    (original replacement : List (HeapAddress (WordLocW payloadWidth))) (tag : HeapTag)
    (raw : List (WordLocW payloadWidth)) (conf : Config) (header : BitVec headerWidth)
    (encoded : wordPayload original original.length tag raw conf =
      (header, original.map (wordAddr conf), true)) (length : replacement.length = original.length) :
    wordPayload replacement original.length tag raw conf =
      (header, replacement.map (wordAddr conf), true) := by
  cases tag <;> simp [wordPayload] at encoded ⊢
  all_goals simp_all
  case thunkTag => simpa [encoded.2.2] using encoded.1
  case numTag =>
    obtain ⟨_, _, ⟨originalNil, _⟩, _⟩ := encoded
    subst original
    simp_all
  case word64Tag =>
    obtain ⟨_, _, ⟨originalNil, _⟩, _⟩ := encoded
    subst original
    simp_all

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
