module

public import Flapjack.Misc.Multiword

@[expose] public section

/-! The multiword facts of `cakeml/compiler/backend/proofs/word_bignumProofScript.sml`
that speak about the tagged `n2mw`/`i2mw` encodings. -/

namespace Flapjack.Compiler.Backend.WordBignum

open Flapjack

/-- Flapjack-only helper: the little-endian encoding of a natural number is
empty exactly at zero. It states HOL's `n2mw` clause split once, so the tagged
`i2mw_NOT_NIL` below does not need to unfold the recursive definition. -/
theorem n2mw_ne_nil {width : Nat} [NeZero width] (n : Nat) :
    Misc.Multiword.n2mw (width := width) n ≠ [] ↔ n ≠ 0 := by
  unfold Misc.Multiword.n2mw
  split
  · rename_i h
    simp [h]
  · rename_i h
    exact ⟨fun _ => h, fun _ => by simp⟩

/-- HOL `i2mw_NOT_NIL` (`word_bignumProofScript.sml:2268`): the magnitude word
list of `i2mw` is empty exactly when the integer is zero. HOL's empty list is
annotated at the word list type, as in the source (`[] : α word list`). -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "i2mw_NOT_NIL"
  (words_as_type_indexed_bitvec)]
theorem i2mw_snd_ne_nil {width : Nat} [NeZero width] (i : Int) :
    (Misc.Multiword.i2mw i).2 ≠ ([] : List (BitVec width)) ↔ i ≠ 0 := by
  unfold Misc.Multiword.i2mw
  simp only [n2mw_ne_nil]
  omega

end Flapjack.Compiler.Backend.WordBignum
