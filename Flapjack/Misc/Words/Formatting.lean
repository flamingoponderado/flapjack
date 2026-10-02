import Flapjack.Misc.ASCIInumbers

/-! Counterpart of pinned wordsScript word-to-character conversion. -/
namespace Flapjack
open Basis.Pure.MlString

/-- Complete original word conversion with arbitrary base and character function. -/
@[hol "HOL/src/n-bit/wordsScript.sml" "w2s_def" (words_as_type_indexed_bitvec)]
def holW2s {width : Nat} [NeZero width] (b : Nat) (f : Nat → HolChar)
    (w : BitVec width) : List HolChar := holN2s b f w.toNat

/-- Original hexadecimal wrapper at every positive input word dimension. -/
@[hol "HOL/src/n-bit/wordsScript.sml" "word_to_hex_string_def" (words_as_type_indexed_bitvec)]
def holWordToHexString {width : Nat} [NeZero width] : BitVec width → List HolChar :=
  holW2s 16 holHex

end Flapjack
