module

public import Flapjack.Byte.SetByte

@[expose] public section

/-! Bounded byte updates to a word, following the HOL byte library. -/
namespace Flapjack.HolByte

/-- Update at most `count` bytes, retaining the original word for missing
input and applying updates in the source's recursive order. -/
@[hol "HOL/src/n-bit/byteScript.sml" "bytes_to_word_def"
  (words_as_type_indexed_bitvec)]
def bytesToWord {width : Nat} [NeZero width] :
    Nat → BitVec width → List (BitVec 8) → BitVec width → Bool → BitVec width
  | 0, _, _, word, _ => word
  | _ + 1, _, [], word, _ => word
  | count + 1, address, byte :: bytes, word, bigEndian =>
      setByte address byte (bytesToWord count (address + 1) bytes word bigEndian) bigEndian

end Flapjack.HolByte
