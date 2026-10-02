import Flapjack.Byte.SetByte

namespace Flapjack.HolByte

/-- Literal recursive HOL decoder: the head byte is written after the tail,
and the address increments as a word. Repeated byte lanes therefore retain
the earlier byte; narrow dimensions and wrapped addresses are not excluded. -/
@[hol "HOL/src/n-bit/byteScript.sml" "word_of_bytes_def"
  (words_as_type_indexed_bitvec)]
def wordOfBytes {width : Nat} [NeZero width] (bigEndian : Bool)
    (address : BitVec width) : List (BitVec 8) → BitVec width
  | [] => 0
  | byte :: rest => setByte address byte (wordOfBytes bigEndian (address + 1) rest) bigEndian

end Flapjack.HolByte
