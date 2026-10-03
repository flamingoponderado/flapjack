import Flapjack.HolRef

/-! Counterpart of the pinned HOL `src/n-bit/byteScript.sml` byte extraction
and serialization definitions. Arbitrary positive word dimensions and byte
counts are retained, including sub-byte dimensions and cyclic extraction. -/
namespace Flapjack.HolByte

@[hol "HOL/src/n-bit/byteScript.sml" "byte_index_def"
  (words_as_type_indexed_bitvec)]
def byteIndex {width : Nat} [NeZero width] (address : BitVec width)
    (bigEndian : Bool) : Nat :=
  let d := width / 8
  if bigEndian then 8 * ((d - 1) - address.toNat % d)
  else 8 * (address.toNat % d)

@[hol "HOL/src/n-bit/byteScript.sml" "get_byte_def"
  (words_as_type_indexed_bitvec)]
def getByte {width : Nat} [NeZero width] (address value : BitVec width)
    (bigEndian : Bool) : BitVec 8 :=
  (value >>> byteIndex address bigEndian).setWidth 8

@[hol "HOL/src/n-bit/byteScript.sml" "word_to_bytes_aux_def"
  (words_as_type_indexed_bitvec)]
def wordToBytesAux {width : Nat} [NeZero width] :
    Nat → BitVec width → Bool → List (BitVec 8)
  | 0, _, _ => []
  | n + 1, value, bigEndian =>
      wordToBytesAux n value bigEndian ++
        [getByte (BitVec.ofNat width n) value bigEndian]

@[hol "HOL/src/n-bit/byteScript.sml" "word_to_bytes_def"
  (words_as_type_indexed_bitvec)]
def wordToBytes {width : Nat} [NeZero width] (value : BitVec width)
    (bigEndian : Bool) : List (BitVec 8) :=
  wordToBytesAux (width / 8) value bigEndian

end Flapjack.HolByte
