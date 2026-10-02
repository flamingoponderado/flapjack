import Flapjack.Byte.WordSliceAlt

namespace Flapjack.HolByte

/-- Literal HOL high slice, widened byte shifted to its original position,
then low slice. The widening occurs before shifting, also at sub-byte widths. -/
@[hol "HOL/src/n-bit/byteScript.sml" "set_byte_def"
  (words_as_type_indexed_bitvec)]
def setByte {width : Nat} [NeZero width] (address : BitVec width)
    (byte : BitVec 8) (word : BitVec width) (bigEndian : Bool) : BitVec width :=
  let index := byteIndex address bigEndian
  (wordSliceAlt width (index + 8) word ||| (byte.setWidth width <<< index)) |||
    wordSliceAlt index 0 word

end Flapjack.HolByte
