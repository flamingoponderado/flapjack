module

public import Flapjack.Byte.BytesToWord

@[expose] public section

/-! Source-shaped byte packing used by the data-to-word heap model. -/
namespace Flapjack.Compiler.Backend.DataToWord
open Flapjack

/-- Update each supplied word from the corresponding group of bytes. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "write_bytes_def"
  (words_as_type_indexed_bitvec)]
def writeBytes {width : Nat} [NeZero width] (bytes : List (BitVec 8)) :
    List (BitVec width) → Bool → List (BitVec width)
  | [], _ => []
  | word :: words, bigEndian =>
      HolByte.bytesToWord (width / 8) 0 bytes word bigEndian ::
        writeBytes (bytes.drop (width / 8)) words bigEndian

end Flapjack.Compiler.Backend.DataToWord
