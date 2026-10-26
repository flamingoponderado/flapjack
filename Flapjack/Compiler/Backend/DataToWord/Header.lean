import Flapjack.Compiler.Backend.DataToWord.Config

/-! Word-level block header encoding. -/
namespace Flapjack.Compiler.Backend.DataToWord

/-- Encode the length, tag and two low marker bits into a word. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "make_header_def"
  (words_as_type_indexed_bitvec)]
def makeHeader {width : Nat} [NeZero width] (conf : Config) (tag : BitVec width) (len : Nat) : BitVec width :=
  (BitVec.ofNat width len <<< (width - conf.lenSize)) ||| (tag <<< 2) ||| 3

/-- Encode a header only when both length and tag fit the source bounds. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "encode_header_def"
  (words_as_type_indexed_bitvec)]
def encodeHeader {width : Nat} [NeZero width] (conf : Config) (tag len : Nat) : Option (BitVec width) :=
  if tag < 2 ^ (width - conf.lenSize - 2) ∧ tag < 2 ^ width / 16 ∧
     len < 2 ^ (width - 4) ∧ len < 2 ^ conf.lenSize then
    some (makeHeader conf (BitVec.ofNat width tag) len)
  else none

end Flapjack.Compiler.Backend.DataToWord
