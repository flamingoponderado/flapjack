module

public import Flapjack.Compiler.Backend.BackendCommon

@[expose] public section

namespace Flapjack

/-- Convert a target word to the 64-bit bitmap representation. A 32-bit
word occupies the upper half; all other widths use ordinary word conversion. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "upper_w2w_def"
  (words_as_type_indexed_bitvec)]
def upperW2w {width : Nat} [NeZero width] (word : BitVec width) : BitVec 64 :=
  if width = 32 then word.setWidth 64 <<< 32 else word.setWidth 64

end Flapjack
