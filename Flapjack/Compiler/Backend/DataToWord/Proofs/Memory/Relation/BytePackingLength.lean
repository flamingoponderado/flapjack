module

public import Flapjack.Compiler.Backend.DataToWord.Bytes
public import Flapjack.HolRef

@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend

/-- Byte packing preserves the destination word count. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "LENGTH_write_bytes"
  (words_as_type_indexed_bitvec)]
theorem writeBytes_wordCount {width : Nat} [NeZero width] (words : List (BitVec width))
    (bytes : List (BitVec 8)) (be : Bool) :
    (DataToWord.writeBytes bytes words be).length = words.length := by
  induction words generalizing bytes with
  | nil => rfl
  | cons x xs ih => simp [DataToWord.writeBytes, ih]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
