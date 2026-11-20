module

public import Flapjack.Compiler.Backend.DataToWord.Config
public import Flapjack.Pancake.WordLang

@[expose] public section

/-! Conditional pointer adjustment in data-to-word memory proofs. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack

/-- Adjust tagged words by the heap offset; locations remain unchanged. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_cond_add_def"
  (words_as_type_indexed_bitvec)]
def wordCondAdd {width : Nat} [NeZero width] (conf : Config) (address : BitVec width) :
    Bool × WordLocW width → WordLocW width
  | (true, .word word) => .word (word + (address <<< (shiftLength conf - wordShiftAmount width)))
  | (_, value) => value

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
