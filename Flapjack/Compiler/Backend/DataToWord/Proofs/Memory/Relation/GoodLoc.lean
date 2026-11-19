module

public import Flapjack.Pancake.WordLang

@[expose] public section

/-! Valid code locations in data-to-word memory proofs. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack

/-- Words are valid; a location needs zero offset and a code label. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "good_loc_def"
  (words_as_type_indexed_bitvec)]
def goodLoc {width : Nat} [NeZero width] (code : Nat → Prop) : WordLocW width → Prop
  | .loc label offset => offset = 0 ∧ code label
  | .word _ => True

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
