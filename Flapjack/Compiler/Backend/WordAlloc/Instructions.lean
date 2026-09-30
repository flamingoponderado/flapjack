import Flapjack.Pancake.WordLang

namespace Flapjack.WordAlloc

/-- Exact HOL immediate colouring: register operands are renamed and word
immediates remain unchanged. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "apply_colour_imm_def"
  (words_as_type_indexed_bitvec)]
def applyColourImm {width : Nat} [NeZero width] (f : Nat → Nat) :
    WordRegImm (BitVec width) → WordRegImm (BitVec width)
  | .reg n => .reg (f n)
  | .imm w => .imm w

end Flapjack.WordAlloc
