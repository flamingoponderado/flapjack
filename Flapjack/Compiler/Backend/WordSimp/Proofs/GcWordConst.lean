import Flapjack.HolRef
import Flapjack.Compiler.Backend.WordSimp

/-!
# `word_simpProof` `is_gc_word_const`

HOL `is_gc_word_const_def` of
`cakeml/compiler/backend/proofs/word_simpProofScript.sml:130-133`, used by the
`word_gcFunctions` root theorems.
-/

namespace Flapjack.Compiler.Backend.WordSimp

/-- Exact HOL `is_gc_word_const_def` (`word_simpProofScript.sml:130-133`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "is_gc_word_const_def"
  (words_as_type_indexed_bitvec)]
def isGcWordConst {width : Nat} [NeZero width] : WordLocW width → Bool
  | .loc _ _ => true
  | .word w => isGcConst w

end Flapjack.Compiler.Backend.WordSimp
