import Flapjack.Compiler.Backend.WordSimp
import Flapjack.Pancake.WordConvs

namespace Flapjack.WordConvs
open Flapjack.Compiler.Backend.WordSimp

/-- Exact HOL SmartSeq label preservation: the same two program binders and
unconditional equality. Only positive-width word representation is translated. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_SmartSeq"
  (words_as_type_indexed_bitvec)]
theorem extractLabels_smartSeqHOL {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width)) :
    extractLabels (smartSeqHOL first second) = extractLabels (.seq first second) := by
  cases first <;> simp [smartSeqHOL, extractLabels]

end Flapjack.WordConvs
