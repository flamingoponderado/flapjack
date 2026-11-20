module

public import Flapjack.Compiler.Backend.WordSimp
public import Flapjack.Pancake.WordConvs
public import Flapjack.Pancake.WordConvs.CodeLabels

@[expose] public section

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

/-- Exact HOL `word_get_code_labels_SmartSeq`
(`wordConvsProofScript.sml:631-635`): `SmartSeq` adds no code labels beyond its
two operands. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_get_code_labels_SmartSeq" (words_as_type_indexed_bitvec)]
theorem getCodeLabels_smartSeqHOL {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width)) :
    getCodeLabelsHOL (smartSeqHOL first second) =
      getCodeLabelsHOL first ∪ getCodeLabelsHOL second := by
  cases first
  all_goals simp [smartSeqHOL, getCodeLabelsHOL]

end Flapjack.WordConvs
