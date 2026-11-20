module

public import Flapjack.Pancake.Proofs.WordConvs.WordSimpLabels.Hoist
public import Flapjack.Pancake.Proofs.WordConvs.WordSimpLabels.PushOut

@[expose] public section

namespace Flapjack.WordConvs.WordSimpLabels
open Flapjack Flapjack.Compiler.Backend.WordSimp

/-- Full original compile_exp label relation for every native program. Every
stage is the actual reviewed compiler operation; label containment and the
source-distinctness implication are derived without an output property premise. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_compile_exp"
  (words_as_type_indexed_bitvec)]
theorem extractLabelsCompileExp {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) :
    labelsRel (extractLabels program) (extractLabels (compileExp program)) := by
  unfold compileExp
  have reassoc : labelsRel (extractLabels program) (extractLabels (seqAssoc .skip program)) := by
    rw [extractLabelsSeqAssoc]
    exact labelsRel_refl _
  exact labelsRel_trans reassoc
    (labelsRel_trans (extractLabelsConstFp (seqAssoc .skip program))
      (labelsRel_trans (labelsRelSimpDuplicateIf (constFp (seqAssoc .skip program)))
        (labelsRelPushOutIf (simpDuplicateIf (constFp (seqAssoc .skip program))))))

/-- Original code-label containment of the complete `compile_exp` pass: the
output keeps only source labels, through all four native stages. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_get_code_labels_word_simp" (words_as_type_indexed_bitvec)]
theorem getCodeLabels_compileExp {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) :
    getCodeLabelsHOL (compileExp program) ⊆ getCodeLabelsHOL program := by
  unfold compileExp
  refine (getCodeLabels_pushOutIf _).trans ?_
  refine (getCodeLabels_simpDuplicateIf _).trans ?_
  refine (getCodeLabels_constFp _).trans ?_
  rw [getCodeLabels_seqAssoc .skip program]
  simp [getCodeLabelsHOL, Set.empty_union]

end Flapjack.WordConvs.WordSimpLabels
