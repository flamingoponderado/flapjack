module

public import Flapjack.Pancake.Proofs.WordConvs.InstSelectExp
public import Flapjack.Pancake.WordConvs.CodeLabels

@[expose] public section

namespace Flapjack.WordConvs
open Flapjack Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Encoders.Asm

/-- Original instruction-selection expression empty code labels for every
native expression and arbitrary source registers/configuration. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_get_code_labels_inst_select_exp" (words_as_type_indexed_bitvec)]
theorem instSelectExp_codeLabels {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (target temporary : Nat)
    (expression : WordLangExpHOL (BitVec width)) :
    getCodeLabelsHOL (instSelectExp config target temporary expression) = ∅ := by
  induction expression using
      (measure (fun e : WordLangExpHOL (BitVec width) => sizeOf e)).wf.induction
      generalizing target temporary with
  | h expression ih =>
    fun_cases instSelectExp config target temporary expression <;>
      simp_all +zetaDelta [instSelectExp, getCodeLabelsHOL]
    all_goals
      repeat' first
        | (apply ih
           simp_wf
           omega)
        | simp_all +zetaDelta [getCodeLabelsHOL, isLookupCurrHeap]
        | split
        | constructor
    case case3 =>
      rename_i child notAddress
      apply ih child
      change sizeOf child < sizeOf (WordLangExpHOL.load child)
      simp

end Flapjack.WordConvs
