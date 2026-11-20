module

public import Flapjack.Pancake.Proofs.WordConvs.InstSelectProgram
public import Flapjack.Pancake.Proofs.WordConvs.InstSelectExpCodeLabels
public import Flapjack.Pancake.WordConvs.CodeLabels

@[expose] public section

/-!
Code-label preservation for the native instruction-selection pass. Kept in a
sibling module so the `Set`-based statement stays out of `InstSelectProgram`'s
environment, where the added `Mathlib.Data.Set.Basic` import makes a downstream
`simp_all` exceed the heartbeat limit.
-/

namespace Flapjack.WordConvs
open Flapjack Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Encoders.Asm

/-- Original unconditional native instruction-selection label preservation,
including recursive return and exception handlers. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_get_code_labels_inst_select" (words_as_type_indexed_bitvec)]
theorem instSelect_codeLabels {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (temporary : Nat)
    (program : WordLangProgHOL (BitVec width)) :
    getCodeLabelsHOL (instSelect config temporary program) = getCodeLabelsHOL program := by
  induction program using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction with
  | h program ih =>
    fun_cases instSelect config temporary program <;>
      simp_all +zetaDelta [getCodeLabelsHOL, instSelectExp_codeLabels]
    all_goals
      repeat' first
        | (apply ih
           simp_wf
           omega)
        | (rw [ih _ (by
             simp_wf
             omega)])
        | simp_all +zetaDelta [getCodeLabelsHOL]
        | split
        | constructor
        | rfl
    case h.case7 p1 =>
      apply ih
      simp_wf

end Flapjack.WordConvs
