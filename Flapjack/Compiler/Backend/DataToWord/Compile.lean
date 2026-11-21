module

public import Flapjack.Compiler.Backend.DataToWord.CompleteStubs
public import Flapjack.Compiler.Backend.DataToWord.Total
public import Flapjack.Compiler.Backend.WordToWord.Compile

@[expose] public section

/-! data_to_wordScript.sml 2835-2852: the whole-program data-to-word
compiler, with and without the word-to-word optimiser. -/
namespace Flapjack.Compiler.Backend.DataToWord

open Flapjack Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `data_to_word$compile_def` (`data_to_wordScript.sml:2835-2842`):
set the floating-point capabilities from the target, prepend the stubs to the
compiled parts and run the word-to-word compiler. HOL's boolean record values
`1 < fp_reg_count` and `ISA = ARMv7 ∧ 2 < fp_reg_count` are decided. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "compile_def"
  (words_as_type_indexed_bitvec)]
noncomputable def compile {width : Nat} [NeZero width] (dataConf : Config)
    (wordConf : WordToWord.Config) (asmConf : AsmConfigExact width)
    (prog : List (Nat × Nat × DataLang.Prog)) :
    List (Option (Spt Nat)) × List (Nat × Nat × WordLangProgHOL (BitVec width)) :=
  let dataConf := { dataConf with
    hasFpOps := decide (1 < asmConf.fpRegCount)
    hasFpTern := decide (asmConf.isa = .armv7 ∧ 2 < asmConf.fpRegCount) }
  let p := stubs dataConf ++ prog.map (compilePart dataConf)
  WordToWord.compile wordConf asmConf p

/-- Exact HOL `data_to_word$compile_0_def` (`data_to_wordScript.sml:2844-2852`):
the same stub and part compilation without the word-to-word optimiser. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "compile_0_def"
  (words_as_type_indexed_bitvec)]
def compile0 {width : Nat} [NeZero width] (dataConf : Config) (asmConf : AsmConfigExact width)
    (prog : List (Nat × Nat × DataLang.Prog)) :
    List (Nat × Nat × WordLangProgHOL (BitVec width)) :=
  let dataConf := { dataConf with
    hasFpOps := decide (1 < asmConf.fpRegCount)
    hasFpTern := decide (asmConf.isa = .armv7 ∧ 2 < asmConf.fpRegCount) }
  stubs dataConf ++ prog.map (compilePart dataConf)

end Flapjack.Compiler.Backend.DataToWord
