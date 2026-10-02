import Flapjack.Pancake.WordConvs

namespace Flapjack
open Flapjack.Compiler.Encoders.Asm

/-- Entire original full_inst_ok_less program lifting at exact positive-word
and assembler-configuration carriers. Instruction validity uses reviewed exact
HolInst conversion; ShareInst uses precisely the source four/two/remaining memop
partition and exact address extraction. Recursive clauses are shared with the
broad executed wrapper through policy-parameterized Flapjack infrastructure. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "full_inst_ok_less_def"
  (words_as_type_indexed_bitvec)]
def fullInstOkLessExact {width : Nat} [NeZero width] (config : AsmConfigExact width)
    (program : WordLangProgHOL (BitVec width)) : Bool :=
  fullInstOkLessWith (fun i => instOkLessExact config (HolInst.ofWordLangInst i))
    (fun operator offset =>
      if operator == .load || operator == .store ||
          operator == .load32 || operator == .store32 then
        asmAddrOffsetOkExact config offset
      else if operator == .load16 || operator == .store16 then
        asmHwOffsetOkExact config offset
      else asmByteOffsetOkExact config offset) program

/-- Flapjack-only unconditional equation interface for the shared recursive
implementation. HOL supplies these clauses inside the tagged definition, not
as a separately named theorem. No validity predicate is assumed as a premise. -/
theorem fullInstOkLessExactSeq {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (first second : WordLangProgHOL (BitVec width)) :
    fullInstOkLessExact config (.seq first second) =
      (fullInstOkLessExact config first && fullInstOkLessExact config second) := by
  simp only [fullInstOkLessExact, fullInstOkLessWith]

end Flapjack
