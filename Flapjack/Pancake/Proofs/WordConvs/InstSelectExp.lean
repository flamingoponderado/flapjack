import Flapjack.Compiler.Backend.WordInst
import Flapjack.Pancake.WordConvs.FullInstOkLess

namespace Flapjack.WordConvs
open Flapjack Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Encoders.Asm

/-- Original instruction-selection expression label emptiness for every native
expression and arbitrary source registers/configuration. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem instSelectExp_noLabels {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (target temporary : Nat)
    (expression : WordLangExpHOL (BitVec width)) :
    extractLabels (instSelectExp config target temporary expression) = [] := by
  induction expression using (measure (fun e : WordLangExpHOL (BitVec width) => sizeOf e)).wf.induction
      generalizing target temporary with
  | h expression ih =>
    fun_cases instSelectExp config target temporary expression <;>
      simp_all +zetaDelta [instSelectExp, extractLabels]
    all_goals
      repeat' first
        | (apply ih; simp_wf; omega)
        | simp_all +zetaDelta [extractLabels, isLookupCurrHeap]
        | split
        | constructor
    case case3 =>
      rename_i child notAddress
      apply ih child
      change sizeOf child < sizeOf (WordLangExpHOL.load child)
      simp

/-- Original unconditional expression-output flat conventions, including every
load, arithmetic, shift, and fallback branch. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem instSelectExp_flatExpConventions {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (target temporary : Nat)
    (expression : WordLangExpHOL (BitVec width)) :
    flatExpConventions (instSelectExp config target temporary expression) = true := by
  induction expression using (measure (fun e : WordLangExpHOL (BitVec width) => sizeOf e)).wf.induction
      generalizing target temporary with
  | h expression ih =>
    fun_cases instSelectExp config target temporary expression <;>
      simp_all +zetaDelta [instSelectExp, flatExpConventions]
    all_goals
      repeat' first
        | (apply ih; simp_wf; omega)
        | simp_all +zetaDelta [flatExpConventions, isLookupCurrHeap]
        | split
        | constructor
    case case3 =>
      rename_i child notAddress
      apply ih child
      change sizeOf child < sizeOf (WordLangExpHOL.load child)
      simp

/-- Original expression instruction validity with the sole source hypothesis
that address offset zero is allowed by the assembler configuration. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem instSelectExp_fullInstOkLess {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (target temporary : Nat)
    (expression : WordLangExpHOL (BitVec width))
    (zeroOffset : addrOffsetOk config 0 = true) :
    fullInstOkLessExact config (instSelectExp config target temporary expression) = true := by
  induction expression using (measure (fun e : WordLangExpHOL (BitVec width) => sizeOf e)).wf.induction
      generalizing target temporary with
  | h expression ih =>
    fun_cases instSelectExp config target temporary expression <;>
      (simp only [addrOffsetOk] at *
       simp [fullInstOkLessExact, HolInst.ofWordLangInst,
         HolArith.ofWordLangArith, HolRegImm.ofWordRegImm,
         HolAddr.ofWordLangAddr, instOkLessExact, asmAddrOffsetOkExact] at ih
       simp +zetaDelta [*, fullInstOkLessExact, fullInstOkLessWith,
        HolInst.ofWordLangInst, HolArith.ofWordLangArith, HolRegImm.ofWordRegImm,
        HolAddr.ofWordLangAddr, instOkLessExact, asmAddrOffsetOkExact])
    all_goals
      repeat' first
        | (apply ih; simp_wf; omega)
        | exact zeroOffset
        | simp +zetaDelta [*, fullInstOkLessExact, fullInstOkLessWith,
            HolInst.ofWordLangInst, HolArith.ofWordLangArith, HolRegImm.ofWordRegImm,
            instOkLessExact]
        | split
        | constructor
    all_goals
      first
      | (apply ih
         change sizeOf _ < sizeOf _
         simp <;> omega)
      | (intro eqZero
         have toNatZero := congrArg BitVec.toNat eqZero
         simp_all +zetaDelta only [BitVec.toNat_zero])

end Flapjack.WordConvs
