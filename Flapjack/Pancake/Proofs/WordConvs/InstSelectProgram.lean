import Flapjack.Pancake.Proofs.WordConvs.InstSelectExp
import Aesop

namespace Flapjack.WordConvs
open Flapjack Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Encoders.Asm

/-- Original unconditional native instruction-selection label preservation,
including recursive return and exception handlers. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "inst_select_lab_pres" (words_as_type_indexed_bitvec)]
theorem instSelect_labPres {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (temporary : Nat)
    (program : WordLangProgHOL (BitVec width)) :
    extractLabels program = extractLabels (instSelect config temporary program) := by
  induction program using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction with
  | h program ih =>
    fun_cases instSelect config temporary program <;>
      simp_all +zetaDelta [extractLabels, instSelectExp_noLabels]
    all_goals
      repeat' first
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | simp_all +zetaDelta [extractLabels]
        | split
        | constructor
    all_goals
      congr 1 <;> (apply ih; change sizeOf _ < sizeOf _; simp; omega)

/-- Original unconditional flat expression conventions for every native
instruction-selection output, including both kinds of call handler. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "inst_select_flat_exp_conventions" (words_as_type_indexed_bitvec)]
theorem instSelect_flatExpConventions {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (temporary : Nat)
    (program : WordLangProgHOL (BitVec width)) :
    flatExpConventions (instSelect config temporary program) = true := by
  induction program using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction with
  | h program ih =>
    fun_cases instSelect config temporary program <;>
      simp_all +zetaDelta [flatExpConventions, instSelectExp_flatExpConventions]
    all_goals
      repeat' first
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | simp_all +zetaDelta [flatExpConventions]
        | split
        | constructor

/-- Original complete instruction-selection instruction-validity theorem.
Only the original zero-offset configuration and source-instruction premises
are assumed; every native constructor and nested handler remains in scope. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "inst_select_full_inst_ok_less" (words_as_type_indexed_bitvec)]
theorem instSelect_fullInstOkLess {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (temporary : Nat)
    (program : WordLangProgHOL (BitVec width))
    (addressZero : addrOffsetOk config 0 = true)
    (halfwordZero : hwOffsetOk config 0 = true)
    (byteZero : byteOffsetOk config 0 = true)
    (source : everyInst (fun i => instOkLessExact config (HolInst.ofWordLangInst i)) program = true) :
    fullInstOkLessExact config (instSelect config temporary program) = true := by
  have expressionValid (target temp : Nat) (expression : WordLangExpHOL (BitVec width)) :=
    instSelectExp_fullInstOkLess config target temp expression addressZero
  induction program using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction with
  | h program ih =>
    fun_cases instSelect config temporary program <;>
      (try simp only [everyInst] at source
       try simp +zetaDelta [fullInstOkLessExactSeq]
       simp only [addrOffsetOk, hwOffsetOk, byteOffsetOk] at *
       simp [fullInstOkLessExact, HolInst.ofWordLangInst, HolAddr.ofWordLangAddr,
         instOkLessExact, asmAddrOffsetOkExact] at ih expressionValid
       try simp +zetaDelta [HolInst.ofWordLangInst, HolAddr.ofWordLangAddr,
         instOkLessExact, asmAddrOffsetOkExact] at source
       simp +zetaDelta [*, fullInstOkLessExact, fullInstOkLessWith,
        HolInst.ofWordLangInst, HolAddr.ofWordLangAddr, instOkLessExact,
        asmAddrOffsetOkExact])
    all_goals
      repeat' first
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | assumption
        | exact source.1
        | exact source.2
        | split
        | constructor
    all_goals try simp only [expToAddrHOL, Option.some.injEq, WordLangAddr.addr.injEq] at *
    all_goals try (solve | (clear ih expressionValid; aesop))
    all_goals try simp only [everyInst, Bool.and_eq_true] at source
    all_goals try simp only [fullInstOkLessWith, Bool.and_eq_true]
    all_goals
      repeat' first
        | (apply ih; change sizeOf _ < sizeOf _; simp; omega)
        | assumption
        | exact source.1
        | exact source.2
        | constructor
    all_goals
      clear ih expressionValid
      cases program <;> simp_all [everyInst, fullInstOkLessWith]
    case ite =>
      rename_i cmp register operand left right notIf
      exact False.elim (notIf cmp register operand left right rfl rfl rfl rfl rfl)

end Flapjack.WordConvs
