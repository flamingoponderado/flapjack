import Flapjack.Pancake.Proofs.WordConvs.InstSelectProgram
import Flapjack.Pancake.Proofs.WordConvs.ThreeToTwo
import Flapjack.Pancake.Proofs.WordConvs.Unreach

/-! Original native instruction-selection, three-to-two and unreachable-code
handler laws. WordSimp, SSA and whole-program composition are separate groups. -/
namespace Flapjack.WordConvs
open Flapjack Flapjack.Compiler.Backend.WordInst
open Flapjack.Compiler.Backend.WordUnreach Flapjack.Compiler.Encoders.Asm

/-- Original unconditional expression-selector handler safety, arbitrary config,
registers, owner and expression. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_good_handlers_inst_select_exp" (words_as_type_indexed_bitvec)]
theorem goodHandlers_instSelectExp {width : Nat} [NeZero width] (n : Nat)
    (config : AsmConfigExact width) (target temporary : Nat)
    (expression : WordLangExpHOL (BitVec width)) :
    goodHandlersHOL n (instSelectExp config target temporary expression) = true := by
  induction expression using (measure (fun e : WordLangExpHOL (BitVec width) => sizeOf e)).wf.induction
      generalizing target temporary with
  | h expression ih =>
    fun_cases instSelectExp config target temporary expression <;>
      simp_all +zetaDelta [instSelectExp, goodHandlersHOL]
    all_goals
      repeat' first
        | (apply ih; simp_wf; omega)
        | simp_all +zetaDelta [goodHandlersHOL, isLookupCurrHeap]
        | split
        | constructor
    case case3 =>
      rename_i child notAddress
      apply ih child
      change sizeOf child < sizeOf (WordLangExpHOL.load child)
      simp

/-- Original complete program-selector iff; no input validity or target-handler
premise, including all returning/exceptional call combinations. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_good_handlers_inst_select" (words_as_type_indexed_bitvec)]
theorem goodHandlers_instSelect {width : Nat} [NeZero width] (n : Nat)
    (config : AsmConfigExact width) (temporary : Nat)
    (program : WordLangProgHOL (BitVec width)) :
    goodHandlersHOL n (instSelect config temporary program) = true ↔
      goodHandlersHOL n program = true := by
  have equal : goodHandlersHOL n (instSelect config temporary program) =
      goodHandlersHOL n program := by
    induction program using
        (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction with
    | h program ih =>
      fun_cases instSelect config temporary program <;>
        simp_all +zetaDelta [goodHandlersHOL, goodHandlers_instSelectExp]
      all_goals
        repeat' first
          | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
          | simp_all +zetaDelta [goodHandlersHOL]
          | split
      all_goals
        congr 1 <;> first
          | rfl
          | (apply ih; change sizeOf _ < sizeOf _; simp; omega)
          | (congr 1; first
              | rfl
              | (apply ih; change sizeOf _ < sizeOf _; simp; omega))
  rw [equal]

/-- Original iff for either enabled value and every program/owner. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_good_handlers_three_to_two_reg_prog" (words_as_type_indexed_bitvec)]
theorem goodHandlers_threeToTwoRegProg {width : Nat} [NeZero width] (n : Nat)
    (enabled : Bool) (program : WordLangProgHOL (BitVec width)) :
    goodHandlersHOL n (threeToTwoRegProg enabled program) = true ↔
      goodHandlersHOL n program = true := by
  have equal : goodHandlersHOL n (threeToTwoRegProg enabled program) =
      goodHandlersHOL n program := by
    cases enabled <;> simp [threeToTwoRegProg]
    induction program using
        (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction with
    | h program ih =>
      fun_cases threeToTwoReg program <;> simp_all +zetaDelta [goodHandlersHOL]
      all_goals
        repeat' first
          | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
          | simp_all +zetaDelta [goodHandlersHOL]
          | split
      all_goals
        congr 1 <;> first
          | rfl
          | (apply ih; change sizeOf _ < sizeOf _; simp; omega)
          | (congr 1; first
              | rfl
              | (apply ih; change sizeOf _ < sizeOf _; simp; omega))
  rw [equal]

/-- Flapjack infrastructure: the native move descriptor strips only handler-free
moves. HOL uses its descriptor cases inline and has no standalone declaration. -/
private theorem goodHandlers_ofDestSeqMove {width : Nat} [NeZero width] (n : Nat)
    (program : WordLangProgHOL (BitVec width)) (priority : Nat)
    (moves : List (Nat × Nat)) (rest : WordLangProgHOL (BitVec width))
    (descriptor : destSeqMove program = some (priority, moves, rest))
    (source : goodHandlersHOL n program = true) : goodHandlersHOL n rest = true := by
  cases program <;> simp_all [destSeqMove, goodHandlersHOL]
  case move =>
    rw [← descriptor.2.2]
    rfl
  case seq first second =>
    cases first <;> simp_all [goodHandlersHOL]

/-- Original SimpSeq implication retains both source guards and all native
terminal/skip/move-merging cases. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_good_handlers_SimpSeq" (words_as_type_indexed_bitvec)]
theorem goodHandlers_simpSeq {width : Nat} [NeZero width] (n : Nat)
    (first second : WordLangProgHOL (BitVec width))
    (firstValid : goodHandlersHOL n first = true)
    (secondValid : goodHandlersHOL n second = true) :
    goodHandlersHOL n (simpSeq first second) = true := by
  fun_cases simpSeq first second <;> simp_all +zetaDelta [goodHandlersHOL]
  all_goals apply goodHandlers_ofDestSeqMove <;> assumption

/-- Original right-association implication with both source guards; native
nested return and exception handlers are included. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_good_handlers_Seq_assoc_right" (words_as_type_indexed_bitvec)]
theorem goodHandlers_seqAssocRight {width : Nat} [NeZero width] (n : Nat)
    (first second : WordLangProgHOL (BitVec width))
    (firstValid : goodHandlersHOL n first = true)
    (secondValid : goodHandlersHOL n second = true) :
    goodHandlersHOL n (seqAssocRight first second) = true := by
  induction first using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction
      generalizing second with
  | h first ih =>
    fun_cases seqAssocRight first second <;>
      try simp_all +zetaDelta only [goodHandlersHOL, Bool.and_eq_true]
    all_goals
      repeat' first
        | apply goodHandlers_simpSeq
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | assumption
        | simp_all +zetaDelta only [goodHandlersHOL, Bool.and_eq_true]
        | split
        | constructor

/-- Original remove-unreach implication, only the original owner/source guard. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_good_handlers_remove_unreach" (words_as_type_indexed_bitvec)]
theorem goodHandlers_removeUnreach {width : Nat} [NeZero width] (n : Nat)
    (program : WordLangProgHOL (BitVec width)) (source : goodHandlersHOL n program = true) :
    goodHandlersHOL n (removeUnreach program) = true :=
  goodHandlers_seqAssocRight n program .skip source rfl

end Flapjack.WordConvs
