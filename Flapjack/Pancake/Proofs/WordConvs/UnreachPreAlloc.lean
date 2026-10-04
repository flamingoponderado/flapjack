import Flapjack.Pancake.Proofs.WordConvs.Unreach

namespace Flapjack.WordConvs
open Flapjack Flapjack.Compiler.Backend.WordUnreach

/-- Flapjack factoring of the same native descriptor analysis for the original
source convention proof; HOL has no separately named descriptor theorem. -/
private theorem callArgConvention_ofDestSeqMove {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (priority : Nat)
    (moves : List (Nat × Nat)) (rest : WordLangProgHOL (BitVec width))
    (descriptor : destSeqMove program = some (priority, moves, rest))
    (source : callArgConventionHOL program = true) :
    callArgConventionHOL rest = true := by
  cases program <;> simp_all [destSeqMove, callArgConventionHOL]
  case move =>
    rw [← descriptor.2.2]
    rfl
  case seq first second =>
    cases first <;> simp_all [callArgConventionHOL]

/-- Flapjack-only factoring of source convention preservation for literal SimpSeq, retaining both
source convention premises and every move-merging branch. HOL has no
separately named SimpSeq lemma for this component. -/
private theorem callArgConvention_simpSeq {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width))
    (firstValid : callArgConventionHOL first = true)
    (secondValid : callArgConventionHOL second = true) :
    callArgConventionHOL (simpSeq first second) = true := by
  fun_cases simpSeq first second <;> try simp_all +zetaDelta only [callArgConventionHOL, Bool.and_eq_true, true_and, and_true]
  all_goals
    first
    | assumption
    | rfl
    | apply callArgConvention_ofDestSeqMove second <;> assumption
    | simp_all +zetaDelta only [callArgConventionHOL, Bool.and_eq_true, true_and, and_true]

/-- Original source pre-allocation component preservation for right association,
with both source-programme premises, including all returning call handlers. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem callArgConvention_seqAssocRight {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width))
    (firstValid : callArgConventionHOL first = true)
    (secondValid : callArgConventionHOL second = true) :
    callArgConventionHOL (seqAssocRight first second) = true := by
  induction first using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction
      generalizing second with
  | h first ih =>
    fun_cases seqAssocRight first second <;> try simp_all +zetaDelta only [callArgConventionHOL, Bool.and_eq_true]
    all_goals
      repeat' first
        | apply callArgConvention_simpSeq
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | assumption
        | simp_all +zetaDelta only [callArgConventionHOL, Bool.and_eq_true, true_and, and_true]
        | split
        | constructor

/-- Original remove_unreach preservation of the source call_arg_convention component. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem callArgConvention_removeUnreach {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width))
    (source : callArgConventionHOL program = true) :
    callArgConventionHOL (removeUnreach program) = true :=
  callArgConvention_seqAssocRight program .skip source rfl

/-- Flapjack factoring of the same native descriptor analysis for the original
source convention proof; HOL has no separately named descriptor theorem. -/
private theorem stackVarConvention_ofDestSeqMove {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (priority : Nat)
    (moves : List (Nat × Nat)) (rest : WordLangProgHOL (BitVec width))
    (descriptor : destSeqMove program = some (priority, moves, rest))
    (source : everyStackVarHOL isStackVar program = true) :
    everyStackVarHOL isStackVar rest = true := by
  cases program <;> simp_all [destSeqMove, everyStackVarHOL]
  case move =>
    rw [← descriptor.2.2]
    rfl
  case seq first second =>
    cases first <;> simp_all [everyStackVarHOL]

/-- Flapjack-only factoring of source convention preservation for literal SimpSeq, retaining both
source convention premises and every move-merging branch. HOL has no
separately named SimpSeq lemma for this component. -/
private theorem stackVarConvention_simpSeq {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width))
    (firstValid : everyStackVarHOL isStackVar first = true)
    (secondValid : everyStackVarHOL isStackVar second = true) :
    everyStackVarHOL isStackVar (simpSeq first second) = true := by
  fun_cases simpSeq first second <;> simp_all +zetaDelta [everyStackVarHOL]
  all_goals
    first
    | apply stackVarConvention_ofDestSeqMove second <;> assumption
    | simp_all +zetaDelta [everyStackVarHOL]

/-- Original source pre-allocation component preservation for right association,
with both source-programme premises, including all returning call handlers. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackVarConvention_seqAssocRight {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width))
    (firstValid : everyStackVarHOL isStackVar first = true)
    (secondValid : everyStackVarHOL isStackVar second = true) :
    everyStackVarHOL isStackVar (seqAssocRight first second) = true := by
  induction first using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction
      generalizing second with
  | h first ih =>
    fun_cases seqAssocRight first second <;> try simp_all +zetaDelta only [everyStackVarHOL, Bool.and_eq_true]
    all_goals
      repeat' first
        | apply stackVarConvention_simpSeq
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | assumption
        | simp_all +zetaDelta only [everyStackVarHOL, Bool.and_eq_true]
        | split
        | constructor

/-- Original remove_unreach preservation of the source every_stack_var_is_stack_var component. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackVarConvention_removeUnreach {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width))
    (source : everyStackVarHOL isStackVar program = true) :
    everyStackVarHOL isStackVar (removeUnreach program) = true :=
  stackVarConvention_seqAssocRight program .skip source rfl

/-- Original whole pre-allocation convention preservation; exactly the source
convention premise, with no target assumptions or restricted constructors. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem preAllocConventions_removeUnreach {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width))
    (source : preAllocConventionsHOL program = true) :
    preAllocConventionsHOL (removeUnreach program) = true := by
  simp only [preAllocConventionsHOL, Bool.and_eq_true] at source ⊢
  exact ⟨stackVarConvention_removeUnreach program source.1,
    callArgConvention_removeUnreach program source.2⟩

end Flapjack.WordConvs
