import Flapjack.Compiler.Backend.StackNames.ProgramNames
import Flapjack.Compiler.Backend.StackNames.NamesOk
import Flapjack.Compiler.Backend.StackProps.FixedNames
import Flapjack.Compiler.Backend.StackProps.ProgramNames
import Flapjack.Compiler.Backend.StackProps.ProgramValidity

namespace Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackProps

/-- Instruction case of HOL's local assembler-admissibility theorem. Renaming
preserves the source register, immediate, architecture and fixed-name guards.
The remaining program constructors and full theorem are separate open work. -/
-- riscv-mi: integer-only specialization of the referenced HOL declaration.

theorem stackNamesCompStackAsmOk_Inst {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (instruction : HolInst width)
    (h : stackAsmName config (.inst instruction) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.inst instruction)) := by
  rcases h with ⟨hi, hn, hf⟩
  have hr := namesOkImp names config hn
  have hne : ∀ a b, a ≠ b → regName a config → regName b config →
      findNameSpt names a ≠ findNameSpt names b := by
    intro a b hab ha hb
    simpa only [findNameSpt_eq_lookupHelper] using
      namesOkImp2 names config a b ⟨hn, hab, ha, hb⟩
  simp only [findNameSpt_eq_lookupHelper] at hne ⊢
  simp only [stackAsmName] at hi
  simp only [stackAsmOkExact, progCompHOL]
  cases instruction with
  | skip => rfl
  | const destination value =>
    simpa only [instFindNameHOL, asmInstOkExact, findNameSpt_eq_lookupHelper] using hr destination hi
  | arith operation =>
    cases operation with
    | binop op dest src right =>
      cases right <;> simp_all [instName, arithName, instFindNameHOL, asmInstOkExact, asmArithOkExact, riFindNameHOL, regImmName, asmRegImmOkExact, fixedNames, findNameSpt_eq_lookupHelper] <;> grind
    | shift op dest src right =>
      cases right <;> simp_all [instName, arithName, instFindNameHOL, asmInstOkExact, asmArithOkExact, riFindNameHOL, fixedNames, findNameSpt_eq_lookupHelper] <;> grind
    | div a b c =>
      simp_all [instName, arithName, instFindNameHOL, asmInstOkExact, asmArithOkExact, fixedNames, findNameSpt_eq_lookupHelper] <;> grind
    | longMul a b c d =>
      simp_all [instName, arithName, instFindNameHOL, asmInstOkExact, asmArithOkExact, fixedNames, findNameSpt_eq_lookupHelper] <;> grind
    | longDiv a b c d e =>
      simp_all [instName, arithName, instFindNameHOL, asmInstOkExact, asmArithOkExact, fixedNames, findNameSpt_eq_lookupHelper] <;> grind
    | addCarry a b c d =>
      simp_all [instName, arithName, instFindNameHOL, asmInstOkExact, asmArithOkExact, fixedNames, findNameSpt_eq_lookupHelper] <;> grind
    | addOverflow a b c d =>
      simp_all [instName, arithName, instFindNameHOL, asmInstOkExact, asmArithOkExact, fixedNames, findNameSpt_eq_lookupHelper] <;> grind
    | subOverflow a b c d =>
      simp_all [instName, arithName, instFindNameHOL, asmInstOkExact, asmArithOkExact, fixedNames, findNameSpt_eq_lookupHelper] <;> grind
  | mem operation destination address =>
    cases address
    cases operation <;>
      simp_all [instName, addrName, instFindNameHOL, asmInstOkExact,
        findNameSpt_eq_lookupHelper] <;> grind

end Flapjack.Compiler.Backend.StackNames
