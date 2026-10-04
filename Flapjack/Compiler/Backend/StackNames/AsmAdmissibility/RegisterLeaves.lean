import Flapjack.Compiler.Backend.StackNames.ProgramNames
import Flapjack.Compiler.Backend.StackNames.NamesOk
import Flapjack.Compiler.Backend.StackProps.FixedNames
import Flapjack.Compiler.Backend.StackProps.ProgramNames
import Flapjack.Compiler.Backend.StackProps.ProgramValidity

namespace Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackProps

/-- HOL comp_ind OpCurrHeap case with the original naming and fixed-register guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_OpCurrHeap {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (operator : BinOp) (destination source : Nat)
    (_h : stackAsmName config (.opCurrHeap operator destination source) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.opCurrHeap operator destination source)) := by
  simp only [progCompHOL, stackAsmOkExact]

/-- HOL comp_ind CodeBufferWrite case with the original naming and fixed-register guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_CodeBufferWrite {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (first second : Nat)
    (h : stackAsmName config (.codeBufferWrite first second) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.codeBufferWrite first second)) := by
  rcases h with ⟨hi, hn, _⟩
  have hr := namesOkImp names config hn
  simp only [stackAsmName] at hi
  have hfirst := hr first hi.1
  have hsecond := hr second hi.2
  simp_all [progCompHOL, stackAsmOkExact, asmRegOkExact, findNameSpt_eq_lookupHelper]

/-- HOL comp_ind Raise case with the original naming and fixed-register guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_Raise {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (register : Nat)
    (h : stackAsmName config (.raise register) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.raise register)) := by
  rcases h with ⟨hi, hn, _⟩
  have hr := namesOkImp names config hn register hi
  simpa [progCompHOL, stackAsmOkExact, asmRegOkExact, findNameSpt_eq_lookupHelper] using hr

/-- HOL comp_ind Return case with the original naming and fixed-register guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_Return {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (register : Nat)
    (h : stackAsmName config (.ret register) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.ret register)) := by
  rcases h with ⟨hi, hn, _⟩
  have hr := namesOkImp names config hn register hi
  simpa [progCompHOL, stackAsmOkExact, asmRegOkExact, findNameSpt_eq_lookupHelper] using hr

/-- HOL comp_ind ShMemOp case with the original naming and fixed-register guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCompStackAsmOk_ShMemOp {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (operator : HolMemop) (register : Nat) (address : HolAddr width)
    (h : stackAsmName config (.shMemOp operator register address) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names (.shMemOp operator register address)) := by
  rcases h with ⟨hi, hn, _⟩
  have hr := namesOkImp names config hn
  simp only [stackAsmName] at hi
  cases address
  cases operator <;> simp_all [progCompHOL, stackAsmOkExact, addrName, asmAddrOkExact, findNameSpt_eq_lookupHelper] <;> grind

end Flapjack.Compiler.Backend.StackNames
