import Flapjack.Compiler.Encoders.RiscV.Target.Configuration

/-! Flapjack-specific congruence of executable inline tables with their
reviewed source-clause tables, and of the two config carriers' check fields.
These are derived relations between Lean implementations, with no separately
named HOL theorem, so they are untagged. Source comparison:
`riscv_targetScript.sml:117-137` gives priority to Sub and explicitly splits
Ror before applying the partial tables; lines277-304 define all config fields.
No equation below assigns an opcode to an unspecified helper slot.
The legacy encode field has a different carrier and remains excluded. -/
namespace Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack Compiler.Encoders.Asm RiscV.L3

/-- Complete immediate-binop relation, retaining HOL's priority Sub clause. -/
theorem riscvAst_binop_imm_helper (b : BinOp) (r1 r2 : Nat) (i : BitVec 64) :
    riscvAst (.inst (.arith (.binop b r1 r2 (.imm i)))) =
      if b = .sub then
        [.ArithI (.ADDI (BitVec.ofNat 5 r1, BitVec.ofNat 5 r2, -i.setWidth 12))]
      else
        [.ArithI (riscvBopI b (BitVec.ofNat 5 r1, BitVec.ofNat 5 r2, i.setWidth 12))] := by
  cases b <;> rfl

/-- Complete immediate-shift relation; Ror never reads the unspecified table slot. -/
theorem riscvAst_shift_imm_helper (sh : Flapjack.Shift) (r1 r2 : Nat) (i : BitVec 64) :
    riscvAst (.inst (.arith (.shift sh r1 r2 (.imm i)))) =
      if sh = .ror then
        [.Shift (.SRLI (31, BitVec.ofNat 5 r2, BitVec.ofNat 6 i.toNat)),
         .Shift (.SLLI (BitVec.ofNat 5 r1, BitVec.ofNat 5 r2, BitVec.ofNat 6 (64-i.toNat))),
         .ArithR (.OR (BitVec.ofNat 5 r1, BitVec.ofNat 5 r1, 31))]
      else
        [.Shift (riscvSh sh (BitVec.ofNat 5 r1, BitVec.ofNat 5 r2, BitVec.ofNat 6 i.toNat))] := by
  cases sh <;> rfl

/-- Complete register-shift relation; all registers retain source n2w truncation. -/
theorem riscvAst_shift_reg_helper (sh : Flapjack.Shift) (r1 r2 r : Nat) :
    riscvAst (.inst (.arith (.shift sh r1 r2 (.reg r)))) =
      if sh = .ror then
        [.ArithI (.ORI (31,0,64)),
         .ArithR (.SUB (31,31,BitVec.ofNat 5 r)),
         .Shift (.SLL (31,BitVec.ofNat 5 r2,31)),
         .Shift (.SRL (BitVec.ofNat 5 r1,BitVec.ofNat 5 r2,BitVec.ofNat 5 r)),
         .ArithR (.OR (BitVec.ofNat 5 r1,BitVec.ofNat 5 r1,31))]
      else
        [.Shift (riscvShv sh (BitVec.ofNat 5 r1, BitVec.ofNat 5 r2, BitVec.ofNat 5 r))] := by
  cases sh <;> rfl

/-- Entire operator/word64 domain, including the strict lower bound for Sub. -/
theorem riscvConfig_validImm_checks :
    riscvConfigForChecks.validImm = riscvConfig.validImm := by
  funext operator i
  cases operator with
  | inl b => cases b <;> rfl
  | inr c => cases c <;> rfl

/-- Every non-encode field of the diagnostic record agrees with the full
native config. This does not equate the records or their distinct encoders. -/
theorem riscvConfig_checks_projections :
    riscvConfigForChecks.isa = riscvConfig.isa ∧
    riscvConfigForChecks.regCount = riscvConfig.regCount ∧
    riscvConfigForChecks.avoidRegs = riscvConfig.avoidRegs ∧
    riscvConfigForChecks.fpRegCount = riscvConfig.fpRegCount ∧
    riscvConfigForChecks.linkReg = riscvConfig.linkReg ∧
    riscvConfigForChecks.twoRegArith = riscvConfig.twoRegArith ∧
    riscvConfigForChecks.bigEndian = riscvConfig.bigEndian ∧
    riscvConfigForChecks.validImm = riscvConfig.validImm ∧
    riscvConfigForChecks.addrOffset = riscvConfig.addrOffset ∧
    riscvConfigForChecks.hwOffset = riscvConfig.hwOffset ∧
    riscvConfigForChecks.byteOffset = riscvConfig.byteOffset ∧
    riscvConfigForChecks.jumpOffset = riscvConfig.jumpOffset ∧
    riscvConfigForChecks.cjumpOffset = riscvConfig.cjumpOffset ∧
    riscvConfigForChecks.locOffset = riscvConfig.locOffset ∧
    riscvConfigForChecks.codeAlignment = riscvConfig.codeAlignment := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,riscvConfig_validImm_checks,
    rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end Flapjack.Compiler.Encoders.RiscV.Target
