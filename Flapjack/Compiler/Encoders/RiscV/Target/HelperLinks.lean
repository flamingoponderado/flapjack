module

public import Flapjack.Compiler.Encoders.RiscV.Target.Configuration

@[expose] public section

/-! Flapjack-specific congruence of executable inline tables with their
reviewed source-clause tables, and the native config's check-field projections.
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

/-- The native config's `valid_imm` clause table: `Sub` uses the strict lower
bound and every other operator the non-strict one, both signed word
comparisons, with the shared upper bound. -/
theorem riscvConfig_validImm_checks (operator : Sum BinOp Cmp) (i : BitVec 64) :
    riscvConfig.validImm operator i =
      ((match operator with
        | .inl .sub => (-2048 : BitVec 64).slt i
        | _ => (-2048 : BitVec 64).sle i) && i.sle 2047) := by
  cases operator with
  | inl b => cases b <;> rfl
  | inr c => cases c <;> rfl

/-- Every check field of the native config, as pinned by the direct HOL oracle
`scripts/hol-probes/riscv_config_probe.out`. `encode` is excluded: it is the
real native encoder and has no HOL probe row. -/
theorem riscvConfig_checks_projections :
    riscvConfig.isa = .riscv ∧
    riscvConfig.regCount = 32 ∧
    riscvConfig.avoidRegs = [0, 2, 3, 4, 31] ∧
    riscvConfig.fpRegCount = 0 ∧
    riscvConfig.linkReg = some 1 ∧
    riscvConfig.twoRegArith = false ∧
    riscvConfig.bigEndian = false ∧
    riscvConfig.addrOffset = (-2048, 2047) ∧
    riscvConfig.hwOffset = (-2048, 2047) ∧
    riscvConfig.byteOffset = (-2048, 2047) ∧
    riscvConfig.jumpOffset = (-2147483648, 0x7FFFF7FF) ∧
    riscvConfig.cjumpOffset = (-1048576 + 8, 1048575 + 4) ∧
    riscvConfig.locOffset = (-2147483648, 0x7FFFF7FF) ∧
    riscvConfig.codeAlignment = 2 := by
  decide

end Flapjack.Compiler.Encoders.RiscV.Target
