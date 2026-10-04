import Flapjack.Compiler.Backend.StackProps.RegisterNames

namespace Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Pre-naming arithmetic admissibility. The x86 fixed registers are logical
names 4/3, before architecture renaming; asmArithOkExact checks hardware1/2. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def arithName {width : Nat} [NeZero width] (operation : HolArith width)
    (config : AsmConfigExact width) : Prop :=
  match operation with
  | .binop b r1 r2 ri =>
      (config.twoRegArith = true → r1 = r2 ∨ b = .or ∧ ri = .reg r2) ∧
      regName r1 config ∧ regName r2 config ∧ regImmName (.inl b) ri config
  | .shift l r1 r2 (.imm i) =>
      (config.twoRegArith = true → r1 = r2) ∧ regName r1 config ∧ regName r2 config ∧
      (i = 0 → l = .lsl) ∧ i.toNat < width
  | .shift _ r1 r2 (.reg r3) =>
      (config.twoRegArith = true → r1 = r2) ∧ regName r1 config ∧ regName r2 config ∧
      regName r3 config ∧ (config.isa = .x86_64 → r3 = 4)
  | .div r1 r2 r3 =>
      regName r1 config ∧ regName r2 config ∧ regName r3 config ∧
      (config.isa = .armv8 ∨ config.isa = .mips ∨ config.isa = .riscv)
  | .longMul r1 r2 r3 r4 =>
      regName r1 config ∧ regName r2 config ∧ regName r3 config ∧ regName r4 config ∧
      (config.isa = .x86_64 → r1 = 3 ∧ r2 = 0 ∧ r3 = 0) ∧
      (config.isa = .armv7 → r1 ≠ r2) ∧
      (config.isa = .armv8 ∨ config.isa = .riscv ∨ config.isa = .ag32 → r1 ≠ r3 ∧ r1 ≠ r4)
  | .longDiv r1 r2 r3 r4 r5 =>
      config.isa = .x86_64 ∧ r1 = 0 ∧ r2 = 3 ∧ r3 = 3 ∧ r4 = 0 ∧ regName r5 config
  | .addCarry r1 r2 r3 r4 =>
      (config.twoRegArith = true → r1 = r2) ∧
      regName r1 config ∧ regName r2 config ∧ regName r3 config ∧ regName r4 config ∧
      (config.isa = .mips ∨ config.isa = .riscv → r1 ≠ r3 ∧ r1 ≠ r4)
  | .addOverflow r1 r2 r3 r4 =>
      (config.twoRegArith = true → r1 = r2) ∧
      regName r1 config ∧ regName r2 config ∧ regName r3 config ∧ regName r4 config ∧
      (config.isa = .mips ∨ config.isa = .riscv → r1 ≠ r3)
  | .subOverflow r1 r2 r3 r4 =>
      (config.twoRegArith = true → r1 = r2) ∧
      regName r1 config ∧ regName r2 config ∧ regName r3 config ∧ regName r4 config ∧
      (config.isa = .mips ∨ config.isa = .riscv → r1 ≠ r3)

end Flapjack.Compiler.Backend.StackProps
