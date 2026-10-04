import Flapjack.Compiler.Encoders.Asm

namespace Flapjack.Compiler.Backend.StackProps

open Flapjack.Compiler.Encoders.Asm

/-- HOL's logical register-name bound before Stack naming. This retains
natural subtraction of the entire avoided-register list length. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def regName {width : Nat} [NeZero width] (register : Nat)
    (config : AsmConfigExact width) : Prop :=
  register < config.regCount - config.avoidRegs.length

/-- HOL pre-naming register/immediate admissibility. Unlike asm reg_imm_ok,
this definition has no xor-minus-one exception: immediate validity is exactly
config.validImm, while registers use the reduced logical-register bound. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def regImmName {width : Nat} [NeZero width] (operator : Sum BinOp Cmp)
    (operand : HolRegImm width) (config : AsmConfigExact width) : Prop :=
  match operand with
  | .reg register => regName register config
  | .imm value => config.validImm operator value = true

end Flapjack.Compiler.Backend.StackProps
