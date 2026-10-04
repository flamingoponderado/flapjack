import Flapjack.Compiler.Backend.StackProps.ArithmeticNames
import Flapjack.Compiler.Backend.StackProps.AddressNames

namespace Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- HOL instruction admissibility before architecture renaming. Constants
use the logical destination bound regardless of their word payload; memory
checks both destination and address. Skip is the remaining constructor. -/
-- riscv-mi: integer-only instruction admissibility.
def instName {width : Nat} [NeZero width] (config : AsmConfigExact width)
    (instruction : HolInst width) : Prop :=
  match instruction with
  | .const destination _ => regName destination config
  | .mem operator destination address => regName destination config ∧ addrName operator address config
  | .arith operation => arithName operation config
  | .skip => True

end Flapjack.Compiler.Backend.StackProps
