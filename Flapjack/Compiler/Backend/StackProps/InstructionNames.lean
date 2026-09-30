import Flapjack.Compiler.Backend.StackProps.ArithmeticNames
import Flapjack.Compiler.Backend.StackProps.AddressNames
import Flapjack.Compiler.Backend.StackProps.FloatNames

namespace Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- HOL instruction admissibility before architecture renaming. Constants
use the logical destination bound regardless of their word payload; memory
checks both destination and address. Skip is the remaining constructor. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "inst_name_def"
  (words_as_type_indexed_bitvec)]
def instName {width : Nat} [NeZero width] (config : AsmConfigExact width)
    (instruction : HolInst width) : Prop :=
  match instruction with
  | .const destination _ => regName destination config
  | .mem operator destination address => regName destination config ∧ addrName operator address config
  | .arith operation => arithName operation config
  | .fp operation => fpName operation config
  | .skip => True

end Flapjack.Compiler.Backend.StackProps
