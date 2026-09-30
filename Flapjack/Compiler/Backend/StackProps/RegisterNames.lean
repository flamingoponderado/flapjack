import Flapjack.Compiler.Encoders.Asm

namespace Flapjack.Compiler.Backend.StackProps

open Flapjack.Compiler.Encoders.Asm

/-- HOL's logical register-name bound before Stack naming. This retains
natural subtraction of the entire avoided-register list length. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "reg_name_def"
  (words_as_type_indexed_bitvec)]
def regName {width : Nat} [NeZero width] (register : Nat)
    (config : AsmConfigExact width) : Prop :=
  register < config.regCount - config.avoidRegs.length

end Flapjack.Compiler.Backend.StackProps
