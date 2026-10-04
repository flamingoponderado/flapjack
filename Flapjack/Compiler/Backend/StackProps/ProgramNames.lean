import Flapjack.Compiler.Backend.StackProps.InstructionNames
import Flapjack.Compiler.Backend.StackLang.Prog

namespace Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

/-- HOL stack instruction naming admissibility. If ignores comparison operands;
Call always checks an indirect target, but checks its handler only when a return
continuation is present. Call metadata and the remaining constructors are ignored. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def stackAsmName {width : Nat} [NeZero width] (config : AsmConfigExact width) :
    HolProg width → Prop
  | .inst instruction => instName config instruction
  | .opCurrHeap _ first second =>
      (config.twoRegArith → first = second) ∧ regName first config ∧ regName second config
  | .shMemOp operator register address =>
      regName register config ∧ addrName operator address config
  | .codeBufferWrite first second | .dataBufferWrite first second =>
      regName first config ∧ regName second config
  | .seq first second | .ite _ _ _ first second =>
      stackAsmName config first ∧ stackAsmName config second
  | .loop body => stackAsmName config body
  | .raise register | .ret register => regName register config
  | .call returns target handler =>
      (match target with | .inr register => regName register config | _ => True) ∧
      (match returns with
       | none => True
       | some (body, _, _, _) =>
           stackAsmName config body ∧
           (match handler with
            | none => True
            | some (body, _, _) => stackAsmName config body))
  | _ => True

end Flapjack.Compiler.Backend.StackProps
