import Flapjack.Compiler.Backend.StackProps
import Flapjack.Compiler.Backend.StackLang.Prog

namespace Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

/-- Exact HOL configuration instance of Stack assembly admissibility. Only
CodeBufferWrite is explicitly checked; DataBufferWrite is a default-true case.
An indirect Call target is checked independently of its return continuation,
while handler traversal is nested under the SOME-return branch. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "stack_asm_ok_def"
  (words_as_type_indexed_bitvec)]
def stackAsmOkExact {width : Nat} [NeZero width] (config : AsmConfigExact width) :
    HolProg width → Prop
  | .inst instruction => asmInstOkExact instruction config = true
  | .shMemOp operator register address =>
      asmRegOkExact register config = true ∧ asmAddrOkExact operator address config = true
  | .codeBufferWrite first second =>
      first < config.regCount ∧ second < config.regCount ∧
      first ∉ config.avoidRegs ∧ second ∉ config.avoidRegs
  | .seq first second | .ite _ _ _ first second =>
      stackAsmOkExact config first ∧ stackAsmOkExact config second
  | .loop body => stackAsmOkExact config body
  | .raise register | .ret register =>
      register < config.regCount ∧ register ∉ config.avoidRegs
  | .call returns target handler =>
      (match target with
       | .inr register => register < config.regCount ∧ register ∉ config.avoidRegs
       | _ => True) ∧
      (match returns with
       | none => True
       | some (body, _, _, _) => stackAsmOkExact config body ∧
           (match handler with
            | none => True
            | some (body, _, _) => stackAsmOkExact config body))
  | _ => True

end Flapjack.Compiler.Backend.StackProps
