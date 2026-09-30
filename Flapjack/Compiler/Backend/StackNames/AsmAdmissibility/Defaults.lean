import Flapjack.Compiler.Backend.StackNames.ProgramNames
import Flapjack.Compiler.Backend.StackNames.NamesOk
import Flapjack.Compiler.Backend.StackProps.FixedNames
import Flapjack.Compiler.Backend.StackProps.ProgramNames
import Flapjack.Compiler.Backend.StackProps.ProgramValidity

namespace Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackLang

/-- Remaining nonrecursive constructor cases of HOL's local admissibility
theorem. The case selector excludes exactly the separately ported instruction,
register and recursive cases. Each remaining constructor uses HOL's default
`stack_asm_ok` clause, including DataBufferWrite: its source naming bounds are
retained in the original antecedent although the target clause is True.
This is a constructor group, not the full assembled theorem. -/
@[hol "cakeml/compiler/backend/proofs/stack_namesProofScript.sml"
  "stack_names_comp_stack_asm_ok" (words_as_type_indexed_bitvec)]
theorem stackNamesCompStackAsmOk_Default {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width) (p : HolProg width)
    (hCase : match p with
      | .inst _ | .opCurrHeap _ _ _ | .shMemOp _ _ _ | .codeBufferWrite _ _
      | .raise _ | .ret _ | .seq _ _ | .ite _ _ _ _ _ | .loop _ | .call _ _ _ => False
      | _ => True)
    (_h : stackAsmName config p ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config) :
    stackAsmOkExact config (progCompHOL names p) := by
  cases p <;> simp_all [progCompHOL, stackAsmOkExact]

end Flapjack.Compiler.Backend.StackNames
