import Flapjack.Compiler.Backend.StackProps.RegisterNames
import Flapjack.Compiler.Backend.StackLang.Prog

namespace Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

/-- HOL's register-name prerequisite for stack removal. Fixed Store/Load check
the first positional argument exactly as the source does, regardless of Lean's
field labels. Call checks a handler only inside the SOME-return branch; its
target and metadata are ignored. The original inferred type is
`alpha asm_config -> beta stackLang.prog -> bool`: configuration and program
word dimensions are independent, including when they differ. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "stack_asm_remove_def"
  (words_as_type_indexed_bitvec)]
def stackAsmRemove {configWidth : Nat} {width : Nat} [NeZero configWidth] [NeZero width]
    (config : AsmConfigExact configWidth) :
    HolProg width → Prop
  | .get n _ | .set _ n | .stackStore n _ | .stackLoad n _ |
      .stackGetSize n | .stackSetSize n => regName n config
  | .opCurrHeap _ n n0 | .stackStoreAny n n0 | .stackLoadAny n n0 |
      .bitmapLoad n n0 | .storeConsts n n0 _ => regName n config ∧ regName n0 config
  | .seq first second => stackAsmRemove config first ∧ stackAsmRemove config second
  | .ite _ _ _ first second => stackAsmRemove config first ∧ stackAsmRemove config second
  | .loop body => stackAsmRemove config body
  | .call returns _ handler =>
      match returns with
      | none => True
      | some (body, _, _, _) =>
          stackAsmRemove config body ∧
            match handler with
            | none => True
            | some (body, _, _) => stackAsmRemove config body
  | _ => True

end Flapjack.Compiler.Backend.StackProps
