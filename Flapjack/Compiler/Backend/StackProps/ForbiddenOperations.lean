import Flapjack.Compiler.Backend.StackLang.Prog

namespace Flapjack.Compiler.Backend.StackProps
open StackLang

/-- Literal source no-install predicate on the faithful StackLang carrier.
Both optional Call bodies are checked independently, including a handler on a
Call whose return continuation is absent. No other fields affect the result. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml"
  "no_install_def" (words_as_type_indexed_bitvec)]
def noInstall {width : Nat} [NeZero width] : HolProg width → Bool
  | .call returnBody _ handler =>
      (match returnBody with
        | some (body, _, _, _) => noInstall body
        | none => true) &&
      (match handler with
        | some (body, _, _) => noInstall body
        | none => true)
  | .seq first second => noInstall first && noInstall second
  | .ite _ _ _ first second => noInstall first && noInstall second
  | .loop body => noInstall body
  | .install _ _ _ _ _ => false
  | _ => true

/-- Literal source no-shared-memory-operation predicate. Each populated Call
continuation is traversed regardless of the other continuation's presence;
ShMemOp alone is forbidden and all other nonrecursive constructors pass. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml"
  "no_shmemop_def" (words_as_type_indexed_bitvec)]
def noShmemop {width : Nat} [NeZero width] : HolProg width → Bool
  | .call returnBody _ handler =>
      (match returnBody with
        | some (body, _, _, _) => noShmemop body
        | none => true) &&
      (match handler with
        | some (body, _, _) => noShmemop body
        | none => true)
  | .seq first second => noShmemop first && noShmemop second
  | .ite _ _ _ first second => noShmemop first && noShmemop second
  | .loop body => noShmemop body
  | .shMemOp _ _ _ => false
  | _ => true

end Flapjack.Compiler.Backend.StackProps
