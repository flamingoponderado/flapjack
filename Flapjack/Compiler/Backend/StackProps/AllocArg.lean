import Flapjack.Compiler.Backend.StackLang.Prog

namespace Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackLang

/-- Stack allocation requires the literal allocation argument one. Unlike the
stack-removal name predicate, Call checks its two optional bodies independently. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "alloc_arg_def"
  (words_as_type_indexed_bitvec)]
def allocArg {width : Nat} [NeZero width] : HolProg width → Prop
  | .alloc words => words = 1
  | .seq first second | .ite _ _ _ first second => allocArg first ∧ allocArg second
  | .loop body => allocArg body
  | .call returns _ handler =>
      (match returns with
       | none => True
       | some (body, _, _, _) => allocArg body) ∧
      (match handler with
       | none => True
       | some (body, _, _) => allocArg body)
  | _ => True

end Flapjack.Compiler.Backend.StackProps
