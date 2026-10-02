import Flapjack.Compiler.Backend.StackLang.Prog

namespace Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackLang

/-- Full original calling-convention predicate. A handler is traversed only
inside a present return record. Install ignores its two data-buffer arguments;
all five FFI arguments and the return register use the original exact equalities. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "call_args_def"
  (words_as_type_indexed_bitvec)]
def callArgs {width : Nat} [NeZero width] (program : HolProg width)
    (ptr len ptr2 len2 ret : Nat) : Prop :=
  match program with
  | .seq first second | .ite _ _ _ first second =>
      callArgs first ptr len ptr2 len2 ret ∧ callArgs second ptr len ptr2 len2 ret
  | .loop body => callArgs body ptr len ptr2 len2 ret
  | .halt n => n = ptr
  | .ffi _ p l p2 l2 r => p = ptr ∧ l = len ∧ p2 = ptr2 ∧ l2 = len2 ∧ r = ret
  | .call returns _ handler =>
      match returns with
      | none => True
      | some (body,register,_,_) =>
          callArgs body ptr len ptr2 len2 ret ∧ register = ret ∧
            (match handler with
             | none => True
             | some (body,_,_) => callArgs body ptr len ptr2 len2 ret)
  | .install p l _ _ r => p = ptr ∧ l = len ∧ r = ret
  | _ => True

end Flapjack.Compiler.Backend.StackProps
