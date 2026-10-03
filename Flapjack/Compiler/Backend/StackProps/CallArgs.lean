import Flapjack.Compiler.Backend.StackLang.Prog

/-! StackProps `call_args_def` (`stackPropsScript.sml:1107-1128`) on the faithful program
carrier. -/

namespace Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackLang

/-- Exact HOL `call_args_def` (`stackPropsScript.sml:1107-1128`): `Halt`, `FFI`, `Install` and
the return-link register of a returning `Call` use the fixed argument registers; `Seq`, `If`,
`Loop` and the `Call` continuations recurse; every other program satisfies it. HOL's `<=>`
clauses are a `bool`-valued predicate, rendered as `Prop`. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "call_args_def"
  (words_as_type_indexed_bitvec)]
def callArgs {width : Nat} [NeZero width] :
    HolProg width → Nat → Nat → Nat → Nat → Nat → Prop
  | .seq p1 p2, ptr, len, ptr2, len2, ret =>
      callArgs p1 ptr len ptr2 len2 ret ∧ callArgs p2 ptr len ptr2 len2 ret
  | .ite _ _ _ p1 p2, ptr, len, ptr2, len2, ret =>
      callArgs p1 ptr len ptr2 len2 ret ∧ callArgs p2 ptr len ptr2 len2 ret
  | .loop p1, ptr, len, ptr2, len2, ret => callArgs p1 ptr len ptr2 len2 ret
  | .halt n, ptr, _, _, _, _ => n = ptr
  | .ffi _ ptr' len' ptr2' len2' ret', ptr, len, ptr2, len2, ret =>
      ptr' = ptr ∧ len' = len ∧ ptr2' = ptr2 ∧ len2' = len2 ∧ ret' = ret
  | .call x1 _ x2, ptr, len, ptr2, len2, ret =>
      match x1 with
      | none => True
      | some (y, r, _, _) =>
          callArgs y ptr len ptr2 len2 ret ∧ r = ret ∧
            (match x2 with
             | some (y', _, _) => callArgs y' ptr len ptr2 len2 ret
             | none => True)
  | .install ptr' len' _ _ ret', ptr, len, _, _, ret => ptr' = ptr ∧ len' = len ∧ ret' = ret
  | _, _, _, _, _, _ => True

end Flapjack.Compiler.Backend.StackProps
