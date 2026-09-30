import Flapjack.Compiler.Backend.Semantics.StackSem.ShMem
import Flapjack.Compiler.Backend.Semantics.StackSem.Expressions

/-! Untagged, source-shaped fragment of the HOL `evaluate_def` `ShMemOp` clause
(`cakeml/compiler/backend/semantics/stackSemScript.sml:922-927`; the bead's
911-918 lies inside the preceding clause). It covers exactly one constructor and
is not the total HOL `evaluate`; the outer `NONE` means this module does not
handle the constructor, so an unported clause is never silently reported as
`Error`.

The effective address is the tagged `word_exp` of `Op Add [Var a; Const w]`;
the exact `word_exp` miss returns `(SOME Error, s)`, a zero clock returns
`(SOME TimeOut, empty_env s)`, and otherwise the tagged `sh_mem_op` dispatch is
applied to `dec_clock s`. The total evaluator and its production refinement are
tracked by flapjack-y19g (parent flapjack-y19g.14). No `@[hol]` tag applies to
this partial case helper. -/

namespace Flapjack.StackSemShMemOpCase

open StackSemShMem StackSemExpressions StackSemStateOps
open Compiler.Backend.StackLang

/-- The HOL `evaluate (ShMemOp op r (Addr a w), s)` branch. `word_exp` on the
effective-address expression gates the clause: a miss returns `(SOME Error, s)`
with the original state, `clock = 0` returns `(SOME TimeOut, empty_env s)`, and
otherwise the shared-memory operator runs on `dec_clock s`. -/
def evaluateShMemOp {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (s : StackSemStateFiniteExact width C F) :
    Option (Option (StackSemResult width) × StackSemStateFiniteExact width C F) :=
  match program with
  | .shMemOp op r address =>
      some (match address with
        | .addr a w =>
            match wordExp s (.op .add [.var a, .const w]) with
            | some a' => if s.clock = 0 then (some .timeOut, emptyEnv s)
                         else shMemOp op r a' (decClock s)
            | none => (some .error, s))
  | _ => none

end Flapjack.StackSemShMemOpCase
