import Flapjack.Compiler.Backend.FlatToClos.Helpers

/-! Closure expressions for checked byte-copy operations. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.Compiler.Backend.BackendCommon

/-- The shared subscript exception used by checked copy operations. This is
Flapjack infrastructure for the source's repeated expression. -/
private def subscriptRaise (t : Tra) : ClosLang.Exp :=
  .raise t (.op t (.blockOp (.cons 3)) [])

/-- Build the three checks shared by both byte-copy operations. This expands
the source's ML `check1` quotation, including the original variable order. -/
private def copyChecks (t : Tra) (v2 v1 v0 : Nat) (body : ClosLang.Exp) : ClosLang.Exp :=
  .ifThenElse t (.op t (.intOp .less) [.op t (.intOp (.const 0)) [], .var t v2])
    (subscriptRaise t)
    (.ifThenElse t (.op t (.intOp .less) [.op t (.intOp (.const 0)) [], .var t v1])
      (subscriptRaise t)
      (.ifThenElse t (.op t (.memOp (.boundsCheckByte true))
        [.op t (.intOp .add) [.var t v2, .var t v1], .var t v0]) body (subscriptRaise t)))

/-- Checked string-to-byte copy body. -/
@[hol "cakeml/compiler/backend/flat_to_closScript.sml" "CopyByteStr_def"]
def copyByteStr (t : Tra) : ClosLang.Exp :=
  copyChecks t 0 1 2 (.op t (.memOp (.copyByte true)) [.var t 0, .var t 1, .var t 2])

/-- Checked byte-array-to-byte copy body. -/
@[hol "cakeml/compiler/backend/flat_to_closScript.sml" "CopyByteAw8_def"]
def copyByteAw8 (t : Tra) : ClosLang.Exp :=
  copyChecks t 2 3 4
    (.ifThenElse t (.op t (.intOp .less) [.op t (.intOp (.const 0)) [], .var t 0])
      (subscriptRaise t)
      (.ifThenElse t (.op t (.memOp (.boundsCheckByte true))
        [.op t (.intOp .add) [.var t 2, .var t 0], .var t 1])
        (.op t (.memOp (.copyByte false))
          [.var t 0, .var t 1, .var t 2, .var t 3, .var t 4])
        (subscriptRaise t)))

end Flapjack.Compiler.Backend.FlatToClos
