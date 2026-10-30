import Flapjack.Compiler.Backend.FlatToClos.Helpers
import Flapjack.Compiler.Backend.Semantics.ClosProps.Globals
import Flapjack.Compiler.Backend.Semantics.ClosProps.NoMti

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

/-- Flapjack helper: the generated string-copy checks contain no unsafe closure. -/
theorem copyByteStr_globalSafe (t : Tra) :
    Flapjack.Compiler.Backend.ClosProps.esgcFree (copyByteStr t) := by
  simp [copyByteStr, copyChecks, subscriptRaise,
    Flapjack.Compiler.Backend.ClosProps.esgcFree, Flapjack.Compiler.Backend.ClosProps.esgcFreeList]

/-- Flapjack helper: the generated array-copy checks contain no unsafe closure. -/
theorem copyByteAw8_globalSafe (t : Tra) :
    Flapjack.Compiler.Backend.ClosProps.esgcFree (copyByteAw8 t) := by
  simp [copyByteAw8, copyChecks, subscriptRaise,
    Flapjack.Compiler.Backend.ClosProps.esgcFree, Flapjack.Compiler.Backend.ClosProps.esgcFreeList]

/-- Flapjack helper: the generated string-copy checks use pre-MTI syntax. -/
theorem copyByteStr_noMti (t : Tra) : ClosProps.noMti (copyByteStr t) := by
  simp [copyByteStr, copyChecks, subscriptRaise, ClosProps.noMti, ClosProps.noMtiList]

/-- Flapjack helper: the generated array-copy checks use pre-MTI syntax. -/
theorem copyByteAw8_noMti (t : Tra) : ClosProps.noMti (copyByteAw8 t) := by
  simp [copyByteAw8, copyChecks, subscriptRaise, ClosProps.noMti, ClosProps.noMtiList]

/-- Flapjack helper: string-copy checks contribute no global writes. -/
theorem copyByteStr_noGlobals (t : Tra) :
    Flapjack.Compiler.Backend.ClosProps.setGlobals (copyByteStr t) =
      Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag := by
  funext key
  simp [copyByteStr, copyChecks, subscriptRaise,
    Flapjack.Compiler.Backend.ClosProps.setGlobals, Flapjack.Compiler.Backend.ClosProps.elistGlobals,
    Flapjack.Compiler.Backend.ClosProps.opGlobalBag, Flapjack.Compiler.Backend.FlatProps.unionGlobalBag,
    Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag]

/-- Flapjack helper: array-copy checks contribute no global writes. -/
theorem copyByteAw8_noGlobals (t : Tra) :
    Flapjack.Compiler.Backend.ClosProps.setGlobals (copyByteAw8 t) =
      Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag := by
  funext key
  simp [copyByteAw8, copyChecks, subscriptRaise,
    Flapjack.Compiler.Backend.ClosProps.setGlobals, Flapjack.Compiler.Backend.ClosProps.elistGlobals,
    Flapjack.Compiler.Backend.ClosProps.opGlobalBag, Flapjack.Compiler.Backend.FlatProps.unionGlobalBag,
    Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag]

end Flapjack.Compiler.Backend.FlatToClos
