import Flapjack.Pancake.CrepInline.Pass

/-! Direct HOL-EVAL guards for every clause of `has_return_def` on the exact
width-indexed Crep carriers. -/

namespace Flapjack.Test.CrepInlineHasReturnParity

open Flapjack
open Flapjack.Basis.Pure.MlString

private def exactName : MlString := ofString "f"

private def hasReturnGuard : Bool :=
  hasReturnHOLExact (.return [.var 2] : CrepProgHOL 8) &&
  hasReturnHOLExact (.call none exactName [] : CrepProgHOL 8) &&
  !(hasReturnHOLExact (.call (some ([10], none)) exactName [] : CrepProgHOL 8)) &&
  hasReturnHOLExact
    (.call (some ([], some (3, .return [.var 2]))) exactName [] : CrepProgHOL 8) &&
  hasReturnHOLExact (.dec 1 (.const 1) (.return [.var 2]) : CrepProgHOL 8) &&
  hasReturnHOLExact (.seq .skip (.return [.var 2]) : CrepProgHOL 8) &&
  hasReturnHOLExact (.ite (.const 1) .skip (.return [.var 2]) : CrepProgHOL 8) &&
  hasReturnHOLExact (.while (.const 1) (.return [.var 2]) : CrepProgHOL 8) &&
  !(hasReturnHOLExact (.skip : CrepProgHOL 8))

#guard hasReturnGuard
#eval hasReturnGuard

def runChecks : IO Bool := do
  if hasReturnGuard then
    IO.println "PASS exact HOL has_return clauses match direct oracle rows"
  else
    IO.println "FAIL exact HOL has_return"
  pure hasReturnGuard

end Flapjack.Test.CrepInlineHasReturnParity
