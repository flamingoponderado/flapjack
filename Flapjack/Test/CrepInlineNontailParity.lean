import Flapjack.Pancake.CrepInline.Pass

/-! Direct HOL-EVAL guards for `inline_nontail_def` on the exact Crep carriers,
including initialization, argument setup, MAP2 truncation and Skip from a
length-mismatched nested declaration. -/

namespace Flapjack.Test.CrepInlineNontailParity

open Flapjack

private def body : CrepProgHOL 8 := .return [.var 8]
private def argumentValues : List (CrepExpHOL 8) := [.const 7]

private def scalar : CrepProgHOL 8 :=
  inlineNontailHOLExact body [10] [20] [30] argumentValues [5]

private def map2Truncates : CrepProgHOL 8 :=
  inlineNontailHOLExact body [10, 11] [20] [30] argumentValues [5]

private def argumentShapeMismatch : CrepProgHOL 8 :=
  inlineNontailHOLExact body [10] [20] [30] argumentValues []

def inlineNontailGuard : Bool :=
  let scalarOk := match scalar with
    | .dec 20 (.const 0)
        (.seq (.dec 30 (.const 7) (.dec 5 (.var 30) (.return [.var 8])))
          (.seq (.assign 10 (.var 20)) .skip)) => true
    | _ => false
  let map2Ok := match map2Truncates with
    | .dec 20 (.const 0)
        (.seq (.dec 30 (.const 7) (.dec 5 (.var 30) (.return [.var 8])))
          (.seq (.assign 10 (.var 20)) .skip)) => true
    | _ => false
  let mismatchOk := match argumentShapeMismatch with
    | .dec 20 (.const 0)
        (.seq (.dec 30 (.const 7) .skip) (.seq (.assign 10 (.var 20)) .skip)) => true
    | _ => false
  scalarOk && map2Ok && mismatchOk

#guard inlineNontailGuard
#eval inlineNontailGuard

def runChecks : IO Bool := do
  if inlineNontailGuard then
    IO.println "PASS exact HOL inline_nontail matches direct oracle rows"
  else
    IO.println "FAIL exact HOL inline_nontail"
  pure inlineNontailGuard

end Flapjack.Test.CrepInlineNontailParity
