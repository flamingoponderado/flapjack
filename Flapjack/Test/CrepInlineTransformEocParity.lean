import Flapjack.Pancake.CrepInline.Pass

/-! Direct HOL-EVAL guards for every clause of `transform_eoc_def` on the exact
width-indexed Crep carriers. -/

namespace Flapjack.Test.CrepInlineTransformEocParity

open Flapjack
open Flapjack.Basis.Pure.MlString

private def exactName : MlString := ofString "f"

private def returned : CrepProgHOL 8 := .return [.var 2, .var 3]
private def callNone : CrepProgHOL 8 := .call none exactName [.var 2]
private def callReturns : CrepProgHOL 8 := .call (some ([12], none)) exactName [.var 2]
private def callHandler : CrepProgHOL 8 :=
  .call (some ([12], some (3, .return [.var 3]))) exactName [.var 2]
private def dec : CrepProgHOL 8 := .dec 1 (.const 1) (.return [.var 2])
private def whl : CrepProgHOL 8 := .while (.const 1) (.return [.var 2])
private def seq : CrepProgHOL 8 := .seq (.return [.var 2]) .skip
private def ite : CrepProgHOL 8 := .ite (.const 1) (.return [.var 2]) .skip

def transformEocGuard : Bool :=
  let returnOk := match transformEocHOLExact [10] returned with
    | .seq (.assign 10 (.var 2)) .skip => true
    | _ => false
  let callNoneOk := match transformEocHOLExact [10] callNone with
    | .call (some ([10], none)) name [.var 2] => name == exactName
    | _ => false
  let callReturnsOk := match transformEocHOLExact [10] callReturns with
    | .call (some ([12], none)) name [.var 2] => name == exactName
    | _ => false
  let callHandlerOk := match transformEocHOLExact [10] callHandler with
    | .call (some ([12], some (3,
        .seq (.assign 10 (.var 3)) .skip))) name [.var 2] =>
        name == exactName
    | _ => false
  let decOk := match transformEocHOLExact [10] dec with
    | .dec 1 (.const 1) (.seq (.assign 10 (.var 2)) .skip) => true
    | _ => false
  let whileOk := match transformEocHOLExact [10] whl with
    | .while (.const 1) (.seq (.assign 10 (.var 2)) .skip) => true
    | _ => false
  let seqOk := match transformEocHOLExact [10] seq with
    | .seq (.seq (.assign 10 (.var 2)) .skip) .skip => true
    | _ => false
  let ifOk := match transformEocHOLExact [10] ite with
    | .ite (.const 1) (.seq (.assign 10 (.var 2)) .skip) .skip => true
    | _ => false
  let defaultOk := match transformEocHOLExact [10] (.skip : CrepProgHOL 8) with
    | .skip => true
    | _ => false
  returnOk && callNoneOk && callReturnsOk && callHandlerOk && decOk &&
    whileOk && seqOk && ifOk && defaultOk

#guard transformEocGuard
#eval transformEocGuard

def runChecks : IO Bool := do
  if transformEocGuard then
    IO.println "PASS exact HOL transform_eoc clauses match direct oracle rows"
  else
    IO.println "FAIL exact HOL transform_eoc clauses"
  pure transformEocGuard

end Flapjack.Test.CrepInlineTransformEocParity
