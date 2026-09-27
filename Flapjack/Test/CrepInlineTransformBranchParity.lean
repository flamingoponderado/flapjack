import Flapjack.Pancake.CrepInline.Pass

/-! Direct HOL-EVAL guards for every clause of `transform_branch_def` on the
exact width-indexed Crep carriers, including loop-depth and handler behavior. -/

namespace Flapjack.Test.CrepInlineTransformBranchParity

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

def transformBranchGuard : Bool :=
  let returnOk := match transformBranchHOLExact 2 [10] returned with
    | .seq (.seq (.assign 10 (.var 2)) .skip) (.break 2) => true
    | _ => false
  let callNoneOk := match transformBranchHOLExact 2 [10] callNone with
    | .seq (.call (some ([10], none)) name [.var 2]) (.break 2) =>
        name == exactName
    | _ => false
  let callReturnsOk := match transformBranchHOLExact 2 [10] callReturns with
    | .call (some ([12], none)) name [.var 2] => name == exactName
    | _ => false
  let callHandlerOk := match transformBranchHOLExact 2 [10] callHandler with
    | .call (some ([12], some (3,
        .seq (.seq (.assign 10 (.var 3)) .skip) (.break 2)))) name [.var 2] =>
        name == exactName
    | _ => false
  let decOk := match transformBranchHOLExact 2 [10] dec with
    | .dec 1 (.const 1) (.seq (.seq (.assign 10 (.var 2)) .skip) (.break 2)) => true
    | _ => false
  let whileOk := match transformBranchHOLExact 2 [10] whl with
    | .while (.const 1) (.seq (.seq (.assign 10 (.var 2)) .skip) (.break 3)) => true
    | _ => false
  let seqOk := match transformBranchHOLExact 2 [10] seq with
    | .seq (.seq (.seq (.assign 10 (.var 2)) .skip) (.break 2)) .skip => true
    | _ => false
  let ifOk := match transformBranchHOLExact 2 [10] ite with
    | .ite (.const 1) (.seq (.seq (.assign 10 (.var 2)) .skip) (.break 2)) .skip => true
    | _ => false
  let defaultOk := match transformBranchHOLExact 2 [10] (.skip : CrepProgHOL 8) with
    | .skip => true
    | _ => false
  returnOk && callNoneOk && callReturnsOk && callHandlerOk && decOk &&
    whileOk && seqOk && ifOk && defaultOk

#guard transformBranchGuard
#eval transformBranchGuard

def runChecks : IO Bool := do
  if transformBranchGuard then
    IO.println "PASS exact HOL transform_branch clauses match direct oracle rows"
  else
    IO.println "FAIL exact HOL transform_branch clauses"
  pure transformBranchGuard

end Flapjack.Test.CrepInlineTransformBranchParity
