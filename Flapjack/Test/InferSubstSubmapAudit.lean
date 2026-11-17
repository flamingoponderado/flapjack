import Flapjack.HolRef.InferSubstSubmapAudit
import Flapjack.Compiler.Inference.InferProps.Substitution

open Lean Meta Flapjack
open Flapjack.Compiler.Inference.InferProps.Substitution

private def replaceBinderCarrier : Expr → Nat → Expr
  | .forallE name _ body info, 0 => .forallE name (mkConst ``Bool) body info
  | .forallE name type body info, n + 1 => .forallE name type (replaceBinderCarrier body n) info
  | type, _ => type

run_meta do
  let theoremInfo ← getConstInfo ``inferSubstSubmap
  let valid ← inferSubstSubmapBinderProblems theoremInfo.type
  unless valid.isEmpty do throwError "submap binder audit rejected the theorem: {valid}"
  let bundle ← inferSubstSubmapBundleProblems ``inferSubstSubmap
  unless bundle.isEmpty do throwError "submap bundle audit rejected the theorem: {bundle}"
  if (← inferSubstSubmapBundleProblems ``True).isEmpty then
    throwError "submap bundle audit accepted an unrelated declaration"
  let conjuncts := theoremInfo.type.getAppArgs
  let swapped := mkApp2 (mkConst ``And) conjuncts[1]! conjuncts[0]!
  if (← inferSubstSubmapBinderProblems swapped).isEmpty then
    throwError "submap binder audit accepted reversed conjuncts"
  if (← inferSubstSubmapBinderProblems conjuncts[0]!).isEmpty then
    throwError "submap binder audit accepted a missing conjunct"
  for side in [0:2] do
    match conjuncts[side]! with
    | .forallE name _ body binderInfo =>
      let bad := Expr.forallE name (mkConst ``Bool) body binderInfo
      let mutated := if side == 0 then mkApp2 (mkConst ``And) bad conjuncts[1]!
        else mkApp2 (mkConst ``And) conjuncts[0]! bad
      if (← inferSubstSubmapBinderProblems mutated).isEmpty then
        throwError "submap binder audit accepted a changed input carrier"
    | _ => throwError "expected a universally quantified conjunct"
    for binder in [1:3] do
      let bad := replaceBinderCarrier conjuncts[side]! binder
      let mutated := if side == 0 then mkApp2 (mkConst ``And) bad conjuncts[1]!
        else mkApp2 (mkConst ``And) conjuncts[0]! bad
      if (← inferSubstSubmapBinderProblems mutated).isEmpty then
        throwError "submap binder audit accepted a changed map carrier"
  forallTelescope conjuncts[0]! fun args conclusion => do
    let changed := conclusion.replace fun expr =>
      if expr == args[2]! then some args[1]! else none
    if changed == conclusion then throwError "map mutation did not change the conclusion"
    let fake ← mkForallFVars args changed
    let fakeTheorem := mkApp2 (mkConst ``And) fake conjuncts[1]!
    if (← inferSubstSubmapBinderProblems fakeTheorem).isEmpty then
      throwError "submap binder audit accepted a repeated map in the conclusion"
    let premise ← args[4]!.fvarId!.getDecl
    let weakened := premise.type.replace fun expr =>
      if expr == args[2]! then some args[1]! else none
    if weakened == premise.type then throwError "map mutation did not change the premise"
    withLocalDeclD `h weakened fun h => do
      let fake ← mkForallFVars ((args.extract 0 4).push h) conclusion
      let fakeTheorem := mkApp2 (mkConst ``And) fake conjuncts[1]!
      if (← inferSubstSubmapBinderProblems fakeTheorem).isEmpty then
        throwError "submap binder audit accepted a repeated map in the premise"
    withLocalDeclD `h (mkConst ``True) fun h => do
      let fake ← mkForallFVars ((args.extract 0 4).push h) conclusion
      let fakeTheorem := mkApp2 (mkConst ``And) fake conjuncts[1]!
      if (← inferSubstSubmapBinderProblems fakeTheorem).isEmpty then
        throwError "submap binder audit accepted a dropped premise"
  forallTelescope conjuncts[1]! fun args conclusion => do
    let changed := conclusion.replace fun expr =>
      if expr == args[2]! then some args[1]! else none
    if changed == conclusion then throwError "list conclusion mutation did not change the statement"
    let fakeConclusion ← mkForallFVars args changed
    let fakeTheorem := mkApp2 (mkConst ``And) conjuncts[0]! fakeConclusion
    if (← inferSubstSubmapBinderProblems fakeTheorem).isEmpty then
      throwError "submap binder audit accepted a repeated map in the list conclusion"
    let premise ← args[4]!.fvarId!.getDecl
    let weakened := premise.type.replace fun expr =>
      if expr == args[2]! then some args[1]! else none
    if weakened == premise.type then throwError "list map mutation did not change the premise"
    withLocalDeclD `h weakened fun h => do
      let fake ← mkForallFVars ((args.extract 0 4).push h) conclusion
      let fakeTheorem := mkApp2 (mkConst ``And) conjuncts[0]! fake
      if (← inferSubstSubmapBinderProblems fakeTheorem).isEmpty then
        throwError "submap binder audit accepted a repeated list-case map"
    let changedBound := premise.type.replace fun expr =>
      let parts := expr.getAppArgs
      if expr.getAppFn.isConstOf ``LE.le && parts.size >= 2 && parts[parts.size - 2]! == args[3]! then
        some <| mkAppN expr.getAppFn (parts.set! (parts.size - 2) (mkNatLit 0))
      else none
    if changedBound == premise.type then throwError "bound mutation did not change the premise"
    withLocalDeclD `h changedBound fun h => do
      let fake ← mkForallFVars ((args.extract 0 4).push h) conclusion
      let fakeTheorem := mkApp2 (mkConst ``And) conjuncts[0]! fake
      if (← inferSubstSubmapBinderProblems fakeTheorem).isEmpty then
        throwError "submap binder audit accepted a changed lower bound"
