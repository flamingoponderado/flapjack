import Flapjack.HolRef.UnifyEqTunifyAudit
import Flapjack.HOL.Unification.UnifDef.Choice

open Lean Meta Flapjack
open Flapjack.HOL.Unification

private noncomputable abbrev chosenAlias := @specifiedUnify
private abbrev guardAlias := @wfs

private def replaceBinderCarrier : Expr → Nat → Expr
  | .forallE name _ body info, 0 => .forallE name (mkConst ``Bool) body info
  | .forallE name type body info, n + 1 => .forallE name type (replaceBinderCarrier body n) info
  | type, _ => type

private def renameMapBinder : Expr → Expr
  | .forallE name type (.forallE _ mapType body mapInfo) info =>
      .forallE name type (.forallE `other mapType body mapInfo) info
  | type => type

run_meta do
  let info ← getConstInfo ``specifiedUnifyEqAux
  let valid ← unifyEqTunifyStatementProblems info.type
  unless valid.isEmpty do throwError "unifier audit rejected the source-shaped statement: {valid}"
  let bundle ← unifyEqTunifyBundleProblems ``specifiedUnifyEqAux
  unless bundle.isEmpty do throwError "unifier audit rejected the source dependency bundle: {bundle}"
  if (← unifyEqTunifyBundleProblems ``True).isEmpty then
    throwError "unifier audit accepted an unrelated declaration"
  let proofDeps := #[``specifiedUnifyEquation, ``tunifyAuxEquation, ``tunifyAuxUP, ``tunifyAuxInd]
  unless (unifyEqTunifyProofDependencyProblems proofDeps).isEmpty do
    throwError "unifier audit rejected all required proof dependencies"
  for required in proofDeps do
    if (unifyEqTunifyProofDependencyProblems (proofDeps.filter (· != required))).isEmpty then
      throwError "unifier audit accepted missing proof dependency {required}"
  for index in [1:4] do
    if (← unifyEqTunifyStatementProblems (replaceBinderCarrier info.type index)).isEmpty then
      throwError "unifier audit accepted a changed carrier at binder {index}"
  if (← unifyEqTunifyStatementProblems (renameMapBinder info.type)).isEmpty then
    throwError "unifier audit accepted a renamed map binder"
  forallTelescope info.type fun args conclusion => do
    withLocalDeclD `h (mkConst ``True) fun h => do
      let missingGuard ← mkForallFVars ((args.extract 0 4).push h) conclusion
      if (← unifyEqTunifyStatementProblems missingGuard).isEmpty then
        throwError "unifier audit accepted a missing well-formedness guard"
    let aliasGuard ← mkAppM ``guardAlias #[args[1]!]
    withLocalDeclD `h aliasGuard fun h => do
      let indirectGuard ← mkForallFVars ((args.extract 0 4).push h) conclusion
      if (← unifyEqTunifyStatementProblems indirectGuard).isEmpty then
        throwError "unifier audit accepted an indirect well-formedness guard"
    let swapped ← mkEq (conclusion.getAppArgs[2]!) (conclusion.getAppArgs[1]!)
    let wrongConclusion ← mkForallFVars args swapped
    if (← unifyEqTunifyStatementProblems wrongConclusion).isEmpty then
      throwError "unifier audit accepted a reversed conclusion"
    let changed := conclusion.replace fun expr => if expr == args[3]! then some args[2]! else none
    if changed == conclusion then throwError "second-term mutation did not change the conclusion"
    let repeatedTerm ← mkForallFVars args changed
    if (← unifyEqTunifyStatementProblems repeatedTerm).isEmpty then
      throwError "unifier audit accepted identified term arguments"
    let aliased := conclusion.replace fun expr =>
      if expr.isConstOf ``specifiedUnify then some (mkConst ``chosenAlias expr.constLevels!) else none
    if aliased == conclusion then throwError "unifier alias mutation did not change the conclusion"
    let indirectConclusion ← mkForallFVars args aliased
    if (← unifyEqTunifyStatementProblems indirectConclusion).isEmpty then
      throwError "unifier audit accepted an indirect chosen operation"
    withLocalDeclD `h (mkConst ``True) fun extra => do
      let extraPremise ← mkForallFVars (args.push extra) conclusion
      if (← unifyEqTunifyStatementProblems extraPremise).isEmpty then
        throwError "unifier audit accepted an extra premise"
