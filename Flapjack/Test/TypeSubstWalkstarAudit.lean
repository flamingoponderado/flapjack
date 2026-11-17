import Flapjack.HolRef.TypeSubstWalkstarAudit
import Flapjack.Compiler.Inference.InferProps.TypeSubstWalkstar

open Lean Meta Flapjack
open Flapjack.Compiler.Inference.InferProps.TypeSubstWalkstar

private noncomputable abbrev walkAlias := Flapjack.Compiler.Inference.Unify.tWalkstar
private abbrev guardAlias := Flapjack.Compiler.Inference.Unify.tWfs

private def replaceBinderCarrier : Expr → Nat → Expr
  | .forallE name _ body info, 0 => .forallE name (mkConst ``Bool) body info
  | .forallE name type body info, n + 1 => .forallE name type (replaceBinderCarrier body n) info
  | type, _ => type

run_meta do
  let info ← getConstInfo ``substInferSubstSwap
  let valid ← typeSubstWalkstarStatementProblems info.type
  unless valid.isEmpty do throwError "walkstar statement audit rejected theorem: {valid}"
  let bundle ← typeSubstWalkstarBundleProblems ``substInferSubstSwap
  unless bundle.isEmpty do throwError "walkstar bundle audit rejected theorem: {bundle}"
  if (← typeSubstWalkstarBundleProblems ``True).isEmpty then
    throwError "walkstar bundle audit accepted an unrelated declaration"
  let conjuncts := info.type.getAppArgs
  if (← typeSubstWalkstarStatementProblems conjuncts[0]!).isEmpty then
    throwError "walkstar audit accepted a missing conjunct"
  let reversed := mkApp2 (mkConst ``And) conjuncts[1]! conjuncts[0]!
  if (← typeSubstWalkstarStatementProblems reversed).isEmpty then
    throwError "walkstar audit accepted reversed conjuncts"
  for side in [0:2] do
    let wrongCarrier := replaceBinderCarrier conjuncts[side]! 2
    let altered := if side == 0 then mkApp2 (mkConst ``And) wrongCarrier conjuncts[1]!
      else mkApp2 (mkConst ``And) conjuncts[0]! wrongCarrier
    if (← typeSubstWalkstarStatementProblems altered).isEmpty then
      throwError "walkstar audit accepted an incorrect map carrier"
    forallTelescope conjuncts[side]! fun args conclusion => do
      withLocalDeclD `h (mkConst ``True) fun h => do
        let fake ← mkForallFVars ((args.extract 0 4).push h) conclusion
        let altered := if side == 0 then mkApp2 (mkConst ``And) fake conjuncts[1]!
          else mkApp2 (mkConst ``And) conjuncts[0]! fake
        if (← typeSubstWalkstarStatementProblems altered).isEmpty then
          throwError "walkstar audit accepted a dropped well-formedness premise"
      let aliasGuard := mkApp (mkConst ``guardAlias) args[2]!
      withLocalDeclD `h aliasGuard fun h => do
        let fake ← mkForallFVars ((args.extract 0 4).push h) conclusion
        let altered := if side == 0 then mkApp2 (mkConst ``And) fake conjuncts[1]!
          else mkApp2 (mkConst ``And) conjuncts[0]! fake
        if (← typeSubstWalkstarStatementProblems altered).isEmpty then
          throwError "walkstar audit accepted an indirect well-formedness premise"
      let changed := conclusion.replace fun expr =>
        if expr == args[3]! then some (mkNatLit 0) else none
      if changed == conclusion then throwError "offset mutation did not change conclusion"
      let fake ← mkForallFVars args changed
      let altered := if side == 0 then mkApp2 (mkConst ``And) fake conjuncts[1]!
        else mkApp2 (mkConst ``And) conjuncts[0]! fake
      if (← typeSubstWalkstarStatementProblems altered).isEmpty then
        throwError "walkstar audit accepted a changed offset"
      let aliased := conclusion.replace fun expr =>
        if expr.isConstOf ``Flapjack.Compiler.Inference.Unify.tWalkstar then some (mkConst ``walkAlias) else none
      if aliased == conclusion then throwError "walkstar alias mutation did not change conclusion"
      let fake ← mkForallFVars args aliased
      let altered := if side == 0 then mkApp2 (mkConst ``And) fake conjuncts[1]!
        else mkApp2 (mkConst ``And) conjuncts[0]! fake
      if (← typeSubstWalkstarStatementProblems altered).isEmpty then
        throwError "walkstar audit accepted an indirect walkstar operation"
      let sides := conclusion.getAppArgs
      let rhsAlias := sides[2]!.replace fun expr =>
        if expr.isConstOf ``Flapjack.Compiler.Inference.Unify.tWalkstar then some (mkConst ``walkAlias) else none
      if rhsAlias == sides[2]! then throwError "nested walkstar alias mutation did not change the right side"
      let changedEq ← mkEq sides[1]! rhsAlias
      let fake ← mkForallFVars args changedEq
      let altered := if side == 0 then mkApp2 (mkConst ``And) fake conjuncts[1]!
        else mkApp2 (mkConst ``And) conjuncts[0]! fake
      if (← typeSubstWalkstarStatementProblems altered).isEmpty then
        throwError "walkstar audit accepted an indirect nested walkstar operation"
  let witness ← getConstInfo ``holFmapAsFiniteSupportNestedWalkstarWitness
  forallTelescope witness.type fun args result => do
    let broad ← mkAppM ``FiniteMapBroad.toBroad #[args[0]!]
    let roundtrip ← mkAppM ``FiniteMapBroad.ofBroad #[broad]
    let vacuous := result.replace fun expr => if expr == roundtrip then some args[0]! else none
    if vacuous == result then throwError "walkstar codec mutation did not change the witness"
    let fake ← mkForallFVars args vacuous
    if (← typeSubstWalkstarWitnessProblems fake).isEmpty then
      throwError "walkstar audit accepted a vacuous codec witness"
    withLocalDeclD `extra (mkConst ``True) fun extra => do
      let conditional ← mkForallFVars (args.push extra) result
      if (← typeSubstWalkstarWitnessProblems conditional).isEmpty then
        throwError "walkstar audit accepted a conditional codec witness"
