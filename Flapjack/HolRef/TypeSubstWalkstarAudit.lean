module

public meta import Lean
public meta import Lean.Util.CollectAxioms
public meta import Flapjack.HolRef

public meta section

/-! Elaborated checks for the two independently quantified maps in the
type-substitution/walkstar theorem. These checks do not establish source fidelity. -/
namespace Flapjack
open Lean Meta

private def typeSubstWalkstarExpected (args : Array Expr) (listCase : Bool) : MetaM Expr := do
  let input := args[0]!
  let names := args[1]!
  let substitution := args[2]!
  let offset := args[3]!
  let walk := mkConst `Flapjack.Compiler.Inference.Unify.tWalkstar
  let subst := mkConst `Flapjack.Compiler.Inference.Infer.inferTypeSubst
  let length ← mkAppM ``List.length #[names]
  let indices ← mkAppM ``List.range #[length]
  let (plain, walked) ← withLocalDeclD `n (mkConst ``Nat) fun n => do
    let index ← mkAppM ``HAdd.hAdd #[offset, n]
    let varExpr ← mkAppM `Flapjack.Compiler.Inference.InferT.uvar #[index]
    let plain ← mkLambdaFVars #[n] varExpr
    let walked ← mkLambdaFVars #[n] (mkApp2 walk substitution varExpr)
    return (plain, walked)
  let plainValues ← mkAppM ``List.map #[plain, indices]
  let walkedValues ← mkAppM ``List.map #[walked, indices]
  let plainZip ← mkAppM ``List.zip #[names, plainValues]
  let walkedZip ← mkAppM ``List.zip #[names, walkedValues]
  let plainSubst := mkApp subst plainZip
  let walkedSubst := mkApp subst walkedZip
  if listCase then
    let mapped ← mkAppM ``List.map #[plainSubst, input]
    let lhs ← mkAppM ``List.map #[mkApp walk substitution, mapped]
    let rhs ← mkAppM ``List.map #[walkedSubst, input]
    mkEq lhs rhs
  else
    mkEq (mkApp2 walk substitution (mkApp plainSubst input)) (mkApp walkedSubst input)

private def typeSubstWalkstarConjunctProblems (type : Expr) (listCase : Bool) : MetaM (Array String) := do
  forallTelescope type fun args conclusion => do
    unless args.size == 5 do return #[s!"expected four variables and one premise, got {args.size}"]
    let semanticT := mkConst `Flapjack.TypeSystemHOL.SemanticT
    let inferT := mkConst `Flapjack.Compiler.Inference.InferT
    let mlString := mkConst `Flapjack.Basis.Pure.MlString.MlString
    let map := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) (mkConst ``Nat) inferT
    let input := if listCase then mkApp (mkConst ``List [Level.zero]) semanticT else semanticT
    let names := mkApp (mkConst ``List [Level.zero]) mlString
    let carriers := #[input, names, map, mkConst ``Nat]
    for i in [0:4] do
      let binder ← args[i]!.fvarId!.getDecl
      unless binder.binderInfo == .default do return #[s!"binder {i + 1} must be explicit"]
      unless ← isDefEq binder.type carriers[i]! do return #[s!"binder {i + 1} has the wrong carrier"]
      if i == 2 && binder.userName != `s then return #["third binder must be s"]
    let premise ← args[4]!.fvarId!.getDecl
    let guard := premise.type.consumeMData
    unless premise.binderInfo == .default &&
        guard.getAppFn.isConstOf `Flapjack.Compiler.Inference.Unify.tWfs &&
        guard.getAppArgs == #[args[2]!] do
      return #["the sole premise must directly assert well-formedness of this map"]
    let eq := conclusion.consumeMData
    let sides := eq.getAppArgs
    unless eq.getAppFn.isConstOf ``Eq && sides.size == 3 do return #["conclusion must be a direct equality"]
    let walk := `Flapjack.Compiler.Inference.Unify.tWalkstar
    let subst := `Flapjack.Compiler.Inference.Infer.inferTypeSubst
    let lhs := sides[1]!.consumeMData
    let rhs := sides[2]!.consumeMData
    if listCase then
      let lhsArgs := lhs.getAppArgs
      let rhsArgs := rhs.getAppArgs
      unless lhs.getAppFn.isConstOf ``List.map && lhsArgs.size == 4 &&
          rhs.getAppFn.isConstOf ``List.map && rhsArgs.size == 4 && rhsArgs[3]! == args[0]! do
        return #["list conclusion must directly map over the original list"]
      let walker := lhsArgs[2]!.consumeMData
      let inner := lhsArgs[3]!.consumeMData
      let innerArgs := inner.getAppArgs
      unless walker.getAppFn.isConstOf walk && walker.getAppArgs == #[args[2]!] &&
          inner.getAppFn.isConstOf ``List.map && innerArgs.size == 4 && innerArgs[3]! == args[0]! &&
          innerArgs[2]!.getAppFn.isConstOf subst && rhsArgs[2]!.getAppFn.isConstOf subst do
        return #["list conclusion must directly apply the reviewed substitution and walkstar operations"]
    else
      let lhsArgs := lhs.getAppArgs
      let rhsArgs := rhs.getAppArgs
      unless lhs.getAppFn.isConstOf walk && lhsArgs.size == 2 && lhsArgs[0]! == args[2]! &&
          lhsArgs[1]!.getAppFn.isConstOf subst && rhs.getAppFn.isConstOf subst &&
          rhsArgs.size == 2 && rhsArgs[1]! == args[0]! do
        return #["type conclusion must directly apply the reviewed substitution and walkstar operations"]
    let expected ← typeSubstWalkstarExpected args listCase
    unless conclusion == expected do
      return #["conclusion must retain the complete zipped substitution and walkstar equations"]
    return #[]

/-- Check both groups separately, including their complete HOL-shaped equations. -/
def typeSubstWalkstarStatementProblems (type : Expr) : MetaM (Array String) := do
  let type := type.consumeMData
  let conjuncts := type.getAppArgs
  unless type.getAppFn.isConstOf ``And && conjuncts.size == 2 do
    return #["the theorem must contain two independently quantified conjuncts"]
  let first ← typeSubstWalkstarConjunctProblems conjuncts[0]! false
  let second ← typeSubstWalkstarConjunctProblems conjuncts[1]! true
  return first ++ second

/-- Check the unconditional codec on the specific inference-map carrier. -/
def typeSubstWalkstarWitnessProblems (type : Expr) : MetaM (Array String) := do
  forallTelescope type fun args result => do
    unless args.size == 2 do return #["walkstar codec requires exactly a map and a key"]
    let mapType := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) (mkConst ``Nat)
      (mkConst `Flapjack.Compiler.Inference.InferT)
    let mapBinder ← args[0]!.fvarId!.getDecl
    let keyBinder ← args[1]!.fvarId!.getDecl
    unless mapBinder.binderInfo == .default && keyBinder.binderInfo == .default && mapBinder.userName == `map do
      return #["walkstar codec binders must be explicit and name the map"]
    unless (← isDefEq mapBinder.type mapType) && (← isDefEq keyBinder.type (mkConst ``Nat)) do
      return #["walkstar codec binders have incorrect carriers"]
    let broad ← mkAppM `Flapjack.FiniteMapBroad.toBroad #[args[0]!]
    let roundtrip ← mkAppM `Flapjack.FiniteMapBroad.ofBroad #[broad]
    let leftLookup ← mkAppM `Flapjack.HolFiniteMapExact.lookup #[roundtrip, args[1]!]
    let rightLookup ← mkAppM `Flapjack.HolFiniteMapExact.lookup #[args[0]!, args[1]!]
    let lookupEq ← mkEq leftLookup rightLookup
    let leftSupport ← mkAppM `Flapjack.HolFiniteMapExact.finiteSupport #[roundtrip]
    let rightSupport ← mkAppM `Flapjack.HolFiniteMapExact.finiteSupport #[args[0]!]
    let supportEq ← mkEq leftSupport rightSupport
    let mapEq ← mkEq roundtrip args[0]!
    let expected := mkApp2 (mkConst ``And) lookupEq (mkApp2 (mkConst ``And) supportEq mapEq)
    unless result == expected do return #["walkstar codec must preserve lookup, support and the complete map"]
    return #[]

/-- Check the source-reviewed theorem, shared witness, dependency provenance,
    and axiom closure. Manifest and source validation are separate. -/
def typeSubstWalkstarBundleProblems (target : Name) : MetaM (Array String) := do
  let expected := `Flapjack.Compiler.Inference.InferProps.TypeSubstWalkstar.substInferSubstSwap
  unless target == expected do return #["walkstar qualifier requires the reviewed theorem"]
  let env ← getEnv
  let owner (name : Name) :=
    match env.getModuleIdxFor? name with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  let dependencies := #[
    (`Flapjack.HolFiniteMapExact, `Flapjack.FiniteMap.Exact),
    (`Flapjack.Compiler.Inference.InferT, `Flapjack.Compiler.Inference.InferT),
    (`Flapjack.TypeSystemHOL.SemanticT, `Flapjack.TypeSystemHOL),
    (`Flapjack.Basis.Pure.MlString.MlString, `Flapjack.Basis.Pure.MlString),
    (`Flapjack.Compiler.Inference.Infer.inferTypeSubst, `Flapjack.Compiler.Inference.Infer),
    (`Flapjack.Compiler.Inference.Infer.inferTypeSubstList, `Flapjack.Compiler.Inference.Infer),
    (`Flapjack.Compiler.Inference.Unify.tWfs, `Flapjack.Compiler.Inference.Unify.Substitution),
    (`Flapjack.Compiler.Inference.Unify.tWalkstar, `Flapjack.Compiler.Inference.Unify.Walkstar),
    (`Flapjack.Compiler.Inference.Unify.walkstarEqn, `Flapjack.Compiler.Inference.Unify.Walkstar),
    (`Flapjack.Compiler.Inference.Unify.tWalkstarEqn1, `Flapjack.Compiler.Inference.Unify.Walkstar),
    (`Flapjack.Compiler.Inference.Unify.tWalk, `Flapjack.Compiler.Inference.Unify.Walk.Term),
    (`Flapjack.Compiler.Inference.Unify.tWalkEqn, `Flapjack.Compiler.Inference.Unify.Walk.Term),
    (`Flapjack.Compiler.Inference.Unify.tVwalk, `Flapjack.Compiler.Inference.Unify.Walk),
    (`Flapjack.Compiler.Inference.Unify.tVwalkEq, `Flapjack.Compiler.Inference.Unify.Walk),
    (`Flapjack.FiniteMapBroad, `Flapjack.FiniteMap.BroadCodec),
    (`Flapjack.FiniteMapBroad.toBroad, `Flapjack.FiniteMap.BroadCodec),
    (`Flapjack.FiniteMapBroad.ofBroad, `Flapjack.FiniteMap.BroadCodec)]
  let mut problems := #[]
  for (name, moduleName) in dependencies do
    if (env.find? name).isNone || owner name != moduleName then
      problems := problems.push s!"{name} is missing or has the wrong defining module"
  let refs : Array (Name × HolRef) := #[
    (`Flapjack.Compiler.Inference.InferT,
      { path := "cakeml/compiler/inference/infer_tScript.sml", name := "infer_t" }),
    (`Flapjack.TypeSystemHOL.SemanticT,
      { path := "cakeml/semantics/typeSystemScript.sml", name := "t" }),
    (`Flapjack.Basis.Pure.MlString.MlString,
      { path := "cakeml/basis/pure/mlstringScript.sml", name := "mlstring" }),
    (`Flapjack.Compiler.Inference.Infer.inferTypeSubst,
      { path := "cakeml/compiler/inference/inferScript.sml", name := "infer_type_subst_def" }),
    (`Flapjack.Compiler.Inference.Infer.inferTypeSubstList,
      { path := "cakeml/compiler/inference/inferScript.sml", name := "infer_type_subst_def" }),
    (`Flapjack.Compiler.Inference.Unify.tWfs,
      { path := "cakeml/compiler/inference/unifyScript.sml", name := "t_wfs_def",
        fmapAsFiniteSupportParameters := #["subst"] }),
    (`Flapjack.Compiler.Inference.Unify.walkstarEqn,
      { path := "cakeml/compiler/inference/unifyScript.sml", name := "t_walkstar_eqn",
        fmapAsFiniteSupportParameters := #["s"] }),
    (`Flapjack.Compiler.Inference.Unify.tWalkstarEqn1,
      { path := "cakeml/compiler/inference/unifyScript.sml", name := "t_walkstar_eqn1",
        fmapAsFiniteSupportParameters := #["s"] }),
    (`Flapjack.Compiler.Inference.Unify.tWalkEqn,
      { path := "cakeml/compiler/inference/unifyScript.sml", name := "t_walk_eqn",
        fmapAsFiniteSupportParameters := #["s1", "s2", "s3"] }),
    (`Flapjack.Compiler.Inference.Unify.tVwalkEq,
      { path := "cakeml/compiler/inference/unifyScript.sml", name := "t_vwalk_eqn",
        fmapAsFiniteSupportParameters := #["subst"] })]
  for (name, ref) in refs do
    unless HolRef.get? env name == some ref do
      problems := problems.push s!"{name} must retain its reviewed HOL reference"
  let witness := `Flapjack.Compiler.Inference.InferProps.TypeSubstWalkstar.holFmapAsFiniteSupportNestedWalkstarWitness
  for name in #[target, witness] do
    if owner name != `Flapjack.Compiler.Inference.InferProps.TypeSubstWalkstar then
      problems := problems.push s!"{name} has the wrong defining module"
    match env.find? name with
    | some (.thmInfo info) =>
      unless info.levelParams.isEmpty do problems := problems.push s!"{name} must be monomorphic"
      if name == target then problems := problems ++ (← typeSubstWalkstarStatementProblems info.type)
      else problems := problems ++ (← typeSubstWalkstarWitnessProblems info.type)
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          problems := problems.push s!"{name} depends on unexpected axiom {axiomName}"
    | _ => problems := problems.push s!"{name} must be a theorem"
  return problems

end Flapjack
