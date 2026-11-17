module

public meta import Lean
public meta import Lean.Util.CollectAxioms

public meta section

/-! Prospective elaborated checks for the inference generalizer's map input
and tuple output. These checks do not enable a qualifier; source comparison,
attribute/export integration, and checker tests remain separate. -/
namespace Flapjack
open Lean Meta

private def generaliseMapCarrier : Expr :=
  mkApp2 (mkConst `Flapjack.HolFiniteMapExact) (mkConst ``Nat) (mkConst ``Nat)

private def generaliseValueCarrier (isList : Bool) : Expr :=
  let typ := mkConst `Flapjack.Compiler.Inference.InferT
  if isList then mkApp (mkConst ``List [Level.zero]) typ else typ

private def generaliseResultCarrier (isList : Bool) : Expr :=
  let prod := mkConst ``Prod [Level.zero, Level.zero]
  mkApp2 prod (mkConst ``Nat) (mkApp2 prod generaliseMapCarrier (generaliseValueCarrier isList))

/-- Check all explicit operation binders and the complete direct result type. -/
def generaliseMapSignatureProblems (type : Expr) (isList : Bool) : MetaM (Array String) := do
  forallTelescope type fun args result => do
    unless args.size == 4 do return #[s!"expected four binders, got {args.size}"]
    let carriers := #[mkConst ``Nat, mkConst ``Nat, generaliseMapCarrier, generaliseValueCarrier isList]
    for i in [0:4] do
      let binder ← args[i]!.fvarId!.getDecl
      unless binder.binderInfo == .default do return #[s!"binder {i + 1} must be explicit"]
      if i == 2 && binder.userName != `subst then return #["third binder must be named subst"]
      unless ← isDefEq binder.type carriers[i]! do return #[s!"binder {i + 1} has the wrong carrier"]
    unless ← isDefEq result (generaliseResultCarrier isList) do
      return #["result must be Nat × canonical map × inference type or list"]
    return #[]

/-- Check the complete witness proposition for the input lookup codec and
returned-map projection, with no additional binders or assumptions. -/
def generaliseMapWitnessProblems (type : Expr) (isList : Bool) : MetaM (Array String) := do
  forallTelescope type fun args result => do
    unless args.size == 5 do return #[s!"expected five witness binders, got {args.size}"]
    let carriers := #[mkConst ``Nat, mkConst ``Nat, generaliseMapCarrier,
      generaliseValueCarrier isList, mkConst ``Nat]
    for i in [0:5] do
      let binder ← args[i]!.fvarId!.getDecl
      unless binder.binderInfo == .default do return #[s!"witness binder {i + 1} must be explicit"]
      if i == 2 && binder.userName != `subst then return #["third witness binder must be named subst"]
      unless ← isDefEq binder.type carriers[i]! do return #[s!"witness binder {i + 1} has the wrong carrier"]
    let min := args[0]!
    let next := args[1]!
    let input := args[2]!
    let value := args[3]!
    let key := args[4]!
    let tree ← mkAppM `Flapjack.HOL.Transfer.Fmsp.fm2sp #[input]
    let map ← mkAppM `Flapjack.HOL.Transfer.Fmsp.sp2fm #[tree]
    let roundtrip ← mkEq (← mkAppM `Flapjack.HolFiniteMapExact.lookup #[map, key])
      (← mkAppM `Flapjack.HolFiniteMapExact.lookup #[input, key])
    let modelName := if isList then
      `Flapjack.Compiler.Inference.Infer.Generalise.generaliseListMap else
      `Flapjack.Compiler.Inference.Infer.Generalise.generaliseMap
    let execName := if isList then `Flapjack.Compiler.Inference.Infer.generaliseList else
      `Flapjack.Compiler.Inference.Infer.generalise
    let model ← mkAppM modelName #[min, next, input, value]
    let exec ← mkAppM execName #[min, next, tree, value]
    let modelMap := mkProj ``Prod 0 (mkProj ``Prod 1 model)
    let execMap := mkProj ``Prod 0 (mkProj ``Prod 1 exec)
    let output ← mkEq (← mkAppM `Flapjack.HolFiniteMapExact.lookup #[modelMap, key])
      (← mkAppM `Flapjack.sptLookup #[key, execMap])
    let expected := mkApp2 (mkConst ``And) roundtrip output
    unless ← withTransparency .reducible (isDefEq result expected) do
      return #["witness must state the exact input codec and returned-map lookup correspondence"]
    return #[]

/-- Validate one exact operation and its same-module witness. This prospective
    audit does not check HOL-reference metadata or source correspondence. -/
def generaliseMapBundleProblems (target : Name) : MetaM (Array String) := do
  let single := `Flapjack.Compiler.Inference.Infer.Generalise.generaliseMap
  let list := `Flapjack.Compiler.Inference.Infer.Generalise.generaliseListMap
  unless target == single || target == list do
    return #[s!"{target} is not an eligible generalization operation"]
  let isList := target == list
  let witness := if isList then
    `Flapjack.Compiler.Inference.Infer.Generalise.holFmapAsFiniteSupportParameterTupleResultWitness_generaliseListMap
    else `Flapjack.Compiler.Inference.Infer.Generalise.holFmapAsFiniteSupportParameterTupleResultWitness_generaliseMap
  let expectedModule := `Flapjack.Compiler.Inference.Infer.Generalise
  let env ← getEnv
  let definingModule (name : Name) :=
    match env.getModuleIdxFor? name with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  let mut problems : Array String := #[]
  for name in #[target, witness] do
    unless definingModule name == expectedModule do
      problems := problems.push s!"{name} has the wrong defining module"
  let exec := if isList then `Flapjack.Compiler.Inference.Infer.generaliseList else
    `Flapjack.Compiler.Inference.Infer.generalise
  let dependencies : Array (Name × Name) := #[
    (`Flapjack.HolFiniteMapExact, `Flapjack.FiniteMap.Exact),
    (`Flapjack.HolFiniteMapExact.lookup, `Flapjack.FiniteMap.Exact),
    (`Flapjack.HolFiniteMapExact.updateEq, `Flapjack.FiniteMap.Exact),
    (`Flapjack.Compiler.Inference.InferT, `Flapjack.Compiler.Inference.InferT),
    (`Flapjack.Spt, `Flapjack.Misc.Sptree),
    (`Flapjack.HOL.Transfer.Fmsp.sp2fm, `Flapjack.HOL.Transfer.Fmsp),
    (`Flapjack.HOL.Transfer.Fmsp.fm2sp, `Flapjack.HOL.Transfer.Fmsp.Inverse),
    (`Flapjack.sptLookup, `Flapjack.Misc.Sptree),
    (exec, `Flapjack.Compiler.Inference.Infer)]
  for (name, owner) in dependencies do
    if (env.find? name).isNone || definingModule name != owner then
      problems := problems.push s!"{name} is missing or has the wrong defining module"
  let some targetInfo := env.find? target | return problems.push s!"{target} is missing"
  let some witnessInfo := env.find? witness | return problems.push s!"{witness} is missing"
  match targetInfo with
  | .defnInfo info =>
    unless info.safety == .safe && info.levelParams.isEmpty do
      problems := problems.push s!"{target} must be a safe monomorphic definition"
  | _ => problems := problems.push s!"{target} must be a definition"
  match witnessInfo with
  | .thmInfo info =>
    unless info.levelParams.isEmpty do
      problems := problems.push s!"{witness} must be a monomorphic theorem"
  | _ => problems := problems.push s!"{witness} must be a theorem"
  problems := problems ++ (← generaliseMapSignatureProblems targetInfo.type isList)
  problems := problems ++ (← generaliseMapWitnessProblems witnessInfo.type isList)
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[target, witness] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        problems := problems.push s!"{name} depends on unexpected axiom {axiomName}"
  return problems

end Flapjack
