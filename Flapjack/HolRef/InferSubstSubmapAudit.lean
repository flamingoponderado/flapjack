module

public meta import Lean
public meta import Lean.Util.CollectAxioms
public meta import Flapjack.HolRef
public meta import Flapjack.HolRef.GeneraliseLengthAudit

public meta section

/-! Elaborated audit for the independently quantified map binders of the
inference substitution submap theorem. This audit alone does not establish
the HOL-to-Lean correspondence. -/
namespace Flapjack
open Lean Meta

/-- Build the HOL-shaped premise independently of the theorem under audit. -/
private def inferSubstSubmapExpectedPremise (args : Array Expr) (listCase : Bool) : MetaM Expr := do
  let input := args[0]!
  let s1 := args[1]!
  let s2 := args[2]!
  let minimum := args[3]!
  let nat := mkConst ``Nat
  let sub ← mkAppM `Flapjack.HolFiniteMapExact.submap #[s1, s2]
  let domain1 ← mkAppM `Flapjack.HolFiniteMapExact.domain #[s1]
  let domain2 ← mkAppM `Flapjack.HolFiniteMapExact.domain #[s2]
  let vars := mkConst `Flapjack.Compiler.Inference.Unify.tVars
  let covered ← withLocalDeclD `v nat fun v => do
    let above ← mkAppM ``LE.le #[minimum, v]
    let occurs ← if listCase then
      let setType ← mkArrow nat (mkSort Level.zero)
      withLocalDeclD `s setType fun s => do
        let mapped ← mkAppM ``List.map #[vars, input]
        let member ← mkAppM ``List.Mem #[s, mapped]
        let pred := mkApp2 (mkConst ``And) (mkApp s v)
          (mkApp2 (mkConst ``And) member above)
        let body ← mkLambdaFVars #[s] pred
        mkAppM ``Exists #[body]
    else
      pure <| mkApp2 (mkConst ``And) (mkApp (mkApp vars input) v) above
    mkForallFVars #[v] (← mkArrow occurs (mkApp domain1 v))
  let newBound ← withLocalDeclD `v nat fun v => do
    let above ← mkAppM ``LE.le #[minimum, v]
    let absent := mkApp (mkConst ``Not) (mkApp domain1 v)
    let fresh := mkApp2 (mkConst ``And) (mkApp domain2 v) absent
    mkForallFVars #[v] (← mkArrow fresh above)
  return mkApp2 (mkConst ``And) sub (mkApp2 (mkConst ``And) covered newBound)

/-- Check one conjunct's explicit binder carriers and direct conclusion. -/
private def inferSubstSubmapConjunctProblems (type : Expr) (listCase : Bool) : MetaM (Array String) := do
  forallTelescope type fun args conclusion => do
    unless args.size == 5 do return #[s!"expected four variables and one premise, got {args.size}"]
    let inferT := mkConst `Flapjack.Compiler.Inference.InferT
    let map := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) (mkConst ``Nat) (mkConst ``Nat)
    let input := if listCase then mkApp (mkConst ``List [Level.zero]) inferT else inferT
    let expected := #[input, map, map, mkConst ``Nat]
    for i in [0:4] do
      let binder ← args[i]!.fvarId!.getDecl
      unless binder.binderInfo == .default do return #[s!"binder {i + 1} must be explicit"]
      unless ← isDefEq binder.type expected[i]! do return #[s!"binder {i + 1} has the wrong carrier"]
      if i == 1 && binder.userName != `s1 then return #["second binder must be s1"]
      if i == 2 && binder.userName != `s2 then return #["third binder must be s2"]
    let premise ← args[4]!.fvarId!.getDecl
    unless premise.binderInfo == .default && premise.type.getAppFn.isConstOf ``And do
      return #["the explicit premise must be a conjunction"]
    let expectedPremise ← inferSubstSubmapExpectedPremise args listCase
    unless ← withTransparency .default (isDefEq premise.type expectedPremise) do
      return #["the premise must preserve submap, coverage, and new-domain bound"]
    let equality := conclusion.consumeMData
    let eqArgs := equality.getAppArgs
    unless equality.getAppFn.isConstOf ``Eq && eqArgs.size == 3 do
      return #["conclusion must be a direct equality"]
    let producer := `Flapjack.Compiler.Inference.Infer.Substitution.inferSubst
    for (side, mapArg) in #[(eqArgs[1]!, args[1]!), (eqArgs[2]!, args[2]!)] do
      let expr := side.consumeMData
      if listCase then
        let parts := expr.getAppArgs
        unless expr.getAppFn.isConstOf ``List.map && parts.size == 4 && parts[3]! == args[0]! do
          return #["list conclusion must directly map over the input"]
        let fn := parts[2]!.consumeMData
        unless fn.getAppFn.isConstOf producer && fn.getAppArgs == #[mapArg] do
          return #["list conclusion must directly apply substitution to the matching map"]
      else
        unless expr.getAppFn.isConstOf producer && expr.getAppArgs == #[mapArg, args[0]!] do
          return #["type conclusion must directly apply substitution to the matching map and input"]
    return #[]

/-- Require two independent HOL-shaped quantifier groups, their complete
    premises, and direct conclusions. Imported-definition audits are separate. -/
def inferSubstSubmapBinderProblems (type : Expr) : MetaM (Array String) := do
  let expression := type.consumeMData
  let conjuncts := expression.getAppArgs
  unless expression.getAppFn.isConstOf ``And && conjuncts.size == 2 do
    return #["the theorem must be a conjunction of two independently quantified cases"]
  let first ← inferSubstSubmapConjunctProblems conjuncts[0]! false
  let second ← inferSubstSubmapConjunctProblems conjuncts[1]! true
  return first ++ second

/-- Check the theorem, its codec witness, and the defining owners of its
    carriers and operations. Source and manifest checks remain separate. -/
def inferSubstSubmapBundleProblems (target : Name) : MetaM (Array String) := do
  let expected := `Flapjack.Compiler.Inference.InferProps.Substitution.inferSubstSubmap
  unless target == expected do return #["submap qualifier requires the reviewed theorem"]
  let env ← getEnv
  let owner (name : Name) :=
    match env.getModuleIdxFor? name with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  let dependencies := #[
    (`Flapjack.HolFiniteMapExact, `Flapjack.FiniteMap.Exact),
    (`Flapjack.Compiler.Inference.InferT, `Flapjack.Compiler.Inference.InferT),
    (`Flapjack.Compiler.Inference.Infer.Substitution.inferSubst,
      `Flapjack.Compiler.Inference.Infer.Substitution),
    (`Flapjack.Compiler.Inference.Unify.tVars, `Flapjack.Compiler.Inference.Unify.Substitution),
    (`Flapjack.FiniteMapBroad, `Flapjack.FiniteMap.BroadCodec),
    (`Flapjack.FiniteMapBroad.toBroad, `Flapjack.FiniteMap.BroadCodec),
    (`Flapjack.FiniteMapBroad.ofBroad, `Flapjack.FiniteMap.BroadCodec),
    (`Flapjack.HolFiniteMapExact.domain, `Flapjack.FiniteMap.DomainExact),
    (`Flapjack.HolFiniteMapExact.submap, `Flapjack.FiniteMap.SubmapExact)]
  let mut problems := #[]
  for (name, moduleName) in dependencies do
    if (env.find? name).isNone || owner name != moduleName then
      problems := problems.push s!"{name} is missing or has the wrong defining module"
  let producerRef : HolRef := {
    path := "cakeml/compiler/inference/inferScript.sml", name := "infer_subst_def",
    fmapAsFiniteSupportParameters := #["subst"] }
  unless HolRef.get? env `Flapjack.Compiler.Inference.Infer.Substitution.inferSubst == some producerRef do
    problems := problems.push "submap theorem requires the reviewed substitution producer reference"
  let varsRef : HolRef := {
    path := "cakeml/compiler/inference/unifyScript.sml", name := "t_vars_def" }
  unless HolRef.get? env `Flapjack.Compiler.Inference.Unify.tVars == some varsRef do
    problems := problems.push "submap theorem requires the reviewed variable-set reference"
  let typeRef : HolRef := {
    path := "cakeml/compiler/inference/infer_tScript.sml", name := "infer_t" }
  unless HolRef.get? env `Flapjack.Compiler.Inference.InferT == some typeRef do
    problems := problems.push "submap theorem requires the reviewed inference-type reference"
  if owner target != `Flapjack.Compiler.Inference.InferProps.Substitution then
    problems := problems.push "submap theorem has the wrong defining module"
  match env.find? target with
  | some (.thmInfo info) =>
    unless info.levelParams.isEmpty do problems := problems.push "submap theorem must be monomorphic"
    problems := problems ++ (← inferSubstSubmapBinderProblems info.type)
    let axioms ← Lean.collectAxioms target
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        problems := problems.push s!"submap theorem depends on unexpected axiom {axiomName}"
  | _ => problems := problems.push "submap declaration must be a theorem"
  let witness := `Flapjack.Compiler.Inference.InferProps.Substitution.holFmapAsFiniteSupportNestedSubmapWitness
  if owner witness != `Flapjack.Compiler.Inference.InferProps.Substitution then
    problems := problems.push "submap codec witness has the wrong defining module"
  match env.find? witness with
  | some (.thmInfo info) =>
    unless info.levelParams.isEmpty do problems := problems.push "submap codec witness must be monomorphic"
    problems := problems ++ (← generaliseLengthWitnessProblems info.type `map)
    let axioms ← Lean.collectAxioms witness
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        problems := problems.push s!"submap codec witness depends on unexpected axiom {axiomName}"
  | _ => problems := problems.push "submap codec witness must be a theorem"
  return problems

end Flapjack
