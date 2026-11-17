module

public meta import Lean
public meta import Lean.Util.CollectAxioms
public meta import Flapjack.HolRef

public meta section

/-! Prospective elaborated statement audit for guarded unifier equivalence.
    It checks the Lean shape only; source correspondence needs separate review. -/
namespace Flapjack
open Lean Meta

/-- Check the direct binders, original well-formedness guard, and complete
    chosen-unifier/recursion-model equality. This does not establish that the
    two model operations correspond to HOL or validate a representation tag. -/
def unifyEqTunifyStatementProblems (type : Expr) : MetaM (Array String) := do
  forallTelescope type fun args conclusion => do
    unless args.size == 5 do
      return #[s!"expected a type, map, two terms and one premise; got {args.size} binders"]
    let typeDecl ← args[0]!.fvarId!.getDecl
    unless typeDecl.binderInfo == .implicit && (← isDefEq typeDecl.type (mkSort (Level.succ Level.zero))) do
      return #["the first binder must be an implicit Type parameter"]
    let termTy ← mkAppM `Flapjack.HOL.Unification.Term #[args[0]!]
    let mapTy ← mkAppM `Flapjack.HolFiniteMapExact #[mkConst ``Nat, termTy]
    for i in [1:4] do
      let binder ← args[i]!.fvarId!.getDecl
      let expected := if i == 1 then mapTy else termTy
      unless binder.binderInfo == .default && (← isDefEq binder.type expected) do
        return #[s!"binder {i + 1} has the wrong explicit carrier"]
      if i == 1 && binder.userName != `s then
        return #["the finite-map binder must be named s"]
    let premise ← args[4]!.fvarId!.getDecl
    let expectedGuard ← mkAppM `Flapjack.HOL.Unification.wfs #[args[1]!]
    unless premise.binderInfo == .default && premise.type.consumeMData == expectedGuard do
      return #["the sole premise must directly assert wfs of the original map"]
    let chosen ← mkAppM `Flapjack.HOL.Unification.specifiedUnify #[args[1]!, args[2]!, args[3]!]
    let recursive ← mkAppM `Flapjack.HOL.Unification.tunifyAux #[args[1]!, args[2]!, args[3]!]
    let expected ← mkEq chosen recursive
    unless conclusion.consumeMData == expected do
      return #["conclusion must be the exact selected/recursive equality on the original arguments"]
    return #[]

/-- Validate the unconditional codec for the exact input substitution. -/
def unifyEqTunifyParamWitnessProblems (type : Expr) : MetaM (Array String) := do
  forallTelescope type fun args conclusion => do
    unless args.size == 3 do return #["parameter witness requires a type, map and key"]
    let ty ← args[0]!.fvarId!.getDecl
    let map ← args[1]!.fvarId!.getDecl
    let key ← args[2]!.fvarId!.getDecl
    let termTy ← mkAppM `Flapjack.HOL.Unification.Term #[args[0]!]
    let mapTy ← mkAppM `Flapjack.HolFiniteMapExact #[mkConst ``Nat, termTy]
    unless ty.binderInfo == .implicit && map.binderInfo == .default && map.userName == `s &&
        key.binderInfo == .default && (← isDefEq map.type mapTy) &&
        (← isDefEq key.type (mkConst ``Nat)) do
      return #["parameter witness binders have the wrong shape"]
    let broad ← mkAppM `Flapjack.FiniteMapBroad.toBroad #[args[1]!]
    let exact ← mkAppM `Flapjack.FiniteMapBroad.ofBroad #[broad]
    let llookup ← mkAppM `Flapjack.HolFiniteMapExact.lookup #[exact, args[2]!]
    let rlookup ← mkAppM `Flapjack.HolFiniteMapExact.lookup #[args[1]!, args[2]!]
    let lookupEq ← mkEq llookup rlookup
    let lsupport ← mkAppM `Flapjack.HolFiniteMapExact.finiteSupport #[exact]
    let rsupport ← mkAppM `Flapjack.HolFiniteMapExact.finiteSupport #[args[1]!]
    let supportEq ← mkEq lsupport rsupport
    let mapEq ← mkEq exact args[1]!
    let expected := mkApp2 (mkConst ``And) lookupEq (mkApp2 (mkConst ``And) supportEq mapEq)
    unless conclusion == expected do return #["parameter witness must preserve lookup, support and map"]
    return #[]

/-- Validate both option-map observations and their equality reflection,
    without a well-formedness or successful-result premise. -/
def unifyEqTunifyOptionWitnessProblems (type : Expr) : MetaM (Array String) := do
  forallTelescope type fun args conclusion => do
    unless args.size == 4 do return #["option witness requires a type, map and two terms"]
    let ty ← args[0]!.fvarId!.getDecl
    let termTy ← mkAppM `Flapjack.HOL.Unification.Term #[args[0]!]
    let mapTy ← mkAppM `Flapjack.HolFiniteMapExact #[mkConst ``Nat, termTy]
    unless ty.binderInfo == .implicit do return #["option witness type must be implicit"]
    for i in [1:4] do
      let binder ← args[i]!.fvarId!.getDecl
      let expected := if i == 1 then mapTy else termTy
      unless binder.binderInfo == .default && (← isDefEq binder.type expected) do
        return #[s!"option witness binder {i + 1} has the wrong carrier"]
      if i == 1 && binder.userName != `s then return #["option witness map must be named s"]
    let chosen ← mkAppM `Flapjack.HOL.Unification.specifiedUnify #[args[1]!, args[2]!, args[3]!]
    let recursive ← mkAppM `Flapjack.HOL.Unification.tunifyAux #[args[1]!, args[2]!, args[3]!]
    let toBroad ← mkAppOptM `Flapjack.FiniteMapBroad.toBroad #[some (mkConst ``Nat), some termTy]
    let ofBroad ← mkAppOptM `Flapjack.FiniteMapBroad.ofBroad #[some (mkConst ``Nat), some termTy]
    let chosenBroad ← mkAppM ``Option.map #[toBroad, chosen]
    let recursiveBroad ← mkAppM ``Option.map #[toBroad, recursive]
    let chosenRoundtrip ← mkAppM ``Option.map #[ofBroad, chosenBroad]
    let recursiveRoundtrip ← mkAppM ``Option.map #[ofBroad, recursiveBroad]
    let chosenEq ← mkEq chosenRoundtrip chosen
    let recursiveEq ← mkEq recursiveRoundtrip recursive
    let broadEq ← mkEq chosenBroad recursiveBroad
    let exactEq ← mkEq chosen recursive
    let reflected := mkApp2 (mkConst ``Iff) broadEq exactEq
    let expected := mkApp2 (mkConst ``And) chosenEq (mkApp2 (mkConst ``And) recursiveEq reflected)
    unless conclusion == expected do return #["option witness must round-trip both results and reflect equality"]
    return #[]

/-- Check that the guarded equation, induction and intermediate invariant are
    present in a proof dependency set. Presence does not establish their
    source correspondence or prevent additional dependencies. -/
def unifyEqTunifyProofDependencyProblems (names : Array Name) : Array String := Id.run do
  let required := #[
    `Flapjack.HOL.Unification.specifiedUnifyEquation,
    `Flapjack.HOL.Unification.tunifyAuxEquation,
    `Flapjack.HOL.Unification.tunifyAuxUP,
    `Flapjack.HOL.Unification.tunifyAuxInd]
  let mut problems := #[]
  for name in required do
    unless names.contains name do
      problems := problems.push s!"unifier proof does not depend on {name}"
  return problems

/-- Collect body dependencies in the unification modules, including private
    helpers and opaque theorem bodies. Dependencies are bounded to that
    namespace; this is not a complete dependency inventory. -/
private def unifyEqTunifyBodyDependencies (env : Environment) (target : Name) : Array Name := Id.run do
  let mut visited : Std.HashSet Name := {}
  let mut pending := #[target]
  let mut result := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless visited.contains name do
      visited := visited.insert name
      result := result.push name
      if let some info := env.find? name then
        if let some body := info.value? (allowOpaque := true) then
          for dep in body.getUsedConstants do
            let moduleName := match env.getModuleIdxFor? dep with
              | some idx => env.header.moduleNames[idx.toNat]!
              | none => env.mainModule
            if moduleName.toString.startsWith "Flapjack.HOL.Unification." then
              pending := pending.push dep
  return result

/-- Check the reviewed statement's owner, its guarded model dependencies,
    selected source references and axiom closure. This remains a prospective
    audit and does not enable a HOL attribute. -/
def unifyEqTunifyBundleProblems (target : Name) : MetaM (Array String) := do
  let expected := `Flapjack.HOL.Unification.specifiedUnifyEqAux
  unless target == expected do return #["unifier audit requires the selected equivalence theorem"]
  let env ← getEnv
  let owner (name : Name) :=
    match env.getModuleIdxFor? name with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  let dependencies := #[
    (`Flapjack.HolFiniteMapExact, `Flapjack.FiniteMap.Exact),
    (`Flapjack.HOL.Unification.Term, `Flapjack.HOL.Unification.Term),
    (`Flapjack.HOL.Unification.wfs, `Flapjack.HOL.Unification.Subst),
    (`Flapjack.HOL.Unification.vwalkEq, `Flapjack.HOL.Unification.Walk),
    (`Flapjack.HOL.Unification.Oc, `Flapjack.HOL.Unification.Walkstar.Occurs),
    (`Flapjack.HOL.Unification.uRWellFounded, `Flapjack.HOL.Unification.UnifDef.WellFounded),
    (`Flapjack.HOL.Unification.tunifyAux, `Flapjack.HOL.Unification.UnifDef.Tunify),
    (`Flapjack.HOL.Unification.tunifyAuxEquation, `Flapjack.HOL.Unification.UnifDef.Tunify),
    (`Flapjack.HOL.Unification.tunifyAuxUP, `Flapjack.HOL.Unification.UnifDef.Tunify),
    (`Flapjack.HOL.Unification.tunifyAuxInd, `Flapjack.HOL.Unification.UnifDef.Tunify),
    (`Flapjack.HOL.Unification.UnifySpec, `Flapjack.HOL.Unification.UnifDef.Choice),
    (`Flapjack.HOL.Unification.specifiedUnify, `Flapjack.HOL.Unification.UnifDef.Choice),
    (`Flapjack.HOL.Unification.specifiedUnifyEquation, `Flapjack.HOL.Unification.UnifDef.Choice)]
  let mut problems := #[]
  for (name, moduleName) in dependencies do
    if (env.find? name).isNone || owner name != moduleName then
      problems := problems.push s!"{name} is missing or has the wrong defining module"
  let refs : Array (Name × HolRef) := #[
    (`Flapjack.HOL.Unification.Term,
      { path := "HOL/examples/algorithms/unification/triangular/first-order/termScript.sml", name := "term" }),
    (`Flapjack.HOL.Unification.wfs,
      { path := "HOL/examples/algorithms/unification/triangular/first-order/substScript.sml", name := "wfs_def",
        fmapAsFiniteSupportParameters := #["subst"] }),
    (`Flapjack.HOL.Unification.vwalkEq,
      { path := "HOL/examples/algorithms/unification/triangular/first-order/walkScript.sml", name := "vwalk_def",
        fmapAsFiniteSupportParameters := #["subst"] }),
    (`Flapjack.HOL.Unification.uRWellFounded,
      { path := "HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml", name := "WF_uR",
        fmapAsFiniteSupportTuple := #["component_1"] })]
  for (name, ref) in refs do
    unless HolRef.get? env name == some ref do
      problems := problems.push s!"{name} must retain its reviewed HOL reference"
  if owner target != `Flapjack.HOL.Unification.UnifDef.Choice then
    problems := problems.push "unifier theorem has the wrong defining module"
  match env.find? target with
  | some (.thmInfo info) =>
    unless info.levelParams.isEmpty do problems := problems.push "unifier theorem must use HOL's Type carrier"
    problems := problems ++ (← unifyEqTunifyStatementProblems info.type)
    problems := problems ++ unifyEqTunifyProofDependencyProblems (unifyEqTunifyBodyDependencies env target)
    let axioms ← Lean.collectAxioms target
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        problems := problems.push s!"unifier theorem depends on unexpected axiom {axiomName}"
  | _ => problems := problems.push "unifier target must be a theorem"
  let paramWitness := `Flapjack.HOL.Unification.holFmapAsFiniteSupportParamWitness_specifiedUnifyEqAux_s
  let optionWitness := `Flapjack.HOL.Unification.holFmapAsFiniteSupportGuardedOptionObservationsWitness_specifiedUnifyEqAux
  for witness in #[paramWitness, optionWitness] do
    if owner witness != `Flapjack.HOL.Unification.UnifDef.Choice then
      problems := problems.push s!"{witness} has the wrong defining module"
    match env.find? witness with
    | some (.thmInfo info) =>
      unless info.levelParams.isEmpty do problems := problems.push s!"{witness} must use HOL's Type carrier"
      if witness == paramWitness then
        problems := problems ++ (← unifyEqTunifyParamWitnessProblems info.type)
      else
        problems := problems ++ (← unifyEqTunifyOptionWitnessProblems info.type)
      let axioms ← Lean.collectAxioms witness
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          problems := problems.push s!"{witness} depends on unexpected axiom {axiomName}"
    | _ => problems := problems.push s!"{witness} must be a theorem"
  return problems

end Flapjack
