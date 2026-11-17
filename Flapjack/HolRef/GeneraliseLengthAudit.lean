module

public meta import Lean
public meta import Lean.Util.CollectAxioms
public meta import Flapjack.HolRef.GeneraliseMapAudit

public meta section

/-! Elaborated statement audit for the inference generalization length theorem.
This check alone does not enable a HOL qualifier or establish source fidelity. -/
namespace Flapjack
open Lean Meta

/-- Check the complete binder list, tuple premise and length conclusion. -/
def generaliseLengthStatementProblems (type : Expr) : MetaM (Array String) := do
  forallTelescope type fun args result => do
    unless args.size == 8 do return #[s!"expected eight binders, got {args.size}"]
    let map := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) (mkConst ``Nat) (mkConst ``Nat)
    let inferT := mkConst `Flapjack.Compiler.Inference.InferT
    let types := mkApp (mkConst ``List [Level.zero]) inferT
    let carriers := #[mkConst ``Nat, mkConst ``Nat, map, types, mkConst ``Nat, map, types]
    for i in [0:7] do
      let binder ← args[i]!.fvarId!.getDecl
      unless binder.binderInfo == .default do return #[s!"binder {i + 1} must be explicit"]
      unless ← isDefEq binder.type carriers[i]! do return #[s!"binder {i + 1} has the wrong carrier"]
      if i == 2 && binder.userName != `subst then return #["third binder must be named subst"]
      if i == 5 && binder.userName != `out then return #["sixth binder must be named out"]
    let premise ← args[7]!.fvarId!.getDecl
    unless premise.binderInfo == .default do return #["premise must be explicit"]
    let premiseExpr := premise.type.consumeMData
    let eqArgs := premiseExpr.getAppArgs
    unless premiseExpr.getAppFn.isConstOf ``Eq && eqArgs.size == 3 do
      return #["premise must be a direct equality"]
    let lhs := eqArgs[1]!.consumeMData
    unless lhs.getAppFn.isConstOf `Flapjack.Compiler.Inference.Infer.Generalise.generaliseListMap &&
        lhs.getAppArgs == #[args[0]!, args[1]!, args[2]!, args[3]!] do
      return #["premise must directly apply the reviewed generalization producer"]
    let actual ← mkAppM `Flapjack.Compiler.Inference.Infer.Generalise.generaliseListMap
      #[args[0]!, args[1]!, args[2]!, args[3]!]
    let tail ← mkAppM ``Prod.mk #[args[5]!, args[6]!]
    let triple ← mkAppM ``Prod.mk #[args[4]!, tail]
    let expectedPremise ← mkEq actual triple
    unless ← withTransparency .reducible (isDefEq premise.type expectedPremise) do
      return #["premise must equate the generalization result to (count, out, result)"]
    let resultLength ← mkAppM ``List.length #[args[6]!]
    let inputLength ← mkAppM ``List.length #[args[3]!]
    let expectedConclusion ← mkEq resultLength inputLength
    unless ← withTransparency .reducible (isDefEq result expectedConclusion) do
      return #["conclusion must state result length equals input length"]
    return #[]

/-- Audit one unconditional codec witness without unfolding its roundtrip. -/
def generaliseLengthWitnessProblems (type : Expr) (binderName : Name) : MetaM (Array String) := do
  forallTelescope type fun args result => do
    unless args.size == 2 do return #[s!"expected two witness binders, got {args.size}"]
    let mapType := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) (mkConst ``Nat) (mkConst ``Nat)
    let mapBinder ← args[0]!.fvarId!.getDecl
    let keyBinder ← args[1]!.fvarId!.getDecl
    unless mapBinder.binderInfo == .default && keyBinder.binderInfo == .default &&
        mapBinder.userName == binderName do return #["witness binders must be explicit and name the map"]
    unless (← isDefEq mapBinder.type mapType) && (← isDefEq keyBinder.type (mkConst ``Nat)) do
      return #["witness binders have the wrong carriers"]
    let original := args[0]!
    let key := args[1]!
    let broad ← mkAppM `Flapjack.FiniteMapBroad.toBroad #[original]
    let roundtrip ← mkAppM `Flapjack.FiniteMapBroad.ofBroad #[broad]
    let lookupRoundtrip ← mkAppM `Flapjack.HolFiniteMapExact.lookup #[roundtrip, key]
    let lookupOriginal ← mkAppM `Flapjack.HolFiniteMapExact.lookup #[original, key]
    let lookupEq ← mkEq lookupRoundtrip lookupOriginal
    let supportRoundtrip ← mkAppM `Flapjack.HolFiniteMapExact.finiteSupport #[roundtrip]
    let supportOriginal ← mkAppM `Flapjack.HolFiniteMapExact.finiteSupport #[original]
    let supportEq ← mkEq supportRoundtrip supportOriginal
    let mapEq ← mkEq roundtrip original
    let expected := mkApp2 (mkConst ``And) lookupEq (mkApp2 (mkConst ``And) supportEq mapEq)
    unless result == expected do
      return #["witness must state the exact lookup, support and map codec roundtrip"]
    return #[]

/-- Check the exact theorem, both local witnesses and their producer bundle.
    HOL metadata and source review are separate requirements. -/
def generaliseLengthBundleProblems (target : Name) : MetaM (Array String) := do
  let expected := `Flapjack.Compiler.Inference.InferProps.Generalise.generaliseListLength
  unless target == expected do return #["length qualifier requires the reviewed theorem"]
  let owner := `Flapjack.Compiler.Inference.InferProps.Generalise
  let substWitness := `Flapjack.Compiler.Inference.InferProps.Generalise.holFmapAsFiniteSupportParamWitness_generaliseListLength_subst
  let outWitness := `Flapjack.Compiler.Inference.InferProps.Generalise.holFmapAsFiniteSupportParamWitness_generaliseListLength_out
  let producer := `Flapjack.Compiler.Inference.Infer.Generalise.generaliseListMap
  let env ← getEnv
  let definingModule (name : Name) :=
    match env.getModuleIdxFor? name with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  let mut problems ← generaliseMapBundleProblems producer
  for dependency in #[`Flapjack.FiniteMapBroad, `Flapjack.FiniteMapBroad.toBroad,
      `Flapjack.FiniteMapBroad.ofBroad] do
    if (env.find? dependency).isNone || definingModule dependency != `Flapjack.FiniteMap.BroadCodec then
      problems := problems.push s!"{dependency} is missing or has the wrong defining module"
  for (name, binder) in #[(target, `none), (substWitness, `subst), (outWitness, `out)] do
    if definingModule name != owner then
      problems := problems.push s!"{name} has the wrong defining module"
    match env.find? name with
    | some (.thmInfo info) =>
      unless info.levelParams.isEmpty do
        problems := problems.push s!"{name} must be monomorphic"
      if name == target then
        problems := problems ++ (← generaliseLengthStatementProblems info.type)
      else
        problems := problems ++ (← generaliseLengthWitnessProblems info.type binder)
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          problems := problems.push s!"{name} depends on unexpected axiom {axiomName}"
    | _ => problems := problems.push s!"{name} must be a theorem"
  return problems

end Flapjack
