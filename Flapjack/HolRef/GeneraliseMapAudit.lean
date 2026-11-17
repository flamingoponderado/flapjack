module

public meta import Lean

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

end Flapjack
