module

public meta import Lean

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

end Flapjack
