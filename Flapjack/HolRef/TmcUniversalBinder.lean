module

public meta import Lean

public meta section

/-! Preliminary elaborated check for the body-bound map in the TMC
induction hypothesis. This does not enable a HOL qualifier: the complete
predicate body, existential scopes, codec witnesses and source correspondence
still require separate checks. -/

namespace Flapjack
open Lean Meta

/-- Check the elaborated TMC induction predicate's outer and universal
telescopes, their carriers and the clock guard. The caller must independently
validate the whole simulation premise and conclusion. -/
def tmcHypothesisUniversalBinderProblems (type value : Expr) : MetaM (Array String) := do
  unless ← isDefEq (← inferType value) type do
    return #["predicate body has the wrong declaration type"]
  lambdaTelescope value fun parameters body => do
    unless parameters.size == 5 do
      return #["predicate must have five outer binders"]
    let nat := mkConst `Nat
    let c := parameters[0]!
    let ffi := parameters[1]!
    let pair := mkApp2 (mkConst `Prod [Level.zero, Level.zero]) nat c
    let state (cfg : Expr) := mkApp2 (mkConst `Flapjack.Compiler.Backend.BviSem.BviState) cfg ffi
    let values := mkApp (mkConst `List [Level.zero]) (mkConst `Flapjack.Compiler.Backend.BvlSem.Value)
    let expressions := mkApp (mkConst `List [Level.zero]) (mkConst `Flapjack.Compiler.Backend.Bvi.Exp)
    let outerNames := #[`C, `F, `xs, `source, `clock]
    let outerTypes := #[mkSort (Level.succ Level.zero), mkSort (Level.succ Level.zero),
      expressions, state pair, nat]
    for i in [:outerNames.size] do
      let binder ← parameters[i]!.fvarId!.getDecl
      let visibility := if i < 2 then BinderInfo.implicit else BinderInfo.default
      unless binder.userName == outerNames[i]! && binder.binderInfo == visibility &&
          binder.type == outerTypes[i]! do
        return #[s!"outer binder {i} has the wrong name, visibility or carrier"]
    forallTelescope body fun binders conclusion => do
      unless binders.size == 10 do
        return #["predicate body has the wrong universal telescope"]
      let map := binders[5]!
      let mapDecl ← map.fvarId!.getDecl
      let expectedMap := mkApp2 (mkConst `Flapjack.HolFiniteMapExact)
        (mkConst `Nat) (mkConst `Nat)
      unless mapDecl.userName == `f && mapDecl.binderInfo == .default && mapDecl.type == expectedMap do
        return #["universal f must be explicit and have the canonical Nat-to-Nat map carrier"]
      let expectedNames := #[`env1, `result, `final, `opt, `f, `target, `env2, `loc]
      let expectedTypes := #[values, mkConst `Flapjack.Compiler.Backend.BviSem.BviResult,
        state pair, mkConst `Bool, expectedMap, state c, values, nat]
      for i in [:expectedNames.size] do
        let binder ← binders[i + 1]!.fvarId!.getDecl
        unless binder.userName == expectedNames[i]! && binder.binderInfo == .default &&
            binder.type == expectedTypes[i]! do
          return #[s!"universal binder {i + 1} has the wrong name, visibility or carrier"]
      let guard ← binders[0]!.fvarId!.getDecl
      let premise ← binders[9]!.fvarId!.getDecl
      let sourceClock := mkAppN (mkConst `Flapjack.Compiler.Backend.BviSem.BviState.clock)
        #[pair, ffi, parameters[3]!]
      let expectedGuard := mkAppN (mkConst `LT.lt [Level.zero])
        #[nat, mkConst `instLTNat, sourceClock, parameters[4]!]
      unless guard.binderInfo == .default && premise.binderInfo == .default &&
          guard.type == expectedGuard && (← isProp premise.type) do
        return #["clock guard or simulation premise has the wrong shape"]
      unless (premise.type.find? (· == map)).isSome && (conclusion.find? (· == map)).isSome do
        return #["universal f must occur in both the premise and conclusion"]
      unless conclusion.isAppOfArity ``Exists 2 do
        return #["predicate must have an existential conclusion"]
      return #[]

end Flapjack
