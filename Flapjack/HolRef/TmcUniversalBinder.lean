module

public meta import Lean

public meta section

/-! Preliminary elaborated check for the body-bound map in the TMC
induction hypothesis. This does not enable a HOL qualifier: the complete
predicate body, existential scopes, codec witnesses and source correspondence
still require separate checks. -/

namespace Flapjack
open Lean Meta

/-- Check the outer telescope of the elaborated TMC induction predicate and
the position, visibility and carrier of its universally quantified map.
The caller must independently validate the whole premise and conclusion. -/
def tmcHypothesisUniversalBinderProblems (type value : Expr) : MetaM (Array String) := do
  unless ← isDefEq (← inferType value) type do
    return #["predicate body has the wrong declaration type"]
  lambdaTelescope value fun parameters body => do
    unless parameters.size == 5 do
      return #["predicate must have five outer binders"]
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
      for i in [:expectedNames.size] do
        let binder ← binders[i + 1]!.fvarId!.getDecl
        unless binder.userName == expectedNames[i]! && binder.binderInfo == .default do
          return #[s!"universal binder {i + 1} has the wrong name or visibility"]
      let guard ← binders[0]!.fvarId!.getDecl
      let premise ← binders[9]!.fvarId!.getDecl
      unless guard.binderInfo == .default && premise.binderInfo == .default &&
          (← isProp guard.type) && (← isProp premise.type) do
        return #["clock guard and simulation premise must be explicit propositions"]
      unless (premise.type.find? (· == map)).isSome && (conclusion.find? (· == map)).isSome do
        return #["universal f must occur in both the premise and conclusion"]
      unless conclusion.isAppOfArity ``Exists 2 do
        return #["predicate must have an existential conclusion"]
      return #[]

end Flapjack
