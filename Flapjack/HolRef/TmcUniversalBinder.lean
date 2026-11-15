module

public meta import Lean

public meta section

/-! Preliminary elaborated check for the body-bound map in the TMC
induction hypothesis. This does not enable a HOL qualifier: the complete
predicate body, existential scopes, codec witnesses and source correspondence
still require separate checks. -/

namespace Flapjack
open Lean Meta

/-- Check the elaborated TMC induction predicate's telescopes, clock guard
and simulation premise. The caller must independently validate the entire
conclusion, map scopes, codec and declaration ownership. -/
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
      let mut clauses := #[]
      let mut remainder := premise.type
      for _ in [:5] do
        match remainder with
        | .app (.app (.const ``And []) first) rest =>
          clauses := clauses.push first
          remainder := rest
        | _ => return #["simulation premise must contain the six original conjuncts"]
      clauses := clauses.push remainder
      let env1 := binders[1]!
      let result := binders[2]!
      let final := binders[3]!
      let opt := binders[4]!
      let target := binders[6]!
      let env2 := binders[7]!
      let xs := parameters[2]!
      let source := parameters[3]!
      let resultType := mkConst `Flapjack.Compiler.Backend.BviSem.BviResult
      let evaluation := mkAppN (mkConst `Flapjack.Compiler.Backend.BviSem.evaluate)
        #[pair, ffi, xs, env1, source]
      let output := mkAppN (mkConst `Prod.mk [Level.zero, Level.zero])
        #[resultType, state pair, result, final]
      let expectedEvaluation := mkApp3 (mkConst ``Eq [Level.succ Level.zero])
        (mkApp2 (mkConst `Flapjack.Compiler.Backend.BviSem.EvalResult) pair ffi) evaluation output
      let expectedEnv := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.envRel) #[opt, map, env1, env2]
      let expectedStates := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.stateRel)
        #[c, ffi, map, source, target]
      unless clauses[0]! == expectedEvaluation && clauses[1]! == expectedEnv &&
          clauses[3]! == expectedStates do
        return #["simulation evaluation, environment or state relation changed"]
      let allSafe ← forallTelescope clauses[2]! fun args conclusion => do
        unless args.size == 2 do return false
        let expression ← args[0]!.fvarId!.getDecl
        let membership ← args[1]!.fvarId!.getDecl
        let exp := mkConst `Flapjack.Compiler.Backend.Bvi.Exp
        let expectedMember := mkAppN (mkConst `Membership.mem [Level.zero, Level.zero])
          #[exp, expressions, mkApp (mkConst `List.instMembership [Level.zero]) exp, xs, args[0]!]
        return expression.binderInfo == .default && expression.type == exp &&
          membership.binderInfo == .default && membership.type == expectedMember &&
          conclusion == mkApp (mkConst `Flapjack.Compiler.Backend.BviTmc.noMutcons) args[0]!
      unless allSafe do return #["no-mutcons premise changed"]
      let singleton ← forallTelescope clauses[4]! fun args conclusion => do
        unless args.size == 1 do return false
        let assumption ← args[0]!.fvarId!.getDecl
        let eqBool := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst `Bool) opt (mkConst `Bool.true)
        let length := mkApp2 (mkConst `List.length [Level.zero])
          (mkConst `Flapjack.Compiler.Backend.Bvi.Exp) xs
        let oneLiteral := Expr.lit (.natVal 1)
        let one := mkAppN (mkConst `OfNat.ofNat [Level.zero])
          #[nat, oneLiteral, mkApp (mkConst `instOfNatNat) oneLiteral]
        let lengthEq := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) nat length one
        return assumption.binderInfo == .default && assumption.type == eqBool && conclusion == lengthEq
      unless singleton do return #["optimized singleton premise changed"]
      let errorType := mkConst `Flapjack.Compiler.Backend.BviSem.ExnOrRet
      let abort := mkApp2 (mkConst `Flapjack.SemanticPrimitivesHOL.ErrorResult.abort)
        errorType (mkConst `Flapjack.SemanticPrimitivesHOL.Abort.typeError)
      let typeError := mkApp3 (mkConst `Flapjack.SemanticPrimitivesHOL.Result.err) values errorType abort
      let safe := mkApp3 (mkConst ``Ne [Level.succ Level.zero]) resultType result typeError
      unless clauses[5]! == safe do return #["source type-error premise changed"]
      unless (premise.type.find? (· == map)).isSome && (conclusion.find? (· == map)).isSome do
        return #["universal f must occur in both the premise and conclusion"]
      unless conclusion.isAppOfArity ``Exists 2 do
        return #["predicate must have an existential conclusion"]
      return #[]

end Flapjack
