module

meta import Flapjack.Compiler.Backend.BviTmc.Proofs.Induction
meta import Flapjack.HolRef.TmcUniversalBinder

meta section

/-! The preliminary map-binder check accepts the actual predicate and rejects
hidden, renamed or wrongly typed map binders. It does not certify the full body. -/
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem Lean Meta

set_option linter.unusedVariables false

-- These are well-typed counterexamples, not mutations of an expression with
-- potentially inconsistent applications after a binder type is changed.
private def extraMapDomain {C F : Type} (xs : List Bvi.Exp)
    (source : BviState (Nat × C) F) (clock : Nat) : Prop :=
  source.clock < clock →
  ∀ (env1 : HolFiniteMapExact Nat Bool) (result : BviResult) (final : BviState (Nat × C) F)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (target : BviState C F)
    (env2 : List Value) (loc : Nat), f = f → ∃ _n : Nat, f = f

private def falseClockGuard {C F : Type} (xs : List Bvi.Exp)
    (source : BviState (Nat × C) F) (clock : Nat) : Prop :=
  True →
  ∀ (env1 : List Value) (result : BviResult) (final : BviState (Nat × C) F)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (target : BviState C F)
    (env2 : List Value) (loc : Nat), f = f → ∃ _n : Nat, f = f

run_meta do
  let .defnInfo info ← getConstInfo ``Flapjack.Compiler.Backend.BviTmc.Induction.hypothesis
    | throwError "missing TMC induction predicate"
  let good ← tmcHypothesisUniversalBinderProblems info.type info.value
  unless good.isEmpty do throwError "actual predicate rejected: {good}"
  for (name, message) in [(``extraMapDomain, "universal binder 1 has the wrong name, visibility or carrier"),
      (``falseClockGuard, "clock guard or simulation premise has the wrong shape")] do
    let .defnInfo decoy ← getConstInfo name | throwError "missing decoy {name}"
    unless ← isDefEq info.type decoy.type do throwError "decoy {name} has the wrong outer signature"
    let problems ← tmcHypothesisUniversalBinderProblems decoy.type decoy.value
    unless problems.contains message do throwError "decoy {name} was not rejected for {message}: {problems}"
  let hidden := info.value.replace fun e =>
    match e with
    | .forallE name domain body _ =>
        if name.eraseMacroScopes == `f then some (.forallE name domain body .implicit) else none
    | _ => none
  let renamed := info.value.replace fun e =>
    match e with
    | .forallE name domain body binder =>
        if name.eraseMacroScopes == `f then some (.forallE `other domain body binder) else none
    | _ => none
  let wrongCarrier := info.value.replace fun e =>
    match e with
    | .forallE name _ body binder =>
        if name.eraseMacroScopes == `f then
          some (.forallE name (mkApp2 (mkConst ``HolFiniteMapExact) (mkConst ``Nat) (mkConst ``Bool)) body binder)
        else none
    | _ => none
  let noConclusion := info.value.replace fun e =>
    if e.isAppOfArity ``Exists 2 then some (mkConst ``True) else none
  for (label, bad) in [("hidden map", hidden), ("renamed map", renamed), ("wrong map carrier", wrongCarrier),
      ("missing simulation conclusion", noConclusion)] do
    let problems ← tmcHypothesisUniversalBinderProblems info.type bad
    if problems.isEmpty then throwError "invalid predicate accepted: {label}"
