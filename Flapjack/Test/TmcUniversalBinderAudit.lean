module

meta import Flapjack.Compiler.Backend.BviTmc.Proofs.Induction
meta import Flapjack.HolRef.TmcUniversalBinder

meta section

/-! The preliminary map-binder check accepts the actual predicate and rejects
hidden, renamed or wrongly typed map binders. It does not certify the full body. -/
open Flapjack Lean Meta

run_meta do
  let .defnInfo info ← getConstInfo ``Flapjack.Compiler.Backend.BviTmc.Induction.hypothesis
    | throwError "missing TMC induction predicate"
  let good ← tmcHypothesisUniversalBinderProblems info.type info.value
  unless good.isEmpty do throwError "actual predicate rejected: {good}"
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
