import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Semantics
import Flapjack.HolRef.SimulationBody

/-! Elaborated regression tests for the prospective simulation-body check.
The fixture is untagged and is not a proof of compiler correctness. -/

open Flapjack Flapjack.Compiler.Backend Flapjack.SemanticPrimitivesHOL
open Flapjack.SemanticPrimitivesProps Lean Meta

private def simulationBodyFixture {C₁ C₂ F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code1 : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (co1 : ClosSem.CompileOracle C₁)
    (cc1 : ClosSem.Compiler C₁) (es1 : List ClosLang.Exp) (code2 : Spt (Nat × Bvl.Exp))
    (co2 : BvlSem.CompileOracle C₂) (cc2 : BvlSem.Compiler C₂) (start : Nat)
    (rel : HolFiniteMapExact Nat (Nat × ClosLang.Exp) → ClosSem.CompileOracle C₁ →
      ClosSem.Compiler C₁ → List ClosLang.Exp → Spt (Nat × Bvl.Exp) →
      BvlSem.CompileOracle C₂ → BvlSem.Compiler C₂ → Nat → Prop) : Prop :=
  ∀ (k : Nat) (res1 : Result (List ClosSem.Value) ClosSem.Value) (s2 : ClosSem.State C₁ F),
    ClosSem.evaluate es1 [] (ClosSem.initialState ffi maxApp code1 co1 cc1 k) = (res1, s2) ∧
    res1 ≠ .err (.abort .typeError) ∧ rel code1 co1 cc1 es1 code2 co2 cc2 start →
    ∃ (ck : Nat) (res2 : Result (List BvlSem.Value) BvlSem.Value) (t2 : BvlSem.State C₂ F),
      BvlSem.evaluate [.call 0 (some start) []] []
        (BvlSem.initialState ffi code2 co2 cc2 (k + ck)) = (res2, t2) ∧
      resultRel (fun _ _ => True) (fun _ _ => True) res1 res2 ∧ s2.ffi = t2.ffi

private def clonedResultRel := @resultRel

run_meta do
  let .defnInfo info ← getConstInfo ``simulationBodyFixture | throwError "missing simulation fixture"
  let good ← predicateDomainSimulationBodyProblems info.type info.value
  unless good.isEmpty do throwError "valid simulation body rejected: {good}"
  let noSafety := info.value.replace fun e =>
    if e.isAppOfArity ``Ne 3 then some (mkConst ``True) else none
  let noTarget := info.value.replace fun e =>
    if e.isAppOfArity ``Exists 2 then some (mkConst ``True) else none
  let noRelation := info.value.replace fun e =>
    if e.isAppOfArity ``resultRel 8 then some (mkConst ``True) else none
  let falseRelation := info.value.replace fun e =>
    if e.isConstOf ``True then some (mkConst ``False) else none
  let clonedRelation := info.value.replace fun e =>
    if e.isConstOf ``resultRel then some (mkConst ``clonedResultRel) else none
  let noFfi := info.value.replace fun e =>
    if e.isAppOfArity ``Eq 3 && (e.getAppArgs[1]!).isAppOfArity ``ClosSem.State.ffi 3 then
      some (mkConst ``True)
    else none
  let noClockExtension := info.value.replace fun e =>
    if e.isAppOfArity ``HAdd.hAdd 6 then some e.getAppArgs[4]! else none
  let noStart := info.value.replace fun e =>
    if e.isAppOfArity ``Option.some 2 then some (mkApp (mkConst ``Option.none [Level.zero]) e.getAppArgs[0]!)
    else none
  let timeoutInstead := info.value.replace fun e =>
    if e.isConstOf ``Abort.typeError then some (mkConst ``Abort.timeoutError) else none
  let hiddenClock ← lambdaTelescope info.value fun args body => do
    match body with
    | .forallE name domain rest _ => mkLambdaFVars args (.forallE name domain rest BinderInfo.implicit)
    | _ => return info.value
  for (label, bad) in [("missing safety", noSafety), ("missing target", noTarget),
      ("missing result relation", noRelation), ("missing FFI equality", noFfi),
      ("false result relation", falseRelation), ("alternate relation head", clonedRelation),
      ("missing clock extension", noClockExtension), ("missing start", noStart),
      ("wrong abort", timeoutInstead), ("implicit clock", hiddenClock)] do
    if label != "implicit clock" && bad == info.value then
      throwError "fixture mutation {label} did not apply"
    let problems ← predicateDomainSimulationBodyProblems info.type bad
    if problems.isEmpty then throwError "invalid simulation body accepted: {label}"
