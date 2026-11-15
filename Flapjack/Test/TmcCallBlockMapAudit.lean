module

import all Flapjack.Compiler.Backend.BviTmc.Proofs.CallBlockCorrectness
meta import Flapjack.HolRef.TmcUniversalBinder
meta import Flapjack.HolRef.TmcCallBlockShape

meta section

/-! The preliminary call-block binder audit checks the six direct binders'
carriers, names, kinds, order and polarity. It does not certify the theorem
statement or complete branch scopes. -/
open Lean Meta Flapjack
open Flapjack.Compiler.Backend.BvlSem

set_option linter.unusedVariables false

private abbrev HiddenRefs := HolFiniteMapExact Nat (Ref Value)
private abbrev HiddenLookup := Nat → Option (Ref Value)

private def validInventory : Prop :=
  ∀ (f : HolFiniteMapExact Nat Nat),
    (∃ (ordinaryMap : HolFiniteMapExact Nat Nat), True) ∧
    (∃ (wrapMap : HolFiniteMapExact Nat Nat), True) ∧
    (∀ (refs : HolFiniteMapExact Nat (Ref Value)), ∃ (auxMap : HolFiniteMapExact Nat Nat), True) ∧
    (∃ (workMap : HolFiniteMapExact Nat Nat), True)

private def wrongRefCarrier : Prop :=
  ∀ (f : HolFiniteMapExact Nat Nat),
    (∃ (ordinaryMap : HolFiniteMapExact Nat Nat), True) ∧
    (∃ (wrapMap : HolFiniteMapExact Nat Nat), True) ∧
    (∀ (refs : HolFiniteMapExact Nat Nat), ∃ (auxMap : HolFiniteMapExact Nat Nat), True) ∧
    (∃ (workMap : HolFiniteMapExact Nat Nat), True)

private def aliasedRefs : Prop :=
  ∀ (f : HolFiniteMapExact Nat Nat),
    (∃ (ordinaryMap : HolFiniteMapExact Nat Nat), True) ∧
    (∃ (wrapMap : HolFiniteMapExact Nat Nat), True) ∧
    (∀ (refs : HiddenRefs), ∃ (auxMap : HolFiniteMapExact Nat Nat), True) ∧
    (∃ (workMap : HolFiniteMapExact Nat Nat), True)

private def extraLookup : Prop :=
  ∀ (_extra : HiddenLookup) (f : HolFiniteMapExact Nat Nat),
    (∃ (ordinaryMap : HolFiniteMapExact Nat Nat), True) ∧
    (∃ (wrapMap : HolFiniteMapExact Nat Nat), True) ∧
    (∀ (refs : HolFiniteMapExact Nat (Ref Value)), ∃ (auxMap : HolFiniteMapExact Nat Nat), True) ∧
    (∃ (workMap : HolFiniteMapExact Nat Nat), True)

private def negativeRefs : Prop :=
  ∀ (f : HolFiniteMapExact Nat Nat),
    (∃ (ordinaryMap : HolFiniteMapExact Nat Nat), True) ∧
    (∃ (wrapMap : HolFiniteMapExact Nat Nat), True) ∧
    (¬ ∀ (refs : HolFiniteMapExact Nat (Ref Value)), ∃ (auxMap : HolFiniteMapExact Nat Nat), False) ∧
    (∃ (workMap : HolFiniteMapExact Nat Nat), True)

private def nestedRefs : Prop :=
  ∀ (_extra : Option (HolFiniteMapExact Nat (Ref Value))) (f : HolFiniteMapExact Nat Nat),
    (∃ (ordinaryMap : HolFiniteMapExact Nat Nat), True) ∧
    (∃ (wrapMap : HolFiniteMapExact Nat Nat), True) ∧
    (∀ (refs : HolFiniteMapExact Nat (Ref Value)), ∃ (auxMap : HolFiniteMapExact Nat Nat), True) ∧
    (∃ (workMap : HolFiniteMapExact Nat Nat), True)

private def shadowedRefs : Prop :=
  ∀ (f : HolFiniteMapExact Nat Nat),
    (∃ (ordinaryMap : HolFiniteMapExact Nat Nat), True) ∧
    (∃ (wrapMap : HolFiniteMapExact Nat Nat), True) ∧
    (∀ (refs : HolFiniteMapExact Nat (Ref Value)),
      ∃ (auxMap : HolFiniteMapExact Nat Nat), ∃ (refs : HolFiniteMapExact Nat (Ref Value)), True) ∧
    (∃ (workMap : HolFiniteMapExact Nat Nat), True)

-- A separate full-shape audit must reject hidden predicates: this inventory
-- intentionally examines direct binders without unfolding arbitrary constants.
private def hiddenMapPredicate : Prop := ∀ (_extra : HolFiniteMapExact Nat Nat), True
private def hiddenMapConjunct : Prop :=
  ∀ (f : HolFiniteMapExact Nat Nat),
    (∃ (ordinaryMap : HolFiniteMapExact Nat Nat), True) ∧
    (∃ (wrapMap : HolFiniteMapExact Nat Nat), True) ∧
    (∀ (refs : HolFiniteMapExact Nat (Ref Value)), ∃ (auxMap : HolFiniteMapExact Nat Nat), True) ∧
    (∃ (workMap : HolFiniteMapExact Nat Nat), hiddenMapPredicate)

run_meta do
  let info ← getConstInfo ``Flapjack.Compiler.Backend.BviTmc.CallBlockCorrectness.evaluate_cb
  let premise ← tmcCallBlockPremiseProblems info.type
  unless premise.isEmpty do throwError "actual call-block premise rejected: {premise}"
  let ordinary ← tmcCallBlockOrdinaryProblems info.type
  unless ordinary.isEmpty do throwError "actual ordinary call-block branch rejected: {ordinary}"
  let wrapper ← tmcCallBlockWrapperProblems info.type
  unless wrapper.isEmpty do throwError "actual call-block wrapper branch rejected: {wrapper}"
  let entries ← tmcCallBlockWorkerEntryProblems info.type
  unless entries.isEmpty do throwError "actual auxiliary/worker entries rejected: {entries}"
  for (binder, name, arity) in [
      (`refs, `Flapjack.Compiler.Backend.BviTmc.stateRefRel, 3),
      (`refs, `Flapjack.Compiler.Backend.BviTmc.CallBlockEnvironment.allocHoleHasVal, 8),
      (`refs, `LE.le, 4),
      (`_work, `Flapjack.Compiler.Backend.BviTmc.holeHasVal, 5),
      (`_work, `Flapjack.Compiler.Backend.BviTmc.holeNotFinalised, 4)] do
    let changed := info.type.replace fun expression =>
      match expression with
      | .forallE n _ _ _ =>
        if n == binder then
          some (expression.replace fun term =>
            if term.isAppOfArity name arity then some (mkConst ``True) else none)
        else none
      | _ => none
    if changed == info.type then throwError "entry mutation did not apply: {name}"
    unless ← isDefEq (← inferType changed) (mkSort Level.zero) do
      throwError "entry mutation is not a well-typed proposition: {name}"
    unless (← tmcCallBlockWrapperProblems changed).isEmpty do
      throwError "entry mutation unexpectedly altered wrapper: {name}"
    if (← tmcCallBlockWorkerEntryProblems changed).isEmpty then
      throwError "entry audit accepted a removed condition: {name}"
  let tiedWork := info.type.replace fun expression =>
    match expression with
    | .forallE `_work _ body visibility =>
      some (.forallE `_work (mkConst ``Unit) body visibility)
    | _ => none
  if tiedWork == info.type then throwError "worker type mutation did not apply"
  unless ← isDefEq (← inferType tiedWork) (mkSort Level.zero) do
    throwError "worker type mutation is not a well-typed proposition"
  unless (← tmcCallBlockWrapperProblems tiedWork).isEmpty do
    throwError "worker type mutation unexpectedly altered wrapper"
  if (← tmcCallBlockWorkerEntryProblems tiedWork).isEmpty then
    throwError "entry audit accepted a specialized worker type"
  for binder in [`refs, `_work] do
    let noPointer := info.type.replace fun expression =>
      match expression with
      | .forallE n _ _ _ =>
        if n == binder then
          some (expression.replace fun term =>
            if term.isAppOfArity ``Eq 3 && term.getAppArgs[1]!.isAppOfArity `Flapjack.holEl 4 then
              some (mkConst ``True)
            else none)
        else none
      | _ => none
    if noPointer == info.type then throwError "pointer mutation did not apply: {binder}"
    unless ← isDefEq (← inferType noPointer) (mkSort Level.zero) do
      throwError "pointer mutation is not a well-typed proposition: {binder}"
    unless (← tmcCallBlockWrapperProblems noPointer).isEmpty do
      throwError "pointer mutation unexpectedly altered wrapper: {binder}"
    if (← tmcCallBlockWorkerEntryProblems noPointer).isEmpty then
      throwError "entry audit accepted a removed pointer equality: {binder}"
  let reversedDomain := info.type.replace fun expression =>
    match expression with
    | .forallE `refs _ _ _ =>
      some (expression.replace fun term =>
        if term.isAppOfArity `LE.le 4 then
          let a := term.getAppArgs
          some (mkAppN term.getAppFn #[a[0]!, a[1]!, a[3]!, a[2]!])
        else none)
    | _ => none
  if reversedDomain == info.type then throwError "domain reversal did not apply"
  unless ← isDefEq (← inferType reversedDomain) (mkSort Level.zero) do
    throwError "domain reversal is not a well-typed proposition"
  unless (← tmcCallBlockWrapperProblems reversedDomain).isEmpty do
    throwError "domain reversal unexpectedly altered wrapper"
  if (← tmcCallBlockWorkerEntryProblems reversedDomain).isEmpty then
    throwError "entry audit accepted a reversed domain inclusion"
  for binder in [`refs, `_work] do
    let wrongFlag := info.type.replace fun expression =>
      match expression with
      | .forallE n _ _ _ =>
        if n == binder then
          some (expression.replace fun term =>
            if term.isAppOfArity `Flapjack.Compiler.Backend.BvlSem.Value.refPtr 2 &&
                term.getAppArgs[0]! == mkConst `Bool.false then
              some (mkApp2 term.getAppFn (mkConst `Bool.true) term.getAppArgs[1]!)
            else none)
        else none
      | _ => none
    if wrongFlag == info.type then throwError "pointer flag mutation did not apply: {binder}"
    unless ← isDefEq (← inferType wrongFlag) (mkSort Level.zero) do
      throwError "pointer flag mutation is not a well-typed proposition: {binder}"
    unless (← tmcCallBlockWrapperProblems wrongFlag).isEmpty do
      throwError "pointer flag mutation unexpectedly altered wrapper: {binder}"
    if (← tmcCallBlockWorkerEntryProblems wrongFlag).isEmpty then
      throwError "entry audit accepted a changed pointer flag: {binder}"
  let wrongIndex := info.type.replace fun expression =>
    match expression with
    | .forallE `_work _ _ _ =>
      some (expression.replace fun term =>
        if term.isAppOfArity `HAdd.hAdd 6 then some term.getAppArgs[4]! else none)
    | _ => none
  if wrongIndex == info.type then throwError "worker index mutation did not apply"
  unless ← isDefEq (← inferType wrongIndex) (mkSort Level.zero) do
    throwError "worker index mutation is not a well-typed proposition"
  unless (← tmcCallBlockWrapperProblems wrongIndex).isEmpty do
    throwError "worker index mutation unexpectedly altered wrapper"
  if (← tmcCallBlockWorkerEntryProblems wrongIndex).isEmpty then
    throwError "entry audit accepted a changed worker index"
  let wrongWrapper := info.type.replace fun expression =>
    if expression.isAppOfArity `Flapjack.Compiler.Backend.BviTmc.wrapperBlockSource 5 then
      some (mkApp (mkConst `Flapjack.Compiler.Backend.Bvi.Exp.var) (mkNatLit 0))
    else none
  if wrongWrapper == info.type then throwError "wrapper program mutation did not apply"
  unless ← isDefEq (← inferType wrongWrapper) (mkSort Level.zero) do
    throwError "wrapper program mutation was not a well-typed proposition"
  if (← tmcCallBlockWrapperProblems wrongWrapper).isEmpty then
    throwError "wrapper audit accepted a changed wrapper program"
  let noCodeGuard := info.type.replace fun expression =>
    if expression.isAppOfArity `Flapjack.Compiler.Backend.BviTmc.optimisedCode 4 then
      some (mkConst ``True)
    else none
  if noCodeGuard == info.type then throwError "optimized-code mutation did not apply"
  unless ← isDefEq (← inferType noCodeGuard) (mkSort Level.zero) do
    throwError "optimized-code mutation was not a well-typed proposition"
  if (← tmcCallBlockWrapperProblems noCodeGuard).isEmpty then
    throwError "wrapper audit accepted a removed optimized-code guard"
  let noConstructorGuard := info.type.replace fun expression =>
    if expression.isAppOfArity ``Eq 3 && expression.getAppArgs[2]!.isAppOfArity
        `Flapjack.Compiler.Backend.BviTmc.CallBlock.callBlock 4 then
      some (mkConst ``True)
    else none
  if noConstructorGuard == info.type then throwError "wrapper constructor mutation did not apply"
  unless ← isDefEq (← inferType noConstructorGuard) (mkSort Level.zero) do
    throwError "wrapper constructor mutation was not a well-typed proposition"
  if (← tmcCallBlockWrapperProblems noConstructorGuard).isEmpty then
    throwError "wrapper audit accepted a removed constructor premise"
  let noWrapperRun := info.type.replace fun expression =>
    match expression with
    | .forallE `tag _ _ _ =>
      some (expression.replace fun term =>
        if term.isAppOfArity ``Eq 3 &&
            term.getAppArgs[1]!.isAppOfArity `Flapjack.Compiler.Backend.BviSem.evaluate 5 then
          some (mkConst ``True)
        else none)
    | _ => none
  if noWrapperRun == info.type then throwError "wrapper evaluation mutation did not apply"
  unless ← isDefEq (← inferType noWrapperRun) (mkSort Level.zero) do
    throwError "wrapper evaluation mutation was not a well-typed proposition"
  unless (← tmcCallBlockOrdinaryProblems noWrapperRun).isEmpty do
    throwError "wrapper evaluation mutation unexpectedly altered ordinary branch"
  if (← tmcCallBlockWrapperProblems noWrapperRun).isEmpty then
    throwError "wrapper audit accepted a removed evaluation clause"
  for (name, arity) in [(`Flapjack.Compiler.Backend.BviTmc.onlyFresh, 3),
      (`Flapjack.Compiler.Backend.BviTmc.holesUnchangedExcept, 7),
      (`Flapjack.Compiler.Backend.BviTmc.holesStillNotFinalised, 6),
      (`Flapjack.Compiler.Backend.BviTmc.stateRel, 5),
      (`Flapjack.HolFiniteMapExact.submap, 4),
      (`Flapjack.SemanticPrimitivesProps.resultRel, 8)] do
    let changed := info.type.replace fun expression =>
      match expression with
      | .forallE `tag _ _ _ =>
        some (expression.replace fun term =>
          if term.isAppOfArity name arity then some (mkConst ``True) else none)
      | _ => none
    if changed == info.type then throwError "wrapper frame mutation did not apply: {name}"
    unless ← isDefEq (← inferType changed) (mkSort Level.zero) do
      throwError "wrapper frame mutation was not a well-typed proposition: {name}"
    unless (← tmcCallBlockOrdinaryProblems changed).isEmpty do
      throwError "wrapper mutation unexpectedly altered ordinary branch: {name}"
    if (← tmcCallBlockWrapperProblems changed).isEmpty then
      throwError "wrapper audit accepted a removed frame condition: {name}"
  for (name, arity) in [(`Flapjack.Compiler.Backend.BviTmc.onlyFresh, 3),
      (`Flapjack.Compiler.Backend.BviTmc.holesUnchangedExcept, 7),
      (`Flapjack.Compiler.Backend.BviTmc.holesStillNotFinalised, 6)] do
    let changed := info.type.replace fun expression =>
      if expression.isAppOfArity name arity then some (mkConst ``True) else none
    if changed == info.type then throwError "ordinary branch mutation did not apply: {name}"
    unless ← isDefEq (← inferType changed) (mkSort Level.zero) do
      throwError "ordinary branch mutation was not a well-typed proposition: {name}"
    if (← tmcCallBlockOrdinaryProblems changed).isEmpty then
      throwError "ordinary branch audit accepted a removed condition: {name}"
  let wrongVisibility := match info.type with
    | .forallE name domain body _ => .forallE name domain body .default
    | _ => info.type
  unless ← isDefEq (← inferType wrongVisibility) (mkSort Level.zero) do
    throwError "outer visibility mutation was not a well-typed proposition"
  if (← tmcCallBlockPremiseProblems wrongVisibility).isEmpty then
    throwError "call-block premise audit accepted a visible compiler type"
  for (name, arity) in [(`Flapjack.Compiler.Backend.BviTmc.wfBlock, 2),
      (`Flapjack.Compiler.Backend.BviTmc.envRel, 4),
      (`Flapjack.Compiler.Backend.BviTmc.stateRel, 5), (`LE.le, 4), (``Ne, 3),
      (`Flapjack.Compiler.Backend.BviTmc.Induction.hypothesis, 5)] do
    let weakened := info.type.replace fun expression =>
      if expression.isAppOfArity name arity then some (mkConst ``True) else none
    if weakened == info.type then throwError "premise mutation did not apply: {name}"
    unless ← isDefEq (← inferType weakened) (mkSort Level.zero) do
      throwError "premise mutation was not a well-typed proposition: {name}"
    if (← tmcCallBlockPremiseProblems weakened).isEmpty then
      throwError "call-block premise audit accepted a removed condition: {name}"
  let noRun := info.type.replace fun expression =>
    if expression.isAppOfArity ``Eq 3 &&
        expression.getAppArgs[1]!.isAppOfArity `Flapjack.Compiler.Backend.BviSem.evaluate 5 then
      some (mkConst ``True)
    else none
  if noRun == info.type then throwError "evaluation-premise mutation did not apply"
  unless ← isDefEq (← inferType noRun) (mkSort Level.zero) do
    throwError "evaluation-premise mutation was not a well-typed proposition"
  if (← tmcCallBlockPremiseProblems noRun).isEmpty then
    throwError "call-block premise audit accepted a removed evaluation premise"
  let hidden := info.type.replace fun expression =>
    if expression.isAppOfArity `Flapjack.Compiler.Backend.BviTmc.wfBlock 2 then
      some (mkApp2 (mkConst ``And) expression (mkConst ``hiddenMapPredicate))
    else none
  if hidden == info.type then throwError "hidden premise mutation did not apply"
  unless ← isDefEq (← inferType hidden) (mkSort Level.zero) do
    throwError "hidden premise mutation was not a well-typed proposition"
  if (← tmcCallBlockPremiseProblems hidden).isEmpty then
    throwError "call-block premise audit accepted an extra named predicate"
  let actual ← tmcCallBlockMapInventoryProblems info.type
  unless actual.isEmpty do throwError "actual call-block binder inventory rejected: {actual}"
  let .defnInfo valid ← getConstInfo ``validInventory | throwError "missing valid fixture"
  let validProblems ← tmcCallBlockMapInventoryProblems valid.value
  unless validProblems.isEmpty do throwError "valid call-block inventory rejected: {validProblems}"
  for name in [``wrongRefCarrier, ``aliasedRefs, ``extraLookup, ``negativeRefs,
      ``nestedRefs, ``shadowedRefs] do
    let .defnInfo decoy ← getConstInfo name | throwError "missing call-block fixture {name}"
    let problems ← tmcCallBlockMapInventoryProblems decoy.value
    if problems.isEmpty then throwError "invalid call-block inventory accepted: {name}"
  let .defnInfo hidden ← getConstInfo ``hiddenMapConjunct | throwError "missing hidden-map fixture"
  unless (← tmcCallBlockMapInventoryProblems hidden.value).isEmpty do
    throwError "direct-binder audit no longer exhibits its documented named-predicate boundary"
