module

import all Flapjack.Compiler.Backend.BviTmc.Proofs.Induction
meta import Flapjack.HolRef.TmcUniversalBinder
meta import Flapjack.FiniteMap.BroadCodec

meta section

/-! The preliminary map-binder check accepts the actual predicate and rejects
hidden, renamed or wrongly typed map binders. It does not certify the full body. -/
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BviTmc Lean Meta

set_option linter.unusedVariables false

private theorem alternativeExpInhabited : Nonempty Bvi.Exp := ⟨.var 0⟩
private theorem alternativeValueInhabited : Nonempty Value := ⟨.number 0⟩

private def erasedToBroad {K V : Type} (_map : HolFiniteMapExact K V) : FiniteMapBroad K V :=
  ⟨fun _ => none, ⟨[], by simp⟩⟩

private def erasedFromBroad {K V : Type} (_map : FiniteMapBroad K V) : HolFiniteMapExact K V :=
  HolFiniteMapExact.empty

private theorem conditionalMapWitness (f : HolFiniteMapExact Nat Nat) (_extra : True) :
    (∀ key, (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).lookup key = f.lookup key) ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f) = f :=
  Induction.holFmapAsFiniteSupportUniversalWitness_hypothesis_f f

private theorem vacuousMapWitness (f : HolFiniteMapExact Nat Nat) :
    (∀ key, f.lookup key = f.lookup key) ∧ f.finiteSupport = f.finiteSupport ∧ f = f := by
  exact ⟨fun _ => rfl, rfl, rfl⟩

private theorem missingSupportWitness (f : HolFiniteMapExact Nat Nat) :
    (∀ key, (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f)).lookup key = f.lookup key) ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad f) = f := by
  cases f
  exact ⟨fun _ => rfl, rfl⟩

private abbrev HiddenPointerMap := HolFiniteMapExact Nat Nat

private def inventoryValid : Prop :=
  ∀ (f : HolFiniteMapExact Nat Nat),
    ∃ (nextMap : HolFiniteMapExact Nat Nat), ∃ (wrapMap : HolFiniteMapExact Nat Nat),
      ∃ (workMap : HolFiniteMapExact Nat Nat), True

private def inventoryAliased : Prop :=
  ∀ (f : HiddenPointerMap),
    ∃ (nextMap : HolFiniteMapExact Nat Nat), ∃ (wrapMap : HolFiniteMapExact Nat Nat),
      ∃ (workMap : HolFiniteMapExact Nat Nat), True

private def inventoryExtraNegative : Prop :=
  (∀ (_extra : HolFiniteMapExact Nat Nat), True) → inventoryValid

private def inventoryNegativeF : Prop :=
  (∀ (f : HolFiniteMapExact Nat Nat), True) →
    ∃ (nextMap : HolFiniteMapExact Nat Nat), ∃ (wrapMap : HolFiniteMapExact Nat Nat),
      ∃ (workMap : HolFiniteMapExact Nat Nat), True

private def inventoryNegatedF : Prop :=
  (¬ ∀ (f : HolFiniteMapExact Nat Nat), False) ∧
    ∃ (nextMap : HolFiniteMapExact Nat Nat), ∃ (wrapMap : HolFiniteMapExact Nat Nat),
      ∃ (workMap : HolFiniteMapExact Nat Nat), True

private def inventoryEqualityF : Prop :=
  ((∀ (f : HolFiniteMapExact Nat Nat), True) = True) ∧
    ∃ (nextMap : HolFiniteMapExact Nat Nat), ∃ (wrapMap : HolFiniteMapExact Nat Nat),
      ∃ (workMap : HolFiniteMapExact Nat Nat), True

private def inventoryNegatedAll : Prop :=
  ¬ ∀ (f : HolFiniteMapExact Nat Nat),
    ∃ (nextMap : HolFiniteMapExact Nat Nat), ∃ (wrapMap : HolFiniteMapExact Nat Nat),
      ∃ (workMap : HolFiniteMapExact Nat Nat), True

private def inventoryInertLet : Prop :=
  let _ignored : Prop := ∀ (f : HolFiniteMapExact Nat Nat),
    ∃ (nextMap : HolFiniteMapExact Nat Nat), ∃ (wrapMap : HolFiniteMapExact Nat Nat),
      ∃ (workMap : HolFiniteMapExact Nat Nat), True
  True

private def inventoryInertApplication : Prop :=
  (fun _ : Prop => True) (∀ (f : HolFiniteMapExact Nat Nat),
    ∃ (nextMap : HolFiniteMapExact Nat Nat), ∃ (wrapMap : HolFiniteMapExact Nat Nat),
      ∃ (workMap : HolFiniteMapExact Nat Nat), True)

private def inventoryNested : Prop :=
  ∀ (_extra : Option (HolFiniteMapExact Nat Nat)), inventoryValid

private def inventoryNestedAlias : Prop :=
  ∀ (_extra : Option HiddenPointerMap) (f : HolFiniteMapExact Nat Nat),
    ∃ (nextMap : HolFiniteMapExact Nat Nat), ∃ (wrapMap : HolFiniteMapExact Nat Nat),
      ∃ (workMap : HolFiniteMapExact Nat Nat), True

private def inventoryRaw : Prop :=
  ∀ (_extra : Nat → Option Nat), inventoryValid

private abbrev HiddenLookup := Nat → Option Nat
private abbrev HiddenKey := Nat
private abbrev HiddenOptional := Option Nat

private def inventoryRawAliasedKey : Prop :=
  ∀ (_extra : HiddenKey → Option Nat) (f : HolFiniteMapExact Nat Nat),
    ∃ (nextMap : HolFiniteMapExact Nat Nat), ∃ (wrapMap : HolFiniteMapExact Nat Nat),
      ∃ (workMap : HolFiniteMapExact Nat Nat), True

private def inventoryNestedRawAliasedKey : Prop :=
  ∀ (_extra : Option (HiddenKey → Option Nat)) (f : HolFiniteMapExact Nat Nat),
    ∃ (nextMap : HolFiniteMapExact Nat Nat), ∃ (wrapMap : HolFiniteMapExact Nat Nat),
      ∃ (workMap : HolFiniteMapExact Nat Nat), True

private def inventoryRawAliasedResult : Prop :=
  ∀ (_extra : Nat → HiddenOptional) (f : HolFiniteMapExact Nat Nat),
    ∃ (nextMap : HolFiniteMapExact Nat Nat), ∃ (wrapMap : HolFiniteMapExact Nat Nat),
      ∃ (workMap : HolFiniteMapExact Nat Nat), True

private def inventoryRawWrongKey : Prop :=
  ∀ (_extra : Bool → Option Nat) (f : HolFiniteMapExact Nat Nat),
    ∃ (nextMap : HolFiniteMapExact Nat Nat), ∃ (wrapMap : HolFiniteMapExact Nat Nat),
      ∃ (workMap : HolFiniteMapExact Nat Nat), True

private def inventoryNestedRaw : Prop :=
  ∀ (_extra : Option HiddenLookup) (f : HolFiniteMapExact Nat Nat),
    ∃ (nextMap : HolFiniteMapExact Nat Nat), ∃ (wrapMap : HolFiniteMapExact Nat Nat),
      ∃ (workMap : HolFiniteMapExact Nat Nat), True

private def inventoryShadowed : Prop :=
  ∀ (f : HolFiniteMapExact Nat Nat), ∃ (nextMap : HolFiniteMapExact Nat Nat),
    ∃ (wrapMap : HolFiniteMapExact Nat Nat), ∃ (workMap : HolFiniteMapExact Nat Nat),
      ∃ (f : HolFiniteMapExact Nat Nat), True

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

private def fakeSimulation {C F : Type} (xs : List Bvi.Exp)
    (source : BviState (Nat × C) F) (clock : Nat) : Prop :=
  source.clock < clock →
  ∀ (env1 : List Value) (result : BviResult) (final : BviState (Nat × C) F)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (target : BviState C F)
    (env2 : List Value) (loc : Nat), f = f → ∃ _n : Nat, f = f

private def fakeConclusion {C F : Type} (xs : List Bvi.Exp)
    (source : BviState (Nat × C) F) (clock : Nat) : Prop :=
  source.clock < clock →
  ∀ (env1 : List Value) (result : BviResult) (final : BviState (Nat × C) F)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (target : BviState C F)
    (env2 : List Value) (loc : Nat),
    evaluate xs env1 source = (result, final) ∧ envRel opt f env1 env2 ∧
      (∀ x ∈ xs, noMutcons x) ∧ stateRel f source target ∧
      (opt = true → xs.length = 1) ∧ result ≠ .err (.abort .typeError) →
    ∃ _dummy : Nat, f = f

private def fakeOptimizedBranches {C F : Type} (xs : List Bvi.Exp)
    (source : BviState (Nat × C) F) (clock : Nat) : Prop :=
  source.clock < clock →
  ∀ (env1 : List Value) (result : BviResult) (final : BviState (Nat × C) F)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (target : BviState C F)
    (env2 : List Value) (loc : Nat),
    evaluate xs env1 source = (result, final) ∧ envRel opt f env1 env2 ∧
      (∀ x ∈ xs, noMutcons x) ∧ stateRel f source target ∧
      (opt = true → xs.length = 1) ∧ result ≠ .err (.abort .typeError) →
    ∃ (next : BviState C F), ∃ (nextMap : HolFiniteMapExact Nat Nat), ∃ (nextResult : BviResult),
      evaluate xs env2 target = (nextResult, next) ∧
      SemanticPrimitivesProps.resultRel (List.Forall₂ (valueRel nextMap))
        (ResultRelation.eorRel nextMap) result nextResult ∧
      stateRel nextMap final next ∧ f.submap nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs next.refs ∅ ∧
      holesStillNotFinalised f target.refs next.refs ∧
      ∀ locOpt, optimisedCode loc locOpt source.code target.code → True ∧ True

private def mutateConclusion (value : Expr) (rewrite : Expr → Option Expr) : MetaM Expr :=
  lambdaTelescope value fun parameters body =>
    forallTelescope body fun binders conclusion => do
      let modified ← mkForallFVars binders (conclusion.replace rewrite)
      mkLambdaFVars parameters modified

private def mutateWrapper (value : Expr) (head : Name) (arity : Nat) : MetaM Expr :=
  mutateConclusion value fun e =>
    match e with
    | .forallE name _ _ _ =>
      if name.eraseMacroScopes == `wrap then
        some (e.replace fun term => if term.isAppOfArity head arity then some (mkConst ``True) else none)
      else none
    | _ => none

private def mutateWorker (value : Expr) (rewrite : Expr → Option Expr) : MetaM Expr :=
  mutateConclusion value fun e =>
    match e with
    | .app (.app (.const ``And []) (.forallE name domain body binder)) worker =>
      if name.eraseMacroScopes == `wrap then
        some (mkApp2 (mkConst ``And) (.forallE name domain body binder) (worker.replace rewrite))
      else none
    | _ => none

run_meta do
  let .defnInfo info ← getConstInfo ``Flapjack.Compiler.Backend.BviTmc.Induction.hypothesis
    | throwError "missing TMC induction predicate"
  let declarationProblems ← tmcHypothesisDeclarationProblems ``Flapjack.Compiler.Backend.BviTmc.Induction.hypothesis
  unless declarationProblems.isEmpty do throwError "actual hypothesis declaration rejected: {declarationProblems}"
  let wrongOwner ← tmcHypothesisDeclarationProblems ``inventoryValid
  if wrongOwner.isEmpty then throwError "unrelated declaration accepted by TMC hypothesis audit"
  for (name, toBroad) in [(``erasedToBroad, true), (``erasedFromBroad, false)] do
    let .defnInfo codec ← getConstInfo name | throwError "missing codec decoy {name}"
    let problems ← tmcCodecBodyProblems codec.type codec.value toBroad
    if problems.isEmpty then throwError "erased codec accepted: {name}"
  for name in [``conditionalMapWitness, ``vacuousMapWitness, ``missingSupportWitness] do
    let witness ← getConstInfo name
    let problems ← tmcMapWitnessTypeProblems witness.type
    if problems.isEmpty then throwError "invalid map witness accepted: {name}"
  lambdaTelescope info.value fun _ body => do
    let inventory ← tmcHypothesisMapInventoryProblems body
    unless inventory.isEmpty do throwError "actual predicate map inventory rejected: {inventory}"
  let .defnInfo inventory ← getConstInfo ``inventoryValid | throwError "missing valid inventory fixture"
  let validInventory ← tmcHypothesisMapInventoryProblems inventory.value
  unless validInventory.isEmpty do throwError "valid map inventory rejected: {validInventory}"
  for name in [``inventoryAliased, ``inventoryExtraNegative, ``inventoryNegativeF, ``inventoryNegatedF,
      ``inventoryEqualityF, ``inventoryNegatedAll, ``inventoryInertLet, ``inventoryInertApplication,
      ``inventoryNested, ``inventoryNestedAlias, ``inventoryRaw, ``inventoryNestedRaw,
      ``inventoryRawAliasedKey, ``inventoryNestedRawAliasedKey, ``inventoryRawAliasedResult, ``inventoryRawWrongKey,
      ``inventoryShadowed] do
    let .defnInfo decoy ← getConstInfo name | throwError "missing inventory decoy {name}"
    let problems ← tmcHypothesisMapInventoryProblems decoy.value
    if problems.isEmpty then throwError "invalid map inventory accepted: {name}"
  let good ← tmcHypothesisUniversalBinderProblems info.type info.value
  unless good.isEmpty do throwError "actual predicate rejected: {good}"
  let alternativeWitness := info.value.replace fun e =>
    if e.isAppOfArity ``holHd 3 && e.getAppArgs[0]! == mkConst ``Bvi.Exp then
      some (mkAppN (mkConst ``holHd) #[e.getAppArgs[0]!, mkConst ``alternativeExpInhabited, e.getAppArgs[2]!])
    else none
  if alternativeWitness == info.value then throwError "inhabitation proof substitution did not apply"
  unless ← isDefEq info.value alternativeWitness do throwError "inhabitation proofs are not definitionally equal"
  let alternativeProblems ← tmcHypothesisUniversalBinderProblems info.type alternativeWitness
  unless alternativeProblems.isEmpty do throwError "equivalent inhabitation proof rejected: {alternativeProblems}"
  let alternativeValueWitness := info.value.replace fun e =>
    if e.isAppOfArity ``holEl 4 && e.getAppArgs[0]! == mkConst ``Value then
      some (mkAppN (mkConst ``holEl) #[e.getAppArgs[0]!, mkConst ``alternativeValueInhabited,
        e.getAppArgs[2]!, e.getAppArgs[3]!])
    else none
  if alternativeValueWitness == info.value then throwError "value inhabitation proof substitution did not apply"
  unless ← isDefEq info.value alternativeValueWitness do throwError "value inhabitation proofs are not definitionally equal"
  let alternativeValueProblems ← tmcHypothesisUniversalBinderProblems info.type alternativeValueWitness
  unless alternativeValueProblems.isEmpty do
    throwError "equivalent value inhabitation proof rejected: {alternativeValueProblems}"
  for (name, message) in [(``extraMapDomain, "universal binder 1 has the wrong name, visibility or carrier"),
      (``falseClockGuard, "clock guard or simulation premise has the wrong shape"),
      (``fakeSimulation, "simulation premise must contain the six original conjuncts"),
      (``fakeConclusion, "next has the wrong carrier"),
      (``fakeOptimizedBranches, "wrapper simulation binders changed")] do
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
  let noSourceRun := info.value.replace fun e =>
    if e.isAppOfArity ``Eq 3 &&
        (e.getAppArgs[1]!).isAppOfArity ``BviSem.evaluate 5 then some (mkConst ``True) else none
  let noEnvRelation := info.value.replace fun e =>
    if e.isAppOfArity ``Flapjack.Compiler.Backend.BviTmc.envRel 4 then some (mkConst ``True) else none
  let noSafeExpressions := info.value.replace fun e =>
    if e.isAppOfArity ``Flapjack.Compiler.Backend.BviTmc.noMutcons 1 then some (mkConst ``True) else none
  let noStateRelation := info.value.replace fun e =>
    if e.isAppOfArity ``Flapjack.Compiler.Backend.BviTmc.stateRel 5 then some (mkConst ``True) else none
  let noSingleton := info.value.replace fun e =>
    if e.isAppOfArity ``Eq 3 && (e.getAppArgs[1]!).isAppOfArity ``List.length 2 then
      some (mkConst ``True) else none
  let noTypeSafety := info.value.replace fun e =>
    if e.isAppOfArity ``Ne 3 then some (mkConst ``True) else none
  let noResultRelation := info.value.replace fun e =>
    if e.isAppOfArity ``Flapjack.SemanticPrimitivesProps.resultRel 8 then some (mkConst ``True) else none
  let noSubmap := info.value.replace fun e =>
    if e.isAppOfArity ``HolFiniteMapExact.submap 4 then some (mkConst ``True) else none
  let noFresh := info.value.replace fun e =>
    if e.isAppOfArity ``onlyFresh 3 then some (mkConst ``True) else none
  let noUnchanged := info.value.replace fun e =>
    if e.isAppOfArity ``holesUnchangedExcept 7 then some (mkConst ``True) else none
  let noNotFinal := info.value.replace fun e =>
    if e.isAppOfArity ``holesStillNotFinalised 6 then some (mkConst ``True) else none
  let noTargetRun ← mutateConclusion info.value fun e =>
    if e.isAppOfArity ``Eq 3 &&
        (e.getAppArgs[1]!).isAppOfArity ``BviSem.evaluate 5 then some (mkConst ``True) else none
  let noTargetState ← mutateConclusion info.value fun e =>
    if e.isAppOfArity ``stateRel 5 then some (mkConst ``True) else none
  let noOptimizedCode ← mutateConclusion info.value fun e =>
    if e.isAppOfArity ``optimisedCode 4 then some (mkConst ``True) else none
  let noWrapper ← mutateConclusion info.value fun e =>
    match e with
    | .forallE name _ _ _ => if name.eraseMacroScopes == `wrap then some (mkConst ``True) else none
    | _ => none
  let noWrapperRewrite ← mutateConclusion info.value fun e =>
    if e.isAppOfArity ``rewriteWrapperSource 4 then
      some (mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Bvi.Exp)) else none
  let wrongWrapperHead ← mutateConclusion info.value fun e =>
    if e.isAppOfArity ``holHd 3 && e.getAppArgs[0]! == mkConst ``Bvi.Exp then
      some (mkAppN (mkConst ``holHd) #[e.getAppArgs[0]!, e.getAppArgs[1]!,
        mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Bvi.Exp)]) else none
  let wrongWrapperLocation ← mutateConclusion info.value fun e =>
    if e.isAppOfArity ``rewriteWrapperSource 4 then
      some (mkAppN (mkConst ``rewriteWrapperSource)
        #[e.getAppArgs[1]!, e.getAppArgs[1]!, e.getAppArgs[2]!, e.getAppArgs[3]!]) else none
  let noWrapperRun ← mutateConclusion info.value fun e =>
    if e.isAppOfArity ``Eq 3 && (e.getAppArgs[1]!).isAppOfArity ``BviSem.evaluate 5 &&
        ((e.getAppArgs[1]!).getAppArgs[2]!).isAppOfArity ``List.cons 3 then
      some (mkConst ``True) else none
  let noWrapperResult ← mutateWrapper info.value ``Flapjack.SemanticPrimitivesProps.resultRel 8
  let noWrapperState ← mutateWrapper info.value ``stateRel 5
  let noWrapperSubmap ← mutateWrapper info.value ``HolFiniteMapExact.submap 4
  let noWrapperFresh ← mutateWrapper info.value ``onlyFresh 3
  let noWrapperUnchanged ← mutateWrapper info.value ``holesUnchangedExcept 7
  let noWrapperNotFinal ← mutateWrapper info.value ``holesStillNotFinalised 6
  let noWorker ← mutateConclusion info.value fun e =>
    match e with
    | .app (.app (.const ``And []) (.forallE name domain body binder)) _ =>
      if name.eraseMacroScopes == `wrap then
        some (mkApp2 (mkConst ``And) (.forallE name domain body binder) (mkConst ``True))
      else none
    | _ => none
  let noWorkerInitialHole ← mutateWorker info.value fun e =>
    if e.isAppOfArity ``holeHasVal 5 then some (mkConst ``True) else none
  let noWorkerNotFinal ← mutateWorker info.value fun e =>
    if e.isAppOfArity ``holeNotFinalised 4 then some (mkConst ``True) else none
  let noWorkerPointer ← mutateWorker info.value fun e =>
    if e.isAppOfArity ``Eq 3 && (e.getAppArgs[1]!).isAppOfArity ``holEl 4 then
      some (mkConst ``True) else none
  let noWorkerRewrite ← mutateWorker info.value fun e =>
    if e.isAppOfArity ``rewriteWorkerSource 6 then some e.getAppArgs[5]! else none
  let wrongWorkerIndex ← mutateWorker info.value fun e =>
    if e.isAppOfArity ``rewriteWorkerSource 6 then
      some (mkAppN (mkConst ``rewriteWorkerSource)
        #[e.getAppArgs[0]!, e.getAppArgs[1]!, e.getAppArgs[2]!, e.getAppArgs[2]!,
          e.getAppArgs[4]!, e.getAppArgs[5]!]) else none
  let wrongWorkerPointerIndex ← mutateWorker info.value fun e =>
    if e.isAppOfArity ``holEl 4 && e.getAppArgs[0]! == mkConst ``Value then
      some (mkAppN (mkConst ``holEl) #[e.getAppArgs[0]!, e.getAppArgs[1]!,
        mkNatLit 0, e.getAppArgs[3]!]) else none
  let wrongWorkerPointerList ← mutateWorker info.value fun e =>
    if e.isAppOfArity ``holEl 4 && e.getAppArgs[0]! == mkConst ``Value then
      some (mkAppN (mkConst ``holEl) #[e.getAppArgs[0]!, e.getAppArgs[1]!,
        e.getAppArgs[2]!, mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Value)]) else none
  let noWorkerResult ← mutateWorker info.value fun e =>
    if e.isAppOfArity ``ResultRelation.optResRel 3 then some (mkConst ``True) else none
  let noWorkerState ← mutateWorker info.value fun e =>
    if e.isAppOfArity ``stateRel 5 then some (mkConst ``True) else none
  let noWorkerSubmap ← mutateWorker info.value fun e =>
    if e.isAppOfArity ``HolFiniteMapExact.submap 4 then some (mkConst ``True) else none
  let noWorkerFresh ← mutateWorker info.value fun e =>
    if e.isAppOfArity ``onlyFresh 3 then some (mkConst ``True) else none
  let noWorkerUnchanged ← mutateWorker info.value fun e =>
    if e.isAppOfArity ``holesUnchangedExcept 7 then some (mkConst ``True) else none
  let noWorkerStill ← mutateWorker info.value fun e =>
    if e.isAppOfArity ``holesStillNotFinalised 6 then some (mkConst ``True) else none
  let noWorkerBlock ← mutateWorker info.value fun e =>
    if e.isAppOfArity ``mutableBlockRel 5 then some (mkConst ``True) else none
  let noWorkerReturnCondition ← mutateWorker info.value fun e =>
    if e.isAppOfArity ``Eq 3 &&
        (e.getAppArgs[2]!).isAppOfArity ``Flapjack.SemanticPrimitivesHOL.Result.val 3 then
      some (mkConst ``True) else none
  let noWorkerFinalHole ← mutateWorker info.value fun e =>
    match e with
    | .forallE name _ _ _ =>
      if name.eraseMacroScopes == `resValue then
        some (e.replace fun term => if term.isAppOfArity ``holeHasVal 5 then some (mkConst ``True) else none)
      else none
    | _ => none
  for (label, bad) in [("hidden map", hidden), ("renamed map", renamed), ("wrong map carrier", wrongCarrier),
      ("missing simulation conclusion", noConclusion), ("missing source run", noSourceRun),
      ("missing environment relation", noEnvRelation), ("missing expression safety", noSafeExpressions),
      ("missing state relation", noStateRelation), ("missing singleton bound", noSingleton),
      ("missing type safety", noTypeSafety), ("missing result relation", noResultRelation),
      ("missing submap", noSubmap), ("missing freshness", noFresh),
      ("missing unchanged holes", noUnchanged), ("missing unfinished holes", noNotFinal),
      ("missing target run", noTargetRun), ("missing target state", noTargetState),
      ("missing optimized code premise", noOptimizedCode), ("missing wrapper", noWrapper),
      ("missing wrapper rewrite", noWrapperRewrite), ("wrong wrapper head", wrongWrapperHead),
      ("wrong wrapper location", wrongWrapperLocation), ("missing wrapper run", noWrapperRun),
      ("missing wrapper result relation", noWrapperResult), ("missing wrapper state", noWrapperState),
      ("missing wrapper submap", noWrapperSubmap), ("missing wrapper freshness", noWrapperFresh),
      ("missing wrapper unchanged holes", noWrapperUnchanged), ("missing wrapper unfinished holes", noWrapperNotFinal),
      ("missing worker", noWorker), ("missing initial worker hole", noWorkerInitialHole),
      ("missing worker hole status", noWorkerNotFinal), ("missing worker pointer", noWorkerPointer),
      ("missing worker rewrite", noWorkerRewrite), ("wrong worker index", wrongWorkerIndex),
      ("wrong worker pointer index", wrongWorkerPointerIndex), ("wrong worker pointer list", wrongWorkerPointerList),
      ("missing worker result relation", noWorkerResult),
      ("missing worker state", noWorkerState), ("missing worker submap", noWorkerSubmap),
      ("missing worker freshness", noWorkerFresh), ("missing worker unchanged holes", noWorkerUnchanged),
      ("missing worker unfinished holes", noWorkerStill), ("missing worker block relation", noWorkerBlock),
      ("missing worker result premise", noWorkerReturnCondition), ("missing final worker hole", noWorkerFinalHole)] do
    if label != "hidden map" && label != "renamed map" && bad == info.value then
      throwError "mutation did not apply: {label}"
    let problems ← tmcHypothesisUniversalBinderProblems info.type bad
    if problems.isEmpty then throwError "invalid predicate accepted: {label}"
