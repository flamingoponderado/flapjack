module

import all Flapjack.Compiler.Backend.BviTmc.Proofs.CallBlockCorrectness
meta import Flapjack.HolRef.TmcUniversalBinder

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
