import Flapjack.HOL.Unification.UnifDef.WellFounded
import Flapjack.HolRef.UnificationTuple

/-! Elaborated negative fixtures for the prospective unification tuple guard.
They do not authorize a HOL qualifier. -/

open Lean Meta Flapjack Flapjack.HOL.Unification

private theorem validExtraPremise {α : Type} (_ : True) : WellFounded (@uR α) :=
  uRWellFounded

private def wrongUnifRelation {α : Type}
    (_ _ : HolFiniteMapExact Nat (Term α) × Term α × Term α) : Prop := False

private theorem validWrongRelation {α : Type} : WellFounded (@wrongUnifRelation α) := by
  constructor
  intro p
  exact Acc.intro p (by intro q edge; cases edge)

private theorem validOneState {α : Type}
    (p : HolFiniteMapExact Nat (Term α) × Term α × Term α) : Acc uR p :=
  uRWellFounded.apply p

private def wrongMapRelation {α : Type}
    (_ _ : (Nat → Option (Term α)) × Term α × Term α) : Prop := False

private def wrongPositionRelation {α : Type}
    (_ _ : Term α × HolFiniteMapExact Nat (Term α) × Term α) : Prop := False

private def extraTypeRelation {α β : Type}
    (_ : HolFiniteMapExact Nat (Term α) × Term α × Term α)
    (_ : HolFiniteMapExact Nat (Term β) × Term β × Term β) : Prop := False

private def extraTupleSlotRelation {α : Type}
    (_ _ : HolFiniteMapExact Nat (Term α) × Term α × Term α × Nat) : Prop := False

private def reversedSubmapRelation {α : Type}
    (left right : HolFiniteMapExact Nat (Term α) × Term α × Term α) : Prop :=
  wfs left.1 ∧ left.1.submap right.1 ∧
  Set.Subset (allVars left.1 left.2.1 left.2.2) (allVars right.1 right.2.1 right.2.2) ∧
  pairCount (walkstar left.1 left.2.1) < pairCount (walkstar left.1 right.2.1)

private def wrongWalkMapRelation {α : Type}
    (left right : HolFiniteMapExact Nat (Term α) × Term α × Term α) : Prop :=
  wfs left.1 ∧ right.1.submap left.1 ∧
  Set.Subset (allVars left.1 left.2.1 left.2.2) (allVars right.1 right.2.1 right.2.2) ∧
  pairCount (walkstar left.1 left.2.1) < pairCount (walkstar right.1 right.2.1)

private def swappedTupleCodec {α : Type}
    (p : HolFiniteMapExact Nat (Term α) × Term α × Term α) :
    FiniteMapBroad Nat (Term α) × Term α × Term α :=
  (FiniteMapBroad.toBroad p.1, p.2.2, p.2.1)

private def ignoredTupleCodec {α : Type}
    (p : HolFiniteMapExact Nat (Term α) × Term α × Term α) :
    FiniteMapBroad Nat (Term α) × Term α × Term α :=
  (FiniteMapBroad.toBroad p.1, p.2.1, p.2.1)

private theorem selfEqualityWitness {α : Type}
    (p : HolFiniteMapExact Nat (Term α) × Term α × Term α) : p = p := rfl

private theorem extraPremiseWitness {α : Type}
    (p : HolFiniteMapExact Nat (Term α) × Term α × Term α) (_ : True) :
    uRTupleOfBroad (uRTupleToBroad p) = p := holFmapAsFiniteSupportTupleWitness_uRWellFounded p

set_option linter.unusedVariables false in
private theorem wrongRelationEquation {α : Type}
    (sx : HolFiniteMapExact Nat (Term α)) (c1 c2 : Term α)
    (s : HolFiniteMapExact Nat (Term α)) (t1 t2 : Term α) : True ↔ True := Iff.rfl

private theorem extraPremiseEquation {α : Type}
    (sx : HolFiniteMapExact Nat (Term α)) (c1 c2 : Term α)
    (s : HolFiniteMapExact Nat (Term α)) (t1 t2 : Term α) (_ : True) :
    uR (sx, c1, c2) (s, t1, t2) ↔
    wfs sx ∧ s.submap sx ∧ Set.Subset (allVars sx c1 c2) (allVars s t1 t2) ∧
      pairCount (walkstar sx c1) < pairCount (walkstar sx t1) := uREq sx c1 c2 s t1 t2

run_meta do
  let ownerProblems ← unificationTupleOwnerAndAxiomProblems
  unless ownerProblems.isEmpty do throwError "valid owners rejected: {ownerProblems}"
  let good ← getConstInfo ``uRWellFounded
  let goodProblems ← unificationTupleSignatureProblems good.type
  unless goodProblems.isEmpty do throwError "valid WF signature rejected: {goodProblems}"
  for bad in [``validExtraPremise, ``validWrongRelation, ``validOneState] do
    let info ← getConstInfo bad
    let problems ← unificationTupleSignatureProblems info.type
    if problems.isEmpty then throwError "invalid WF signature {bad} accepted"
  let relation ← getConstInfo ``uR
  let relationProblems ← unificationTupleRelationTypeProblems relation.type
  unless relationProblems.isEmpty do throwError "valid relation type rejected: {relationProblems}"
  let .defnInfo relationDef := relation | throwError "missing relation definition"
  let bodyProblems ← unificationTupleRelationBodyProblems relationDef.value
  unless bodyProblems.isEmpty do throwError "valid relation body rejected: {bodyProblems}"
  for bad in [``wrongUnifRelation, ``reversedSubmapRelation, ``wrongWalkMapRelation] do
    let .defnInfo wrongBody ← getConstInfo bad | throwError "missing relation fixture {bad}"
    let wrongProblems ← unificationTupleRelationBodyProblems wrongBody.value
    if wrongProblems.isEmpty then throwError "invalid relation body {bad} accepted"
  let equation ← getConstInfo ``uREq
  let equationProblems ← unificationTupleEquationProblems equation.type
  unless equationProblems.isEmpty do throwError "valid relation equation rejected: {equationProblems}"
  for bad in [``wrongRelationEquation, ``extraPremiseEquation] do
    let info ← getConstInfo bad
    let problems ← unificationTupleEquationProblems info.type
    if problems.isEmpty then throwError "invalid relation equation {bad} accepted"
  for bad in [``wrongMapRelation, ``wrongPositionRelation, ``extraTypeRelation,
      ``extraTupleSlotRelation] do
    let info ← getConstInfo bad
    let problems ← unificationTupleRelationTypeProblems info.type
    if problems.isEmpty then throwError "invalid relation carrier {bad} accepted"
  for (name, direction) in [(``uRTupleToBroad, true), (``uRTupleOfBroad, false)] do
    let .defnInfo info ← getConstInfo name | throwError "missing codec {name}"
    let problems ← unificationTupleCodecProblems info.type info.value direction
    unless problems.isEmpty do throwError "valid codec {name} rejected: {problems}"
  for name in [``swappedTupleCodec, ``ignoredTupleCodec] do
    let .defnInfo info ← getConstInfo name | throwError "missing codec fixture {name}"
    let problems ← unificationTupleCodecProblems info.type info.value true
    if problems.isEmpty then throwError "invalid codec {name} accepted"
  for (name, direction) in [(``holFmapAsFiniteSupportTupleWitness_uRWellFounded, true),
      (``holFmapAsFiniteSupportTupleWitness_uRWellFounded_reverse, false)] do
    let info ← getConstInfo name
    let problems ← unificationTupleWitnessTypeProblems info.type direction
    unless problems.isEmpty do throwError "valid witness {name} rejected: {problems}"
  for name in [``selfEqualityWitness, ``extraPremiseWitness] do
    let info ← getConstInfo name
    let problems ← unificationTupleWitnessTypeProblems info.type true
    if problems.isEmpty then throwError "invalid witness {name} accepted"
