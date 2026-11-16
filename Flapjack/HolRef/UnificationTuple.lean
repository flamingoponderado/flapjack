module

public meta import Lean
public meta import Lean.Util.CollectAxioms

public meta section

/-! Prospective elaborated checks for the tuple-valued unification relation.
These checks do not enable a HOL qualifier. Source correspondence, codec bodies,
witnesses, and attribute/export integration require separate validation. -/

namespace Flapjack
open Lean Meta

/-- Check the actual `WF_uR` signature, including the unreduced relation head.
The constant name and single type parameter are checked before definitional
equality so that wrappers and another well-founded relation cannot pass. -/
def unificationTupleSignatureProblems (type : Expr) : MetaM (Array String) := do
  forallTelescope type fun args result => do
    unless args.size == 1 do return #[s!"expected one type binder, got {args.size}"]
    let binder ← args[0]!.fvarId!.getDecl
    unless binder.binderInfo == .implicit do return #["atom type binder must be implicit"]
    unless ← isDefEq binder.type (mkSort (Level.succ Level.zero)) do
      return #["atom binder must be Type"]
    unless result.getAppFn.isConstOf ``WellFounded do
      return #["conclusion must be WellFounded"]
    let resultArgs := result.getAppArgs
    unless resultArgs.size == 2 do return #["WellFounded has an unexpected application shape"]
    let relation := resultArgs[1]!
    unless relation.getAppFn.isConstOf `Flapjack.HOL.Unification.uR do
      return #["well-founded relation must be the imported uR constant"]
    let relationArgs := relation.getAppArgs
    unless relationArgs.size == 1 && relationArgs[0]! == args[0]! do
      return #["uR must use exactly the quantified atom type"]
    let expected ← mkAppM ``WellFounded #[mkApp (mkConst `Flapjack.HOL.Unification.uR) args[0]!]
    unless ← isDefEq result expected do return #["well-foundedness has the wrong relation carrier"]
    return #[]

/-- Validate the actual type of `uR`, including the same canonical map and
term carrier in both triple arguments. This check does not inspect its body. -/
def unificationTupleRelationTypeProblems (type : Expr) : MetaM (Array String) := do
  forallTelescope type fun args result => do
    unless args.size == 3 do return #[s!"relation needs three binders, got {args.size}"]
    let atom ← args[0]!.fvarId!.getDecl
    unless atom.binderInfo == .implicit do return #["relation atom binder must be implicit"]
    unless ← isDefEq atom.type (mkSort (Level.succ Level.zero)) do
      return #["relation atom binder must be Type"]
    let term := mkApp (mkConst `Flapjack.HOL.Unification.Term) args[0]!
    let map := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) (mkConst ``Nat) term
    let pair (a b : Expr) := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) a b
    let triple := pair map (pair term term)
    for i in [1:3] do
      let binder ← args[i]!.fvarId!.getDecl
      unless binder.binderInfo == .default do return #["relation tuple binders must be explicit"]
      unless ← isDefEq binder.type triple do return #[s!"relation tuple {i} has the wrong carrier"]
    unless ← isDefEq result (mkSort Level.zero) do return #["relation must return Prop"]
    return #[]

private def unificationTupleExpectedBody (left right : Expr) : MetaM Expr := do
    let leftMap := mkProj ``Prod 0 left
    let rightMap := mkProj ``Prod 0 right
    let leftTail := mkProj ``Prod 1 left
    let rightTail := mkProj ``Prod 1 right
    let leftFirst := mkProj ``Prod 0 leftTail
    let leftSecond := mkProj ``Prod 1 leftTail
    let rightFirst := mkProj ``Prod 0 rightTail
    let rightSecond := mkProj ``Prod 1 rightTail
    let wf ← mkAppM `Flapjack.HOL.Unification.wfs #[leftMap]
    let sub ← mkAppM `Flapjack.HolFiniteMapExact.submap #[rightMap, leftMap]
    let child ← mkAppM `Flapjack.HOL.Unification.allVars #[leftMap, leftFirst, leftSecond]
    let parent ← mkAppM `Flapjack.HOL.Unification.allVars #[rightMap, rightFirst, rightSecond]
    let subset ← mkAppM `Set.Subset #[child, parent]
    let leftWalk ← mkAppM `Flapjack.HOL.Unification.walkstar #[leftMap, leftFirst]
    let rightWalk ← mkAppM `Flapjack.HOL.Unification.walkstar #[leftMap, rightFirst]
    let leftSize ← mkAppM `Flapjack.HOL.Unification.pairCount #[leftWalk]
    let rightSize ← mkAppM `Flapjack.HOL.Unification.pairCount #[rightWalk]
    let smaller := mkApp2 (mkConst ``Nat.lt) leftSize rightSize
    return mkApp2 (mkConst ``And) wf
      (mkApp2 (mkConst ``And) sub (mkApp2 (mkConst ``And) subset smaller))

/-- Check the elaborated body of `uR` against the four source conjuncts. The
source audit and imported-owner checks remain separate requirements. -/
def unificationTupleRelationBodyProblems (value : Expr) : MetaM (Array String) := do
  lambdaTelescope value fun args body => do
    unless args.size == 3 do return #["relation body needs atom and two tuple binders"]
    let expected ← unificationTupleExpectedBody args[1]! args[2]!
    unless ← isDefEq body expected do return #["relation body differs from the four source conjuncts"]
    return #[]

/-- Validate the elaborated `uR_def` equation and all six component binders.
The relation's body and imported attribute metadata are audited separately. -/
def unificationTupleEquationProblems (type : Expr) : MetaM (Array String) := do
  forallTelescope type fun args result => do
    unless args.size == 7 do return #[s!"relation equation needs seven binders, got {args.size}"]
    let atom ← args[0]!.fvarId!.getDecl
    unless atom.binderInfo == .implicit do return #["equation atom binder must be implicit"]
    unless ← isDefEq atom.type (mkSort (Level.succ Level.zero)) do
      return #["equation atom binder must be Type"]
    let term := mkApp (mkConst `Flapjack.HOL.Unification.Term) args[0]!
    let map := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) (mkConst ``Nat) term
    for i in [1:7] do
      let binder ← args[i]!.fvarId!.getDecl
      unless binder.binderInfo == .default do return #["equation component binders must be explicit"]
      unless ← isDefEq binder.type (if i == 1 || i == 4 then map else term) do
        return #[s!"equation component {i} has the wrong carrier"]
    unless result.getAppFn.isConstOf ``Iff do return #["equation must conclude an iff"]
    let iffArgs := result.getAppArgs
    unless iffArgs.size == 2 do return #["equation iff has the wrong shape"]
    let lhs := iffArgs[0]!
    unless lhs.getAppFn.isConstOf `Flapjack.HOL.Unification.uR do
      return #["equation lhs must apply the imported uR directly"]
    let leftTail ← mkAppM ``Prod.mk #[args[2]!, args[3]!]
    let left ← mkAppM ``Prod.mk #[args[1]!, leftTail]
    let rightTail ← mkAppM ``Prod.mk #[args[5]!, args[6]!]
    let right ← mkAppM ``Prod.mk #[args[4]!, rightTail]
    let expectedRelation ← mkAppM `Flapjack.HOL.Unification.uR #[left, right]
    unless ← isDefEq lhs expectedRelation do return #["equation lhs has wrong tuple components"]
    let rhs := iffArgs[1]!
    let mut spine := rhs
    for _ in [:3] do
      unless spine.getAppFn.isConstOf ``And && spine.getAppArgs.size == 2 do
        return #["equation rhs must have the direct four-conjunct source shape"]
      spine := spine.getAppArgs[1]!
    let expected ← unificationTupleExpectedBody left right
    unless ← isDefEq rhs expected do
      return #["equation rhs differs from the imported relation body"]
    return #[]

/-- Check a tuple codec's elaborated type and body against the exact map codec
and unchanged term projections. This prospective guard is not a source audit. -/
def unificationTupleCodecProblems (type value : Expr) (toBroad : Bool) : MetaM (Array String) := do
  let pair (a b : Expr) := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) a b
  let carriers (atom : Expr) := Id.run do
    let term := mkApp (mkConst `Flapjack.HOL.Unification.Term) atom
    let map := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) (mkConst ``Nat) term
    let broad := mkApp2 (mkConst `Flapjack.FiniteMapBroad) (mkConst ``Nat) term
    return (pair map (pair term term), pair broad (pair term term))
  let typeProblems ← forallTelescope type fun args result => do
    unless args.size == 2 do return #["codec needs exactly atom and tuple binders"]
    let atom ← args[0]!.fvarId!.getDecl
    let tuple ← args[1]!.fvarId!.getDecl
    unless atom.binderInfo == .implicit && tuple.binderInfo == .default do
      return #["codec binders have the wrong visibility"]
    unless ← isDefEq atom.type (mkSort (Level.succ Level.zero)) do
      return #["codec atom binder must be Type"]
    let (canonical, broad) := carriers args[0]!
    unless ← isDefEq tuple.type (if toBroad then canonical else broad) do
      return #["codec input has the wrong tuple carrier"]
    unless ← isDefEq result (if toBroad then broad else canonical) do
      return #["codec output has the wrong tuple carrier"]
    return #[]
  let bodyProblems ← lambdaTelescope value fun args body => do
    unless args.size == 2 do return #["codec body needs exactly two binders"]
    let atom ← args[0]!.fvarId!.getDecl
    let tuple ← args[1]!.fvarId!.getDecl
    unless atom.binderInfo == .implicit && tuple.binderInfo == .default do
      return #["codec body binders have the wrong visibility"]
    let (canonical, broad) := carriers args[0]!
    unless ← isDefEq tuple.type (if toBroad then canonical else broad) do
      return #["codec body input has the wrong carrier"]
    let input := args[1]!
    let mapProjection := mkProj ``Prod 0 input
    let tail := mkProj ``Prod 1 input
    let mapped ← mkAppM (if toBroad then `Flapjack.FiniteMapBroad.toBroad
      else `Flapjack.FiniteMapBroad.ofBroad) #[mapProjection]
    let terms ← mkAppM ``Prod.mk #[mkProj ``Prod 0 tail, mkProj ``Prod 1 tail]
    let expected ← mkAppM ``Prod.mk #[mapped, terms]
    unless ← isDefEq body expected do
      return #["codec body must preserve the map codec and both ordered term slots"]
    return #[]
  return typeProblems ++ bodyProblems

/-- Check the unconditional type of either tuple round-trip witness. The codec
bodies and proof axiom closure require separate checks. -/
def unificationTupleWitnessTypeProblems (type : Expr) (forward : Bool) : MetaM (Array String) := do
  forallTelescope type fun args result => do
    unless args.size == 2 do return #["witness needs exactly atom and tuple binders"]
    let atom ← args[0]!.fvarId!.getDecl
    let tuple ← args[1]!.fvarId!.getDecl
    unless atom.binderInfo == .implicit && tuple.binderInfo == .default do
      return #["witness binders have the wrong visibility"]
    unless ← isDefEq atom.type (mkSort (Level.succ Level.zero)) do
      return #["witness atom binder must be Type"]
    let term := mkApp (mkConst `Flapjack.HOL.Unification.Term) args[0]!
    let map := mkApp2 (mkConst (if forward then `Flapjack.HolFiniteMapExact
      else `Flapjack.FiniteMapBroad)) (mkConst ``Nat) term
    let pair (a b : Expr) := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) a b
    unless ← isDefEq tuple.type (pair map (pair term term)) do
      return #["witness input has the wrong tuple carrier"]
    unless result.getAppFn.isConstOf ``Eq do return #["witness must conclude an equality"]
    let equality := result.getAppArgs
    unless equality.size == 3 && equality[2]! == args[1]! do
      return #["witness equality must return the original tuple"]
    let outer := equality[1]!
    let outerName := if forward then `Flapjack.HOL.Unification.uRTupleOfBroad
      else `Flapjack.HOL.Unification.uRTupleToBroad
    let innerName := if forward then `Flapjack.HOL.Unification.uRTupleToBroad
      else `Flapjack.HOL.Unification.uRTupleOfBroad
    unless outer.getAppFn.isConstOf outerName do return #["witness must apply the outer codec directly"]
    let outerArgs := outer.getAppArgs
    unless outerArgs.size == 2 && outerArgs[0]! == args[0]! do
      return #["outer codec must use the same atom type"]
    let inner := outerArgs[1]!
    unless inner.getAppFn.isConstOf innerName do return #["witness must apply the inner codec directly"]
    let innerArgs := inner.getAppArgs
    unless innerArgs.size == 2 && innerArgs[0]! == args[0]! && innerArgs[1]! == args[1]! do
      return #["inner codec must use the same atom type and tuple"]
    let first ← mkAppM (if forward then `Flapjack.HOL.Unification.uRTupleToBroad
      else `Flapjack.HOL.Unification.uRTupleOfBroad) #[args[1]!]
    let roundtrip ← mkAppM (if forward then `Flapjack.HOL.Unification.uRTupleOfBroad
      else `Flapjack.HOL.Unification.uRTupleToBroad) #[first]
    let expected ← mkEq roundtrip args[1]!
    unless ← isDefEq result expected do return #["witness must state the complete roundtrip"]
    return #[]

/-- Check one imported `uREq` map witness against the canonical substitution
codec theorem, with no extra binder or premise. -/
def unificationEquationMapWitnessTypeProblems (type : Expr) : MetaM (Array String) := do
  forallTelescope type fun args result => do
    unless args.size == 3 do return #["equation map witness needs exactly three binders"]
    let atom ← args[0]!.fvarId!.getDecl
    let mapBinder ← args[1]!.fvarId!.getDecl
    let key ← args[2]!.fvarId!.getDecl
    unless atom.binderInfo == .implicit && mapBinder.binderInfo == .default &&
        key.binderInfo == .default do return #["equation map witness has wrong binder visibility"]
    unless ← isDefEq atom.type (mkSort (Level.succ Level.zero)) do
      return #["equation map witness atom binder must be Type"]
    let term := mkApp (mkConst `Flapjack.HOL.Unification.Term) args[0]!
    let map := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) (mkConst ``Nat) term
    unless ← isDefEq mapBinder.type map do return #["equation map witness has the wrong map carrier"]
    unless ← isDefEq key.type (mkConst ``Nat) do return #["equation map witness has the wrong key carrier"]
    let broad ← mkAppM `Flapjack.FiniteMapBroad.toBroad #[args[1]!]
    let restored ← mkAppM `Flapjack.FiniteMapBroad.ofBroad #[broad]
    let restoredLookup ← mkAppM `Flapjack.HolFiniteMapExact.lookup #[restored]
    let originalLookup ← mkAppM `Flapjack.HolFiniteMapExact.lookup #[args[1]!]
    let lookupEq ← mkEq (mkApp restoredLookup args[2]!) (mkApp originalLookup args[2]!)
    let restoredSupport ← mkAppM `Flapjack.HolFiniteMapExact.finiteSupport #[restored]
    let originalSupport ← mkAppM `Flapjack.HolFiniteMapExact.finiteSupport #[args[1]!]
    let supportEq ← mkEq restoredSupport originalSupport
    let mapEq ← mkEq restored args[1]!
    let expected := mkApp2 (mkConst ``And) lookupEq (mkApp2 (mkConst ``And) supportEq mapEq)
    unless ← withTransparency .reducible (isDefEq result expected) do
      return #["equation map witness must state the canonical codec roundtrip"]
    return #[]

/-- Resolve the exact owners and reject axioms in the tuple codec and witness
bundle. Relation bodies and attribute metadata are checked separately. -/
def unificationTupleOwnerAndAxiomProblems : CoreM (Array String) := do
  let env ← getEnv
  let targetModule := `Flapjack.HOL.Unification.UnifDef.WellFounded
  let relationModule := `Flapjack.HOL.Unification.UnifDef
  let target := `Flapjack.HOL.Unification.uRWellFounded
  let relation := `Flapjack.HOL.Unification.uR
  let equation := `Flapjack.HOL.Unification.uREq
  let codecs := #[`Flapjack.HOL.Unification.uRTupleToBroad,
    `Flapjack.HOL.Unification.uRTupleOfBroad]
  let witnesses := #[`Flapjack.HOL.Unification.holFmapAsFiniteSupportTupleWitness_uRWellFounded,
    `Flapjack.HOL.Unification.holFmapAsFiniteSupportTupleWitness_uRWellFounded_reverse]
  let equationWitnesses := #[`Flapjack.HOL.Unification.holFmapAsFiniteSupportParamWitness_uREq_sx,
    `Flapjack.HOL.Unification.holFmapAsFiniteSupportParamWitness_uREq_s]
  let definingModule (name : Name) :=
    match env.getModuleIdxFor? name with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  let mut errors : Array String := #[]
  for name in #[target, relation, equation] ++ codecs ++ witnesses ++ equationWitnesses do
    let expectedModule := if name == relation || name == equation || equationWitnesses.contains name then
      relationModule else targetModule
    unless definingModule name == expectedModule do
      errors := errors.push s!"{name} has the wrong defining module"
    let info := env.checked.get.find? name
    let isDefinition := name == relation || codecs.contains name
    match info with
    | some (.defnInfo d) =>
      unless isDefinition && d.safety == .safe && d.levelParams.isEmpty do
        errors := errors.push s!"{name} must have the expected safe definition kind"
    | some (.thmInfo t) =>
      unless !isDefinition && t.levelParams.isEmpty do
        errors := errors.push s!"{name} must have the expected theorem kind"
    | _ => errors := errors.push s!"{name} is missing or has the wrong declaration kind"
  for name in codecs ++ witnesses ++ equationWitnesses do
    if (env.checked.get.find? name).isSome then
      let axioms ← collectAxioms name
      unless axioms.isEmpty do errors := errors.push s!"{name} depends on axioms {axioms}"
  for name in #[target, equation] do
    if (env.checked.get.find? name).isSome then
      let axioms ← collectAxioms name
      let allowed := #[`propext, `Classical.choice, `Quot.sound]
      for axiomName in axioms do
        unless allowed.contains axiomName do
          errors := errors.push s!"{name} depends on unexpected axiom {axiomName}"
  let dependencies : Array (Name × Name) := #[
    (`Flapjack.HolFiniteMapExact, `Flapjack.FiniteMap.Exact),
    (`Flapjack.FiniteMapBroad, `Flapjack.FiniteMap.BroadCodec),
    (`Flapjack.FiniteMapBroad.toBroad, `Flapjack.FiniteMap.BroadCodec),
    (`Flapjack.FiniteMapBroad.ofBroad, `Flapjack.FiniteMap.BroadCodec),
    (`Flapjack.HolFiniteMapExact.submap, `Flapjack.FiniteMap.SubmapExact),
    (`Flapjack.HOL.Unification.Term, `Flapjack.HOL.Unification.Term),
    (`Flapjack.HOL.Unification.pairCount, `Flapjack.HOL.Unification.Term),
    (`Flapjack.HOL.Unification.wfs, `Flapjack.HOL.Unification.Subst),
    (`Flapjack.HOL.Unification.allVars, relationModule),
    (`Flapjack.HOL.Unification.walkstar, `Flapjack.HOL.Unification.Walkstar),
    (`Flapjack.HOL.Unification.holFmapAsFiniteSupportParamWitness_vR_subst,
      `Flapjack.HOL.Unification.Subst)]
  for (name, owner) in dependencies do
    if (env.find? name).isNone || definingModule name != owner then
      errors := errors.push s!"{name} is missing or has the wrong defining module"
  return errors

/-- Run all prospective elaborated checks over the exact resolved declaration
bundle. HOL-reference metadata and source-level checks are still separate, and
this function does not enable a qualifier. -/
def unificationTupleElaboratedProblems : MetaM (Array String) := do
  let ownerProblems ← unificationTupleOwnerAndAxiomProblems
  unless ownerProblems.isEmpty do return ownerProblems
  let target ← getConstInfo `Flapjack.HOL.Unification.uRWellFounded
  let .defnInfo relation ← getConstInfo `Flapjack.HOL.Unification.uR
    | return #["uR is not a definition"]
  let equation ← getConstInfo `Flapjack.HOL.Unification.uREq
  let mut problems ← unificationTupleSignatureProblems target.type
  problems := problems ++ (← unificationTupleRelationTypeProblems relation.type)
  if problems.isEmpty then
    problems := problems ++ (← unificationTupleRelationBodyProblems relation.value)
  problems := problems ++ (← unificationTupleEquationProblems equation.type)
  for (name, direction) in #[(
      `Flapjack.HOL.Unification.uRTupleToBroad, true),
      (`Flapjack.HOL.Unification.uRTupleOfBroad, false)] do
    let .defnInfo codec ← getConstInfo name | return problems.push s!"{name} is not a definition"
    problems := problems ++ (← unificationTupleCodecProblems codec.type codec.value direction)
  for (name, direction) in #[(
      `Flapjack.HOL.Unification.holFmapAsFiniteSupportTupleWitness_uRWellFounded, true),
      (`Flapjack.HOL.Unification.holFmapAsFiniteSupportTupleWitness_uRWellFounded_reverse, false)] do
    let witness ← getConstInfo name
    problems := problems ++ (← unificationTupleWitnessTypeProblems witness.type direction)
  for name in #[`Flapjack.HOL.Unification.holFmapAsFiniteSupportParamWitness_uREq_sx,
      `Flapjack.HOL.Unification.holFmapAsFiniteSupportParamWitness_uREq_s] do
    let witness ← getConstInfo name
    problems := problems ++ (← unificationEquationMapWitnessTypeProblems witness.type)
  return problems

end Flapjack
