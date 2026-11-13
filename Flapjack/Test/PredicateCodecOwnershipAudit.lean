import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvalSim
import Flapjack.HolRef.PredicateCodec

/-! Owner and axiom tests for the prospective codec guard. These checks are
preparatory and do not authorize a HOL qualifier. -/

open Lean Elab Command Flapjack Flapjack.Compiler.Backend

private noncomputable def axiomCarrier : Nat := Classical.choice ⟨0⟩

private abbrev AuditCode := Nat → Option (Nat × ClosLang.Exp)
private abbrev AuditSupport (lookup : AuditCode) :=
  ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys
private abbrev AuditTail (C₁ C₂ : Type) := ClosSem.CompileOracle C₁ →
  ClosSem.Compiler C₁ → List ClosLang.Exp → Spt (Nat × Bvl.Exp) →
  BvlSem.CompileOracle C₂ → BvlSem.Compiler C₂ → Nat → Prop

set_option linter.unusedVariables false in
private abbrev wrongTail (C₁ C₂ : Type) := ClosSem.CompileOracle C₁ →
  ClosSem.Compiler C₁ → List ClosLang.Exp → Spt (Nat × Bvl.Exp) →
  BvlSem.CompileOracle C₁ → BvlSem.Compiler C₁ → Nat → Prop
private abbrev wrongRaw := Nat → Option Nat
private abbrev vacuousSupport (_lookup : AuditCode) := True
private abbrev implicitSupport (lookup : AuditCode) :=
  ∃ keys : List Nat, ∀ {key : Nat}, lookup key ≠ none → key ∈ keys
private abbrev implicitPremise (lookup : AuditCode) :=
  ∃ keys : List Nat, ∀ key, ∀ {_h : lookup key ≠ none}, key ∈ keys

private def validLookup (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : AuditCode :=
  code.lookup

private def emptyLookup (_code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : AuditCode :=
  fun _ => none

private def implicitLookup {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} : AuditCode :=
  code.lookup

private def validReconstruction (lookup : AuditCode) (support : AuditSupport lookup) :
    HolFiniteMapExact Nat (Nat × ClosLang.Exp) := ⟨lookup, support⟩

private def emptyReconstruction (_lookup : AuditCode) (_support : AuditSupport _lookup) :
    HolFiniteMapExact Nat (Nat × ClosLang.Exp) := HolFiniteMapExact.empty

private def emptyAuditCode : AuditCode := fun _ => none
private theorem emptyAuditSupport : AuditSupport emptyAuditCode := by
  exact ⟨[], by simp [emptyAuditCode]⟩

private def discardCanonicalInput {C₁ C₂ : Type}
    (rel : HolFiniteMapExact Nat (Nat × ClosLang.Exp) → AuditTail C₁ C₂)
    (_lookup : AuditCode) (_support : AuditSupport _lookup) : AuditTail C₁ C₂ :=
  rel HolFiniteMapExact.empty

private def discardRawInput {C₁ C₂ : Type}
    (rel : (lookup : AuditCode) → AuditSupport lookup → AuditTail C₁ C₂)
    (_code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : AuditTail C₁ C₂ :=
  rel emptyAuditCode emptyAuditSupport

private def cloneOfBroad (lookup : AuditCode) (support : AuditSupport lookup) :
    HolFiniteMapExact Nat (Nat × ClosLang.Exp) := ⟨lookup, support⟩
private def clonedCanonicalPredicate {C₁ C₂ : Type}
    (rel : HolFiniteMapExact Nat (Nat × ClosLang.Exp) → AuditTail C₁ C₂)
    (lookup : AuditCode) (support : AuditSupport lookup) : AuditTail C₁ C₂ :=
  rel (cloneOfBroad lookup support)

private def cloneToBroad (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : AuditCode :=
  code.lookup
private def clonedRawPredicate {C₁ C₂ : Type}
    (rel : (lookup : AuditCode) → AuditSupport lookup → AuditTail C₁ C₂)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : AuditTail C₁ C₂ :=
  rel (cloneToBroad code) code.finiteSupport

private def auditToBroad (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : AuditCode :=
  code.lookup
private theorem choiceSupport (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    AuditSupport (auditToBroad code) := Classical.choice ⟨code.finiteSupport⟩
private noncomputable def choicePredicate {C₁ C₂ : Type}
    (rel : (lookup : AuditCode) → AuditSupport lookup → AuditTail C₁ C₂)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : AuditTail C₁ C₂ :=
  rel (auditToBroad code) (choiceSupport code)

private def replaceAuditAliases (names : Array Name) (expression : Expr) : Expr :=
  expression.replace fun e =>
    if e.isConstOf ``AuditTail then some (mkConst names[0]!)
    else if e.isConstOf ``AuditCode then some (mkConst names[1]!)
    else if e.isConstOf ``AuditSupport then some (mkConst names[2]!)
    else if e.isConstOf ``auditToBroad then some (mkConst names[3]!)
    else none

-- These deliberately trivial declarations test resolution only. Their
-- bodies are not acceptable codec or witness content for the qualifier.
namespace Flapjack.Test.PredicateCodecCurrent
private abbrev SimulationTail := Nat
private abbrev RawCode := Nat
private abbrev RawCodeSupport := Nat
private def toBroad : Nat := 0
private def ofBroad : Nat := 0
private def toBroadPredicate : Nat := 0
private def fromBroadPredicate : Nat := 0
theorem simulationPredicateRoundtrips : True := trivial
end Flapjack.Test.PredicateCodecCurrent

namespace Flapjack.Test.PredicateCodecWrongKind
private def SimulationTail : Nat := 0
private abbrev RawCode := Nat
private abbrev RawCodeSupport := Nat
private def toBroad : Nat := 0
private def ofBroad : Nat := 0
private def toBroadPredicate : Nat := 0
private def fromBroadPredicate : Nat := 0
theorem simulationPredicateRoundtrips : True := trivial
end Flapjack.Test.PredicateCodecWrongKind

run_cmd do
  let env ← getEnv
  let names ← match resolvePredicateCodec env with
    | .ok names => pure names
    | .error message => throwError "current codec did not resolve: {message}"
  unless names.size == 8 do throwError "unexpected codec declaration count"
  let exportedEnv := env.setExporting true
  let .ok exportedNames := resolvePredicateCodec exportedEnv
    | throwError "codec resolver rejected the exported view"
  unless exportedNames == names do
    throwError "exported view resolved different codec declarations"
  let some (.thmInfo _) := exportedEnv.checked.get.find? names[7]!
    | throwError "roundtrip witness is not a checked theorem in exported view"
  let exportedAxioms ← liftTermElabM <| withEnv exportedEnv do
    predicateCodecAxiomProblems exportedNames
  unless exportedAxioms.isEmpty do
    throwError "exported codec view changed its axiom closure: {exportedAxioms}"
  let competing := env.constants.toList.filter fun (name, _) =>
    privateToUserName? name == some `Flapjack.Compiler.Backend.ClosToBvl.toBroad &&
      predicateCodecDefiningModule env name != `Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvalSim
  if competing.isEmpty then throwError "missing imported competing private helper fixture"
  if (resolvePredicateCodecInModule env `Flapjack.HolRef
      `Flapjack.Compiler.Backend.ClosToBvl).isOk then
    throwError "codec was resolved from the wrong owner"
  let problems ← liftCoreM (predicateCodecAxiomProblems names)
  unless problems.isEmpty do throwError "current codec has axiom problems: {problems}"
  let combined ← liftCoreM predicateCodecOwnerAndAxiomProblems
  unless combined.isEmpty do throwError "combined owner and axiom check failed: {combined}"
  let elaborated ← liftTermElabM predicateCodecElaboratedProblems
  unless elaborated.isEmpty do throwError "complete codec audit failed: {elaborated}"
  for i in #[0, 1, 2] do
    let some (.defnInfo info) := env.find? names[i]! | throwError "missing codec alias {i}"
    let errors ← liftTermElabM (predicateCodecAliasBodyProblems names i info.type info.value)
    unless errors.isEmpty do throwError "valid codec alias {i} rejected: {errors}"
  for (name, i) in [(``AuditTail, 0), (``AuditCode, 1), (``AuditSupport, 2)] do
    let some (.defnInfo info) := env.find? name | throwError "missing valid alias fixture {name}"
    let errors ← liftTermElabM (predicateCodecAliasBodyProblems names i info.type info.value)
    unless errors.isEmpty do throwError "valid alias fixture {name} rejected: {errors}"
  for (name, i) in [(``wrongTail, 0), (``wrongRaw, 1), (``vacuousSupport, 2),
      (``implicitSupport, 2), (``implicitPremise, 2)] do
    let some (.defnInfo info) := env.find? name | throwError "missing invalid alias fixture {name}"
    let errors ← liftTermElabM (predicateCodecAliasBodyProblems names i info.type info.value)
    if errors.isEmpty then throwError "invalid alias fixture {name} was accepted"
  for i in #[3, 4] do
    let some (.defnInfo info) := env.find? names[i]! | throwError "missing map codec {i}"
    let errors ← liftTermElabM (predicateCodecMapBodyProblems names i info.type info.value)
    unless errors.isEmpty do throwError "valid map codec {i} rejected: {errors}"
  for (name, i) in [(``validLookup, 3), (``validReconstruction, 4)] do
    let some (.defnInfo info) := env.find? name | throwError "missing valid fixture {name}"
    let errors ← liftTermElabM (predicateCodecMapBodyProblems names i info.type info.value)
    unless errors.isEmpty do throwError "valid codec fixture {name} rejected: {errors}"
  for (name, i) in [(``emptyLookup, 3), (``emptyReconstruction, 4)] do
    let some (.defnInfo info) := env.find? name | throwError "missing vacuous fixture {name}"
    let errors ← liftTermElabM (predicateCodecMapBodyProblems names i info.type info.value)
    if errors.isEmpty then throwError "vacuous codec fixture {name} was accepted"
  let some (.defnInfo implicitInfo) := env.find? ``implicitLookup | throwError "missing implicit fixture"
  let implicitErrors ← liftTermElabM (predicateCodecMapBodyProblems names 3 implicitInfo.type implicitInfo.value)
  if implicitErrors.isEmpty then throwError "implicit map codec input was accepted"
  let invalidIndex ← liftTermElabM (predicateCodecMapBodyProblems names 5 implicitInfo.type implicitInfo.value)
  if invalidIndex.isEmpty then throwError "unrecognized map codec index was accepted"
  for i in #[5, 6] do
    let some (.defnInfo info) := env.find? names[i]! | throwError "missing predicate codec {i}"
    let errors ← liftTermElabM (predicateCodecTranslatorBodyProblems names i info.type info.value)
    unless errors.isEmpty do throwError "valid predicate codec {i} rejected: {errors}"
  for (name, i, expectedError) in [(``discardCanonicalInput, 5, "predicate codec has the wrong canonical application spine"),
      (``discardRawInput, 6, "predicate codec has the wrong raw application spine"),
      (``clonedCanonicalPredicate, 5, "predicate codec has the wrong canonical application spine"),
      (``clonedRawPredicate, 6, "predicate codec has the wrong raw application spine")] do
    let some (.defnInfo info) := env.find? name | throwError "missing predicate fixture {name}"
    let (consistent, errors) ← liftTermElabM do
      let type := replaceAuditAliases names info.type
      let value := replaceAuditAliases names info.value
      let consistent ← Lean.Meta.isDefEq (← Lean.Meta.inferType value) type
      return (consistent, ← predicateCodecTranslatorBodyProblems names i type value)
    unless consistent do throwError "predicate fixture {name} changed type after alias replacement"
    unless errors.contains expectedError do throwError "predicate fixture {name} was not rejected by its body: {errors}"
  let some (.defnInfo choiceInfo) := env.find? ``choicePredicate | throwError "missing choice fixture"
  let choiceBodyErrors ← liftTermElabM (predicateCodecTranslatorBodyProblems names 6
    (replaceAuditAliases names choiceInfo.type) (replaceAuditAliases names choiceInfo.value))
  unless choiceBodyErrors.isEmpty do throwError "choice fixture has an unexpected body problem: {choiceBodyErrors}"
  let choiceAxioms ← liftCoreM (predicateCodecAxiomProblems (names.set! 6 ``choicePredicate))
  if choiceAxioms.isEmpty then throwError "axiom-dependent support proof was accepted"
  let some witness := env.find? names[7]! | throwError "missing witness"
  let goodType ← liftTermElabM (predicateCodecWitnessTypeProblems names witness.type)
  unless goodType.isEmpty do throwError "valid witness type rejected: {goodType}"
  let oneSided := witness.type.replace fun e =>
    match e with
    | .app (.app (.const ``And []) first) _ => some first
    | _ => none
  let selfEqual := witness.type.replace fun e =>
    match e with
    | .app (.app (.app eq ty) _) right =>
      if eq.isConstOf ``Eq then some (mkApp3 eq ty right right) else none
    | _ => none
  let reversed := witness.type.replace fun e =>
    match e with
    | .app (.app (.app eq ty) left) right =>
      if eq.isConstOf ``Eq then some (mkApp3 eq ty right left) else none
    | _ => none
  let implicitPredicateDomain := witness.type.replace fun e =>
    match e with
    | .forallE `rel (.forallE n domain body _) result binderInfo =>
      some (.forallE `rel (.forallE n domain body BinderInfo.implicit) result binderInfo)
    | _ => none
  let implicitSupportDomain := witness.type.replace fun e =>
    match e with
    | .forallE `rel (.forallE n domain (.forallE s support tail _) info) result binderInfo =>
      some (.forallE `rel (.forallE n domain (.forallE s support tail BinderInfo.implicit) info)
        result binderInfo)
    | _ => none
  let extraBinder := Expr.forallE `extra (mkSort Level.zero) witness.type BinderInfo.implicit
  for (label, bad) in [("one-sided", oneSided), ("self-equality", selfEqual),
      ("reversed equality", reversed), ("implicit predicate domain", implicitPredicateDomain),
      ("implicit support domain", implicitSupportDomain), ("extra binder", extraBinder)] do
    let errors ← liftTermElabM (predicateCodecWitnessTypeProblems names bad)
    if errors.isEmpty then throwError "invalid {label} witness type was accepted"
  let noNames ← liftTermElabM (predicateCodecWitnessTypeProblems #[] witness.type)
  if noNames.isEmpty then throwError "witness type was accepted without a codec bundle"
  let duplicateNames ← liftTermElabM (predicateCodecWitnessTypeProblems (names.set! 7 names[0]!) witness.type)
  if duplicateNames.isEmpty then throwError "witness type was accepted with duplicate codec names"
  let badAxiom ← liftCoreM (predicateCodecAxiomProblems (names.set! 7 ``Classical.choice))
  if badAxiom.isEmpty then throwError "axiom dependency was accepted"
  let indirect ← liftCoreM (predicateCodecAxiomProblems (names.set! 7 ``axiomCarrier))
  if indirect.isEmpty then throwError "transitive axiom dependency was accepted"
  let missing ← liftCoreM (predicateCodecAxiomProblems (names.set! 7 `Flapjack.Test.missingPredicateCodec))
  if missing.isEmpty then throwError "missing checked declaration was accepted"
  let incomplete ← liftCoreM (predicateCodecAxiomProblems #[])
  if incomplete.isEmpty then throwError "an incomplete declaration set was accepted"
  let duplicate ← liftCoreM (predicateCodecAxiomProblems (names.set! 7 names[0]!))
  if duplicate.isEmpty then throwError "a duplicated declaration was accepted"
  let current ← match resolvePredicateCodecInModule env env.mainModule
      `Flapjack.Test.PredicateCodecCurrent with
    | .ok names => pure names
    | .error message => throwError "current-module codec did not resolve: {message}"
  unless current.size == 8 do throwError "unexpected current-module declaration count"
  let currentProblems ← liftCoreM (predicateCodecAxiomProblems current)
  unless currentProblems.isEmpty do throwError "current-module declarations failed: {currentProblems}"
  let vacuous ← liftTermElabM (predicateCodecElaboratedProblemsIn env.mainModule
    `Flapjack.Test.PredicateCodecCurrent)
  if vacuous.isEmpty then throwError "vacuous same-owner codec passed the complete audit"
  if (resolvePredicateCodecInModule env env.mainModule `Flapjack.Test.PredicateCodecWrongKind).isOk then
    throwError "a regular definition was accepted in an abbreviation slot"
