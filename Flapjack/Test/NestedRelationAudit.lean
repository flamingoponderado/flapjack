import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.ValueRelation
import Lean.Util.CollectAxioms

/-! Elaborated checks for the proposed closure-annotation relation qualifier.

This is preparatory: it does not authorize a HOL tag or replace source review.
It checks mutual inductive membership, complete constructor and witness types
against independently elaborated propositions, and the witness's axiom
dependencies. It does not establish HOL correspondence or authorize a tag.
-/

open Lean Elab Command
open Flapjack Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- The source number rule, independently elaborated for comparison. -/
private def expectedNumberRule : Prop :=
  ∀ value : Int, ValueRel (.number value) (.number value)

private def expectedWordRule : Prop :=
  ∀ value : BitVec 64, ValueRel (.word64 value) (.word64 value)

private def expectedBlockRule : Prop :=
  ∀ (tag : Nat) (left right : List Value),
    List.Forall₂ ValueRel left right → ValueRel (.block tag left) (.block tag right)

private def expectedBytesRule : Prop :=
  ∀ bytes : List (BitVec 8), ValueRel (.byteVector bytes) (.byteVector bytes)

private def expectedPointerRule : Prop :=
  ∀ (flag : Bool) (address : Nat), ValueRel (.refPtr flag address) (.refPtr flag address)

private def expectedClosureRule : Prop :=
  ∀ (location : Option Nat) (args nextArgs env nextEnv : List Value)
    (arity m : Nat) (body nextBody : Flapjack.Compiler.Backend.ClosLang.Exp) (index : Spt Nat),
    shiftSource (altFreeSource [body]).1 m arity index = [nextBody] →
    (∀ n, altFvSource n [body] = true ∧ arity ≤ n → EnvOk m 0 index env nextEnv (n - arity)) →
    everyFnVarsNone [body] → env.length = m → List.Forall₂ ValueRel args nextArgs →
    ValueRel (.closure location args env arity body) (.closure location nextArgs nextEnv arity nextBody)

private def expectedRecclosureRule : Prop :=
  ∀ (location : Option Nat) (args nextArgs env nextEnv : List Value)
    (functions nextFunctions : List (Nat × Flapjack.Compiler.Backend.ClosLang.Exp)) (index : Nat),
    FunctionsRel env nextEnv functions.length functions nextFunctions →
    List.Forall₂ ValueRel args nextArgs → index < functions.length →
    ValueRel (.recclosure location args env functions index)
      (.recclosure location nextArgs nextEnv nextFunctions index)

private def expectedOutsideRule : Prop :=
  ∀ (m l : Nat) (index : Spt Nat) (env nextEnv : List Value) (n : Nat),
    l + m ≤ n → EnvOk m l index env nextEnv n

private def expectedLocalRule : Prop :=
  ∀ (m l : Nat) (index : Spt Nat) (env nextEnv : List Value) (n : Nat),
    n < l → ValueRel (@holEl Value ⟨unitValue⟩ n env) (@holEl Value ⟨unitValue⟩ n nextEnv) →
    n < env.length → n < nextEnv.length → EnvOk m l index env nextEnv n

private def expectedCapturedRule : Prop :=
  ∀ (m l : Nat) (index : Spt Nat) (env nextEnv : List Value) (n compact : Nat),
    l ≤ n → n < l + m → n < l + m → sptLookup (n - l) index = some compact →
    n < env.length → l + compact < nextEnv.length →
    ValueRel (@holEl Value ⟨unitValue⟩ n env) (@holEl Value ⟨unitValue⟩ (l + compact) nextEnv) →
    EnvOk m l index env nextEnv n

private def expectedFunctionsNilRule : Prop :=
  ∀ (env nextEnv : List Value) (count : Nat), FunctionsRel env nextEnv count [] []

private def expectedFunctionsConsRule : Prop :=
  ∀ (env nextEnv : List Value) (count arity m : Nat)
    (body nextBody : Flapjack.Compiler.Backend.ClosLang.Exp) (index : Spt Nat)
    (functions nextFunctions : List (Nat × Flapjack.Compiler.Backend.ClosLang.Exp)),
    shiftSource (altFreeSource [body]).1 m (count + arity) index = [nextBody] →
    (∀ n, altFvSource n [body] = true ∧ arity + count ≤ n →
      EnvOk m 0 index env nextEnv (n - (arity + count))) →
    everyFnVarsNone [body] → env.length = m →
    FunctionsRel env nextEnv count functions nextFunctions →
    FunctionsRel env nextEnv count ((arity, body) :: functions) ((arity, nextBody) :: nextFunctions)

private def expectedFunctionsWitness : Prop :=
  ∀ (env nextEnv : List Value) (count : Nat)
    (functions nextFunctions : List (Nat × Flapjack.Compiler.Backend.ClosLang.Exp)),
    FunctionsRel env nextEnv count functions nextFunctions ↔
      List.Forall₂ (fun left right => ∃ m i,
        right.1 = left.1 ∧
        shiftSource (altFreeSource [left.2]).1 m (count + left.1) i = [right.2] ∧
        (∀ n, altFvSource n [left.2] = true ∧ left.1 + count ≤ n →
          EnvOk m 0 i env nextEnv (n - (left.1 + count))) ∧
        everyFnVarsNone [left.2] ∧ env.length = m) functions nextFunctions

run_cmd do
  let env ← getEnv
  let names := [``ValueRel, ``FunctionsRel, ``EnvOk]
  let constructors : List (Name × List Name) := [
    (``ValueRel, [``ValueRel.number, ``ValueRel.word64, ``ValueRel.block,
      ``ValueRel.byteVector, ``ValueRel.refPtr, ``ValueRel.closure, ``ValueRel.recclosure]),
    (``FunctionsRel, [``FunctionsRel.nil, ``FunctionsRel.cons]),
    (``EnvOk, [``EnvOk.outside, ``EnvOk.local, ``EnvOk.captured])]
  for (name, expectedConstructors) in constructors do
    match env.find? name with
    | some (.inductInfo info) =>
      unless info.all == names do
        throwError "{name} is not in the expected mutual inductive block"
      unless info.ctors == expectedConstructors do
        throwError "{name} does not have the expected constructors"
      if info.isUnsafe then
        throwError "{name} is unsafe"
    | _ => throwError "{name} is not an inductive declaration"
  let required : List (Name × List Name) := [
    (``ValueRel.recclosure, [``FunctionsRel, ``Value, ``List.Forall₂]),
    (``FunctionsRel.cons, [``shiftSource, ``altFreeSource, ``altFvSource,
      ``everyFnVarsNone, ``EnvOk, ``FunctionsRel, ``Value]),
    (``EnvOk.captured, [``ValueRel, ``Value, ``sptLookup, ``holEl]),
    (``functionsRel_iff, [``FunctionsRel, ``List.Forall₂, ``EnvOk, ``Value,
      ``shiftSource, ``altFreeSource, ``altFvSource, ``everyFnVarsNone])]
  for (name, dependencies) in required do
    let some info := env.find? name | throwError "missing declaration {name}"
    let used := info.type.getUsedConstants
    for dependency in dependencies do
      unless used.contains dependency do
        throwError "{name} does not use expected elaborated dependency {dependency}"
  let rules : List (Name × Name) := [
    (``ValueRel.number, ``expectedNumberRule), (``ValueRel.word64, ``expectedWordRule),
    (``ValueRel.block, ``expectedBlockRule), (``ValueRel.byteVector, ``expectedBytesRule),
    (``ValueRel.refPtr, ``expectedPointerRule), (``ValueRel.closure, ``expectedClosureRule),
    (``ValueRel.recclosure, ``expectedRecclosureRule), (``EnvOk.outside, ``expectedOutsideRule),
    (``EnvOk.local, ``expectedLocalRule), (``EnvOk.captured, ``expectedCapturedRule),
    (``FunctionsRel.nil, ``expectedFunctionsNilRule),
    (``FunctionsRel.cons, ``expectedFunctionsConsRule)]
  for (ruleName, expectedName) in rules do
    let some (.ctorInfo rule) := env.find? ruleName | throwError "missing constructor {ruleName}"
    let some (.defnInfo expected) := env.find? expectedName | throwError "missing expected rule {expectedName}"
    unless ← liftTermElabM (Lean.Meta.isDefEq rule.type expected.value) do
      throwError "{ruleName} does not have its expected elaborated rule type"
  let some (.thmInfo witness) := env.find? ``functionsRel_iff
    | throwError "missing functionsRel_iff theorem"
  let some (.defnInfo expectedWitness) := env.find? ``expectedFunctionsWitness
    | throwError "missing expected witness type"
  unless ← liftTermElabM (Lean.Meta.isDefEq witness.type expectedWitness.value) do
    throwError "functionsRel_iff does not have the expected elaborated type"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms ``functionsRel_iff
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError "functionsRel_iff has unapproved axiom {axiomName}"

namespace Flapjack.Test
/-- Marker emitted only after the elaborated relation audit succeeds. -/
theorem nestedRelationAudit_passed : True := trivial
end Flapjack.Test
