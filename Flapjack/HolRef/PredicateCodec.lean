module

public meta import Lean
public meta import Lean.Util.CollectAxioms

public meta section

/-! Elaboration-side infrastructure for the prospective closure simulation
finite-map qualifier. These checks are not connected to `@[hol]`: resolving
names and excluding axioms does not validate codec bodies, witness statements,
or correspondence with HOL. -/

namespace Flapjack
open Lean

private def predicateCodecOwner : Name :=
  `Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvalSim

private def predicateCodecNamespace : Name :=
  `Flapjack.Compiler.Backend.ClosToBvl

private def predicateCodecHelpers : Array String :=
  #["SimulationTail", "RawCode", "RawCodeSupport", "toBroad", "ofBroad",
    "toBroadPredicate", "fromBroadPredicate"]

/-- Resolve a declaration's defining module, including the current module's
unindexed declarations. This is not itself a representation check. -/
def predicateCodecDefiningModule (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

/-- Resolve private helpers and a public witness within an explicit owner and
namespace. The actual qualifier must use `resolvePredicateCodec`, which fixes
both; this parameterized function supports owner-isolation tests. -/
def resolvePredicateCodecInModule (env : Environment) (owner namespaceName : Name) : Except String (Array Name) := do
  let mut buckets : Array (Array Name) := Array.replicate predicateCodecHelpers.size #[]
  for (name, _) in env.constants.toList do
    if let some userName := privateToUserName? name then
      if predicateCodecDefiningModule env name == owner then
        for i in [:predicateCodecHelpers.size] do
          if userName == Name.str namespaceName predicateCodecHelpers[i]! then
            buckets := buckets.modify i (·.push name)
  let mut resolved : Array Name := #[]
  for i in [:predicateCodecHelpers.size] do
    let found := buckets[i]!
    unless found.size == 1 do
      throw s!"expected one private {predicateCodecHelpers[i]!} in {owner}, found {found.size}"
    let name := found[0]!
    match env.find? name with
    | some (.defnInfo info) =>
      unless info.safety == .safe && info.levelParams.isEmpty do
        throw s!"{name} must be a safe, monomorphic definition"
      if i < 3 then
        unless info.hints == .abbrev do
          throw s!"{name} must be an abbreviation"
      else
        match info.hints with
        | .regular _ => pure ()
        | _ => throw s!"{name} must be a regular definition"
    | _ => throw s!"{name} must be a definition"
    resolved := resolved.push name
  let witness := Name.str namespaceName "simulationPredicateRoundtrips"
  unless predicateCodecDefiningModule env witness == owner do
    throw s!"{witness} has the wrong defining module"
  match env.find? witness with
  | some (.thmInfo info) =>
    unless info.levelParams.isEmpty do
      throw s!"{witness} must be monomorphic"
  | _ => throw s!"{witness} must be a theorem"
  return resolved.push witness

/-- Resolve only the reviewed codec owner. This preliminary check does not
authorize a qualifier without separate body and witness-type validation. -/
def resolvePredicateCodec (env : Environment) : Except String (Array Name) :=
  resolvePredicateCodecInModule env predicateCodecOwner predicateCodecNamespace

/-- Reject axiom dependencies of the already resolved codec declarations.
Callers must separately validate their owners, kinds, bodies, and types. -/
def predicateCodecAxiomProblems (names : Array Name) : CoreM (Array String) := do
  unless names.size == predicateCodecHelpers.size + 1 do
    return #["predicate codec axiom check requires the complete resolved declaration set"]
  unless names.toList.eraseDups.length == names.size do
    return #["predicate codec axiom check requires distinct declarations"]
  let env ← getEnv
  let mut errors : Array String := #[]
  for name in names do
    if (env.checked.get.find? name).isNone then
      errors := errors.push s!"{name} is absent from the checked environment"
    else
      let axioms ← collectAxioms name
      unless axioms.isEmpty do
        errors := errors.push s!"{name} depends on axioms {axioms}"
  return errors

/-- Check the fixed owner's declaration kinds and axiom closure together.
This is preliminary infrastructure, not a codec-body or HOL-source review. -/
def predicateCodecOwnerAndAxiomProblems : CoreM (Array String) := do
  match resolvePredicateCodec (← getEnv) with
  | .error message => return #[message]
  | .ok names => predicateCodecAxiomProblems names

end Flapjack
