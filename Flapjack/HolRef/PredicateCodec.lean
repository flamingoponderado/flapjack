module

public meta import Lean
public meta import Lean.Util.CollectAxioms

public meta section

/-! Elaboration-side infrastructure for the prospective closure simulation
finite-map qualifier. These checks are not connected to `@[hol]`: resolving
names and excluding axioms does not validate codec bodies, witness statements,
or correspondence with HOL. -/

namespace Flapjack
open Lean Meta

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

/-- Check one complete, unconditional equality in the prospective transport
witness. `names` must be the owner-validated codec bundle; the codec bodies are
checked separately. The equality applications are compared before reduction. -/
private def predicateCodecWitnessHalfProblems (names : Array Name) (c₁ c₂ : Expr)
    (first : Bool) (type : Expr) : MetaM (Array String) := do
  forallTelescope type fun args result => do
    let count := if first then 2 else 3
    if args.size != count then
      return #[s!"roundtrip half has {args.size} binders instead of {count}"]
    let mut errors : Array String := #[]
    let mut types : Array Expr := #[]
    for arg in args do
      let d ← arg.fvarId!.getDecl
      types := types.push d.type
      if d.binderInfo != BinderInfo.default then
        errors := errors.push "roundtrip half has a non-explicit binder"
    let nat := mkConst `Nat
    let exp := mkConst `Flapjack.Compiler.Backend.ClosLang.Exp
    let payload := mkApp2 (mkConst `Prod [Level.zero, Level.zero]) nat exp
    let code := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) nat payload
    let tail := mkApp2 (mkConst names[0]!) c₁ c₂
    let raw := mkConst names[1]!
    let support := mkConst names[2]!
    if first then
      let relProblems ← forallTelescope types[0]! fun domains conclusion => do
        if domains.size != 1 then return #["canonical predicate must have one domain"]
        let d ← domains[0]!.fvarId!.getDecl
        let mut issues : Array String := #[]
        if d.binderInfo != BinderInfo.default then
          issues := issues.push "canonical predicate domain must be explicit"
        unless ← isDefEq d.type code do
          issues := issues.push "canonical predicate domain has the wrong type"
        if conclusion != tail then
          issues := issues.push "canonical predicate tail has the wrong application spine"
        return issues
      errors := errors ++ relProblems
      unless ← isDefEq types[1]! code do
        errors := errors.push "canonical code has the wrong type"
      let toRaw := mkAppN (mkConst names[5]!) #[c₁, c₂, args[0]!]
      let lhs := mkAppN (mkConst names[6]!) #[c₁, c₂, toRaw, args[1]!]
      let rhs := mkApp args[0]! args[1]!
      let expected := mkApp3 (mkConst `Eq [Level.succ Level.zero]) tail lhs rhs
      if result != expected then
        errors := errors.push "canonical predicate roundtrip equality has the wrong application spine"
    else
      let relProblems ← forallTelescope types[0]! fun domains conclusion => do
        if domains.size != 2 then return #["raw predicate must have two domains"]
        let lookup ← domains[0]!.fvarId!.getDecl
        let finite ← domains[1]!.fvarId!.getDecl
        let mut issues : Array String := #[]
        if lookup.binderInfo != BinderInfo.default || finite.binderInfo != BinderInfo.default then
          issues := issues.push "raw predicate domains must be explicit"
        unless ← isDefEq lookup.type raw do
          issues := issues.push "raw predicate lookup has the wrong type"
        unless ← isDefEq finite.type (mkApp support domains[0]!) do
          issues := issues.push "raw predicate support has the wrong type"
        if conclusion != tail then
          issues := issues.push "raw predicate tail has the wrong application spine"
        return issues
      errors := errors ++ relProblems
      unless ← isDefEq types[1]! raw do
        errors := errors.push "raw lookup has the wrong type"
      unless ← isDefEq types[2]! (mkApp support args[1]!) do
        errors := errors.push "raw support has the wrong type"
      let fromRaw := mkAppN (mkConst names[6]!) #[c₁, c₂, args[0]!]
      let lhs := mkAppN (mkConst names[5]!) #[c₁, c₂, fromRaw, args[1]!, args[2]!]
      let rhs := mkApp2 args[0]! args[1]! args[2]!
      let expected := mkApp3 (mkConst `Eq [Level.succ Level.zero]) tail lhs rhs
      if result != expected then
        errors := errors.push "raw predicate roundtrip equality has the wrong application spine"
    return errors

/-- Check the elaborated type of the prospective predicate-transport witness.
This does not validate the codec definitions, declaration ownership or axioms,
and remains unconnected to `@[hol]`. -/
def predicateCodecWitnessTypeProblems (names : Array Name) (type : Expr) :
    MetaM (Array String) := do
  unless names.size == 8 do return #["witness type check requires the resolved codec bundle"]
  unless names.toList.eraseDups.length == names.size do
    return #["witness type check requires distinct codec declarations"]
  forallTelescope type fun args result => do
    unless args.size == 2 do return #["witness must have exactly two compiler type parameters"]
    let mut errors : Array String := #[]
    for arg in args do
      let d ← arg.fvarId!.getDecl
      if d.binderInfo != BinderInfo.implicit then
        errors := errors.push "witness compiler type parameters must be implicit"
      unless ← isDefEq d.type (mkSort (Level.succ Level.zero)) do
        errors := errors.push "witness compiler parameter must have type Type"
    let .app (.app (.const ``And []) first) second := result
      | return errors.push "witness must be a conjunction of both roundtrips"
    errors := errors ++ (← predicateCodecWitnessHalfProblems names args[0]! args[1]! true first)
    errors := errors ++ (← predicateCodecWitnessHalfProblems names args[0]! args[1]! false second)
    return errors

end Flapjack
