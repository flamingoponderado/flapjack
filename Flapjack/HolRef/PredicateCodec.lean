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
  match env.checked.get.find? witness with
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

/-- Check the elaborated body of one representation alias: the simulation
tail, raw lookup, or finite-support predicate. The names must come from the
owner-validated bundle. This is not an enabled `@[hol]` check. -/
def predicateCodecAliasBodyProblems (names : Array Name) (index : Nat)
    (type value : Expr) : MetaM (Array String) := do
  unless names.size == 8 && names.toList.eraseDups.length == names.size do
    return #["codec alias check requires distinct resolved declarations"]
  unless index < 3 do return #["codec alias index must be 0, 1 or 2"]
  let count := if index == 0 then 2 else if index == 1 then 0 else 1
  let nat := mkConst `Nat
  let closExp := mkConst `Flapjack.Compiler.Backend.ClosLang.Exp
  let bvlExp := mkConst `Flapjack.Compiler.Backend.Bvl.Exp
  let pair (a b : Expr) := mkApp2 (mkConst `Prod [Level.zero, Level.zero]) a b
  let payload := pair nat closExp
  let raw := mkConst names[1]!
  let expectedSort := if index == 2 then mkSort Level.zero else mkSort (Level.succ Level.zero)
  let typeProblems ← forallTelescope type fun args result => do
    if args.size != count then return #[s!"codec alias type needs {count} binders"]
    let mut errors : Array String := #[]
    for i in [:args.size] do
      let d ← args[i]!.fvarId!.getDecl
      if d.binderInfo != BinderInfo.default then
        errors := errors.push "codec alias type binders must be explicit"
      unless ← isDefEq d.type (if index == 0 then mkSort (Level.succ Level.zero) else raw) do
        errors := errors.push "codec alias type has the wrong input carrier"
    unless ← isDefEq result expectedSort do errors := errors.push "codec alias has the wrong result sort"
    return errors
  let bodyProblems ← lambdaTelescope value fun args body => do
    if args.size != count then return #[s!"codec alias body needs {count} binders"]
    let mut errors : Array String := #[]
    for i in [:args.size] do
      let d ← args[i]!.fvarId!.getDecl
      if d.binderInfo != BinderInfo.default then
        errors := errors.push "codec alias body binders must be explicit"
      unless ← isDefEq d.type (if index == 0 then mkSort (Level.succ Level.zero) else raw) do
        errors := errors.push "codec alias body has the wrong input carrier"
    if index == 0 then
      let sourceOracle := mkApp (mkConst `Flapjack.Compiler.Backend.ClosSem.CompileOracle) args[0]!
      let sourceCompiler := mkApp (mkConst `Flapjack.Compiler.Backend.ClosSem.Compiler) args[0]!
      let expressions := mkApp (mkConst `List [Level.zero]) closExp
      let targetCode := mkApp (mkConst `Flapjack.Spt) (pair nat bvlExp)
      let targetOracle := mkApp (mkConst `Flapjack.Compiler.Backend.BvlSem.CompileOracle) args[1]!
      let targetCompiler := mkApp (mkConst `Flapjack.Compiler.Backend.BvlSem.Compiler) args[1]!
      let expected := #[sourceOracle, sourceCompiler, expressions, targetCode, targetOracle, targetCompiler, nat]
      let tailErrors ← forallTelescope body fun domains result => do
        unless domains.size == expected.size do return #["simulation tail must have seven domains"]
        let mut issues : Array String := #[]
        for i in [:domains.size] do
          let d ← domains[i]!.fvarId!.getDecl
          if d.binderInfo != BinderInfo.default then issues := issues.push "simulation tail domain is not explicit"
          unless ← isDefEq d.type expected[i]! do issues := issues.push s!"simulation tail domain {i} has the wrong type"
        unless ← isDefEq result (mkSort Level.zero) do issues := issues.push "simulation tail does not end in Prop"
        return issues
      errors := errors ++ tailErrors
    else if index == 1 then
      let expected := mkForall Name.anonymous BinderInfo.default nat
        (mkApp (mkConst `Option [Level.zero]) payload)
      unless ← isDefEq body expected do errors := errors.push "raw lookup has the wrong type"
      match body with
      | .forallE _ _ _ BinderInfo.default => pure ()
      | _ => errors := errors.push "raw lookup must have an explicit key domain"
    else
      let listNat := mkApp (mkConst `List [Level.zero]) nat
      let optionPayload := mkApp (mkConst `Option [Level.zero]) payload
      let expected ← withLocalDeclD `keys listNat fun keys => do
        let predicate ← withLocalDeclD `key nat fun key => do
          let present := mkApp3 (mkConst `Ne [Level.succ Level.zero]) optionPayload
            (mkApp args[0]! key) (mkApp (mkConst `Option.none [Level.zero]) payload)
          let membership := mkAppN (mkConst `Membership.mem [Level.zero, Level.zero])
            #[nat, listNat, mkApp (mkConst `List.instMembership [Level.zero]) nat, keys, key]
          mkForallFVars #[key] (mkForall Name.anonymous BinderInfo.default present membership)
        let predicate ← mkLambdaFVars #[keys] predicate
        return mkApp2 (mkConst `Exists [Level.succ Level.zero]) listNat predicate
      unless ← isDefEq body expected do errors := errors.push "finite-support predicate has the wrong body"
      match body with
      | .app (.app (.const ``Exists _) _) (.lam _ _ (.forallE _ _ (.forallE _ _ _ premiseInfo) keyInfo) keysInfo) =>
        unless keysInfo == BinderInfo.default && keyInfo == BinderInfo.default &&
            premiseInfo == BinderInfo.default do
          errors := errors.push "finite-support predicate binders must be explicit"
      | _ => errors := errors.push "finite-support predicate has the wrong binder structure"
    return errors
  return typeProblems ++ bodyProblems

/-- Check the elaborated type and unreduced body of the direct map codec.
Index 3 is the lookup projection and index 4 is reconstruction. The caller
must separately resolve and validate the codec bundle and the support alias;
this preliminary check remains unconnected to `@[hol]`. -/
def predicateCodecMapBodyProblems (names : Array Name) (index : Nat)
    (type value : Expr) : MetaM (Array String) := do
  unless names.size == 8 && names.toList.eraseDups.length == names.size do
    return #["map codec check requires distinct resolved declarations"]
  unless index == 3 || index == 4 do return #["map codec index must be 3 or 4"]
  let nat := mkConst `Nat
  let exp := mkConst `Flapjack.Compiler.Backend.ClosLang.Exp
  let payload := mkApp2 (mkConst `Prod [Level.zero, Level.zero]) nat exp
  let code := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) nat payload
  let raw := mkConst names[1]!
  let support := mkConst names[2]!
  let count := if index == 3 then 1 else 2
  let typeProblems ← forallTelescope type fun args result => do
    if args.size != count then return #[s!"map codec type needs {count} binders"]
    let mut errors : Array String := #[]
    for arg in args do
      let d ← arg.fvarId!.getDecl
      if d.binderInfo != BinderInfo.default then
        errors := errors.push "map codec type binders must be explicit"
    let d₀ ← args[0]!.fvarId!.getDecl
    unless ← isDefEq d₀.type (if index == 3 then code else raw) do
      errors := errors.push "map codec type has the wrong input carrier"
    if index == 4 then
      let d₁ ← args[1]!.fvarId!.getDecl
      unless ← isDefEq d₁.type (mkApp support args[0]!) do
        errors := errors.push "map codec type has the wrong support premise"
    unless ← isDefEq result (if index == 3 then raw else code) do
      errors := errors.push "map codec type has the wrong result carrier"
    return errors
  let bodyProblems ← lambdaTelescope value fun args body => do
    if args.size != count then return #[s!"map codec body needs {count} binders"]
    let mut errors : Array String := #[]
    for arg in args do
      let d ← arg.fvarId!.getDecl
      if d.binderInfo != BinderInfo.default then
        errors := errors.push "map codec body binders must be explicit"
    let d₀ ← args[0]!.fvarId!.getDecl
    unless ← isDefEq d₀.type (if index == 3 then code else raw) do
      errors := errors.push "map codec body has the wrong input carrier"
    if index == 4 then
      let d₁ ← args[1]!.fvarId!.getDecl
      unless ← isDefEq d₁.type (mkApp support args[0]!) do
        errors := errors.push "map codec body has the wrong support premise"
    let expected := if index == 3 then
      mkAppN (mkConst `Flapjack.HolFiniteMapExact.lookup) #[nat, payload, args[0]!]
    else
      mkAppN (mkConst `Flapjack.HolFiniteMapExact.mk) #[nat, payload, args[0]!, args[1]!]
    if body != expected then errors := errors.push "map codec has the wrong application spine"
    return errors
  return typeProblems ++ bodyProblems

/-- Validate the binders of one predicate-transport helper. The helper types
refer to aliases in the resolved bundle; those aliases must be checked
separately before this result can be used. -/
private def predicateCodecTranslatorInputs (names : Array Name) (index : Nat)
    (args : Array Expr) : MetaM (Array String) := do
  let count := if index == 5 then 5 else 4
  unless args.size == count do return #[s!"predicate codec needs {count} binders"]
  let mut errors : Array String := #[]
  let mut types : Array Expr := #[]
  for i in [:args.size] do
    let d ← args[i]!.fvarId!.getDecl
    types := types.push d.type
    let expectedInfo := if i < 2 then BinderInfo.implicit else BinderInfo.default
    if d.binderInfo != expectedInfo then
      errors := errors.push s!"predicate codec binder {i} has the wrong visibility"
  for i in [:2] do
    unless ← isDefEq types[i]! (mkSort (Level.succ Level.zero)) do
      errors := errors.push s!"predicate codec compiler parameter {i} is not Type"
  let nat := mkConst `Nat
  let exp := mkConst `Flapjack.Compiler.Backend.ClosLang.Exp
  let payload := mkApp2 (mkConst `Prod [Level.zero, Level.zero]) nat exp
  let code := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) nat payload
  let raw := mkConst names[1]!
  let support := mkConst names[2]!
  let tail := mkApp2 (mkConst names[0]!) args[0]! args[1]!
  let relErrors ← forallTelescope types[2]! fun domains result => do
    let domainCount := if index == 5 then 1 else 2
    unless domains.size == domainCount do
      return #[s!"predicate codec relation needs {domainCount} domains"]
    let mut issues : Array String := #[]
    for domain in domains do
      let d ← domain.fvarId!.getDecl
      if d.binderInfo != BinderInfo.default then
        issues := issues.push "predicate codec relation domains must be explicit"
    let d₀ ← domains[0]!.fvarId!.getDecl
    unless ← isDefEq d₀.type (if index == 5 then code else raw) do
      issues := issues.push "predicate codec relation has the wrong first domain"
    if index == 6 then
      let d₁ ← domains[1]!.fvarId!.getDecl
      unless ← isDefEq d₁.type (mkApp support domains[0]!) do
        issues := issues.push "predicate codec relation has the wrong support domain"
    if result != tail then
      issues := issues.push "predicate codec relation has the wrong tail application"
    return issues
  errors := errors ++ relErrors
  unless ← isDefEq types[3]! (if index == 5 then raw else code) do
    errors := errors.push "predicate codec data input has the wrong type"
  if index == 5 then
    unless ← isDefEq types[4]! (mkApp support args[3]!) do
      errors := errors.push "predicate codec support input has the wrong type"
  return errors

/-- Check predicate-transport types and computational application spines.
The support argument on the reverse path may be any axiom-free proof of the
required proposition for the actual lookup; Lean may lift that proof to an
auxiliary theorem. Callers must separately validate aliases, owners and axiom
closure. This check is not yet connected to `@[hol]`. -/
def predicateCodecTranslatorBodyProblems (names : Array Name) (index : Nat)
    (type value : Expr) : MetaM (Array String) := do
  unless names.size == 8 && names.toList.eraseDups.length == names.size do
    return #["predicate codec check requires distinct resolved declarations"]
  unless index == 5 || index == 6 do return #["predicate codec index must be 5 or 6"]
  let typeProblems ← forallTelescope type fun args result => do
    let errors ← predicateCodecTranslatorInputs names index args
    let count := if index == 5 then 5 else 4
    unless args.size == count do return errors
    let expected := mkApp2 (mkConst names[0]!) args[0]! args[1]!
    if result != expected then return errors.push "predicate codec has the wrong result tail"
    return errors
  let bodyProblems ← lambdaTelescope value fun args body => do
    let mut errors ← predicateCodecTranslatorInputs names index args
    let count := if index == 5 then 5 else 4
    unless args.size == count do return errors
    let tail := mkApp2 (mkConst names[0]!) args[0]! args[1]!
    unless ← isDefEq (← inferType body) tail do
      errors := errors.push "predicate codec body has the wrong result tail"
    if index == 5 then
      let map := mkApp2 (mkConst names[4]!) args[3]! args[4]!
      if body != mkApp args[2]! map then
        errors := errors.push "predicate codec has the wrong canonical application spine"
    else
      let .app (.app rel lookup) proof := body
        | return errors.push "predicate codec must apply its raw relation twice"
      if rel != args[2]! || lookup != mkApp (mkConst names[3]!) args[3]! then
        errors := errors.push "predicate codec has the wrong raw application spine"
      let proofType ← inferType proof
      unless ← isDefEq proofType (mkApp (mkConst names[2]!) lookup) do
        errors := errors.push "predicate codec proof is not support for its actual lookup"
    return errors
  return typeProblems ++ bodyProblems

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

/-- Audit a codec in an explicit owner and namespace. This parameterized form
supports adversarial fixtures; only the fixed-owner wrapper may be considered
by a future qualifier. Neither form checks HOL correspondence. -/
def predicateCodecElaboratedProblemsIn (owner namespaceName : Name) : MetaM (Array String) := do
  let env ← getEnv
  let names ← match resolvePredicateCodecInModule env owner namespaceName with
    | .error message => return #[message]
    | .ok names => pure names
  let axiomProblems ← predicateCodecAxiomProblems names
  unless axiomProblems.isEmpty do return axiomProblems
  for i in [:7] do
    let some (.defnInfo info) := env.checked.get.find? names[i]!
      | return #[s!"{names[i]!} is not a checked definition"]
    unless info.safety == .safe && info.levelParams.isEmpty do
      return #[s!"{names[i]!} is not a safe monomorphic checked definition"]
    if i < 3 then
      unless info.hints == .abbrev do return #[s!"{names[i]!} is not a checked abbreviation"]
    else
      match info.hints with
      | .regular _ => pure ()
      | _ => return #[s!"{names[i]!} is not a regular checked definition"]
    let problems ← if i < 3 then
        predicateCodecAliasBodyProblems names i info.type info.value
      else if i < 5 then
        predicateCodecMapBodyProblems names i info.type info.value
      else
        predicateCodecTranslatorBodyProblems names i info.type info.value
    unless problems.isEmpty do return problems
  let some (.thmInfo witness) := env.checked.get.find? names[7]!
    | return #[s!"{names[7]!} is not a checked theorem"]
  unless witness.levelParams.isEmpty do return #["checked witness must be monomorphic"]
  predicateCodecWitnessTypeProblems names witness.type

/-- Audit the fixed codec's checked declarations, bodies, witness type and
axiom closure together. This is still unconnected to `@[hol]` and does not
check an evaluation-simulation body or establish correspondence with HOL. -/
def predicateCodecElaboratedProblems : MetaM (Array String) :=
  predicateCodecElaboratedProblemsIn predicateCodecOwner predicateCodecNamespace

end Flapjack
