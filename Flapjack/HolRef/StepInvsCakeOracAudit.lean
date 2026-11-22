module

public meta import Lean
public meta import Lean.Util.CollectAxioms
public meta import Flapjack.HolRef
public meta import Flapjack.Compiler.Backend.BackendProof.SourceOracle

public meta section

/-! Elaborated audit of the narrow transitive HOL `THE` rendering used by
backendProof `step_invs_cake_orac` (`stepInvs_cakeOrac`): its `Nonempty β`
instance flows only into the reviewed `srcOracStepInvs` (tagged
`total_function_inhabitants := [C]`), whose body renders HOL `THE` by
`holThe`. Source comparison remains necessary; this audit is not a
cross-prover equivalence proof. -/
namespace Flapjack
open Lean Meta

open Flapjack.Compiler.Backend.BackendProof Flapjack.Compiler.Backend.BackendDefs
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend

/-- Independent expected type for `stepInvs_cakeOrac`. -/
private def expectedStepInvsCakeOrac : Prop :=
  ∀ {width : Nat} [NeZero width] {β : Type} [Nonempty β]
    (st : EvalOracleState)
    (f : Backend.Config × BackendProgs width → (Nat × Nat) × Value × List Dec)
    (asmConf : AsmConfigExact width) (c' : Backend.Config)
    (syn : Nat → (Nat × Nat) × List Dec)
    (decf : Value → Option (SourceToFlat.Config × β)),
    st.oracle = f ∘ cakeOrac asmConf c' syn id id →
    (∀ (x : Backend.Config × BackendProgs width) (k : Nat)
        (envId : Nat × Nat) (stV : Value) (decs : List Dec),
      x = cakeOrac asmConf c' syn id id k →
      f x = (envId, stV, decs) →
      decs = x.2.sourceProg ∧ envId = x.2.envId ∧
        ∃ dSt : SourceToFlat.Config × β, decf stV = some dSt ∧ dSt.1 = x.1.sourceConf) →
    SourceToFlat.OracleInvariant.srcOracStepInvs (some decf) SourceToSource.compile
      (some (.evalOracle st))

private def stepInvsName : Name := `Flapjack.Compiler.Backend.BackendProof.stepInvs_cakeOrac
private def srcOracStepInvsName : Name :=
  `Flapjack.Compiler.Backend.SourceToFlat.OracleInvariant.srcOracStepInvs

private def ownerModule (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

/-- Check the binder telescope: exactly the `NeZero width` and `Nonempty β`
instances, and `β` occurs only in the decoder binder's type. -/
def stepInvsCakeOracTelescopeProblems (type : Expr) : MetaM (Array String) := do
  forallTelescope type fun args _result => do
    -- Ten binders and the two premises of the source statement.
    unless args.size == 12 do return #["theorem has an unexpected number of binders"]
    let β := args[2]!
    let βDecl ← β.fvarId!.getDecl
    unless βDecl.userName == `β && βDecl.binderInfo == .implicit &&
        βDecl.type == .sort (.succ .zero) do
      return #["third binder must be the implicit payload type β : Type"]
    let mut instances : Array Expr := #[]
    for arg in args do
      let decl ← arg.fvarId!.getDecl
      if decl.binderInfo == .instImplicit then instances := instances.push decl.type
    let nonempty := mkApp (mkConst ``Nonempty [.succ .zero]) β
    let neZero ← mkAppM ``NeZero #[args[0]!]
    unless instances.size == 2 && instances[0]! == neZero && instances[1]! == nonempty do
      return #["expected exactly the NeZero width and Nonempty β instances"]
    let decf := args[9]!
    let decfDecl ← decf.fvarId!.getDecl
    let value := mkConst ``Flapjack.SemanticPrimitivesHOL.Value
    let payload ← mkAppM ``Prod #[mkConst ``Flapjack.Compiler.Backend.SourceToFlat.Config, β]
    let decoderType ← mkArrow value (← mkAppM ``Option #[payload])
    unless decfDecl.userName == `decf && decfDecl.binderInfo == .default &&
        decfDecl.type == decoderType do
      return #["last binder must be the decoder decf : Value → Option (Config × β)"]
    let mut problems : Array String := #[]
    for i in [0:10] do
      if i == 2 || i == 3 || i == 9 then continue
      let decl ← args[i]!.fvarId!.getDecl
      if decl.type.containsFVar β.fvarId! then
        problems := problems.push s!"binder {decl.userName} mentions β outside the decoder type"
    -- The premises' and result's β occurrences (the decoder, `srcOracStepInvs`'s
    -- payload argument and the existential's domain) are pinned by the complete
    -- expected statement compared in `stepInvsCakeOracProblems`.
    return problems

/-- Check the exact target, reviewed producer and complete statement. -/
def stepInvsCakeOracProblems (target : Name) : MetaM (Array String) := do
  unless target == stepInvsName do return #["unexpected transitive srcOracStepInvs target"]
  let env ← getEnv
  let producerRef : HolRef := {
    path := "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml",
    name := "src_orac_step_invs_def",
    totalFunctionInhabitants := #["C"] }
  unless HolRef.get? env srcOracStepInvsName == some producerRef do
    return #["srcOracStepInvs must retain its reviewed HOL THE reference"]
  unless ownerModule env srcOracStepInvsName ==
      `Flapjack.Compiler.Backend.SourceToFlat.Proofs.OracleStep do
    return #["srcOracStepInvs has the wrong defining module"]
  let some (.defnInfo producer) := env.find? srcOracStepInvsName
    | return #["srcOracStepInvs must be a definition"]
  unless producer.value.getUsedConstants.contains ``Flapjack.holThe do
    return #["srcOracStepInvs must render HOL THE by holThe"]
  let some (.thmInfo info) := env.find? target | return #["stepInvs_cakeOrac must be a theorem"]
  unless info.levelParams.isEmpty do return #["stepInvs_cakeOrac must be monomorphic"]
  unless ownerModule env target == `Flapjack.Compiler.Backend.BackendProof.SourceOracle do
    return #["stepInvs_cakeOrac has the wrong defining module"]
  let telescope ← stepInvsCakeOracTelescopeProblems info.type
  unless telescope.isEmpty do return telescope
  let some (.defnInfo spec) := env.find? ``expectedStepInvsCakeOrac
    | return #["missing independent expected type"]
  unless ← withReducible (isDefEq info.type spec.value) do
    return #["stepInvs_cakeOrac type differs from the complete audited statement"]
  let mut problems : Array String := #[]
  for axiomName in ← Lean.collectAxioms target do
    unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
      problems := problems.push s!"{target} depends on unexpected axiom {axiomName}"
  return problems

end Flapjack
