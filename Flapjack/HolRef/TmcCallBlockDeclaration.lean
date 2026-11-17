module

public meta import Flapjack.HolRef.TmcCallBlockShape

public meta section

/-! Declaration and witness audit for the TMC call-block theorem. This does
not register a HOL qualifier or replace a source-level correspondence review. -/

namespace Flapjack
open Lean Meta

private def callBlockOwner (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

/-- Check a canonical map roundtrip statement for the call-block witnesses. -/
def tmcCallBlockMapWitnessProblems (type item : Expr) (pointwise : Bool) : MetaM (Array String) := do
  forallTelescope type fun args body => do
    unless args.size == 1 do return #["map witness must have one input"]
    let nat := mkConst `Nat
    let mapType := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) nat item
    let binder ← args[0]!.fvarId!.getDecl
    unless binder.binderInfo == .default && binder.type == mapType do
      return #["map witness input carrier changed"]
    let map := args[0]!
    let toBroad := mkAppN (mkConst `Flapjack.FiniteMapBroad.toBroad) #[nat, item, map]
    let roundtrip := mkAppN (mkConst `Flapjack.FiniteMapBroad.ofBroad) #[nat, item, toBroad]
    let lookup m := mkAppN (mkConst `Flapjack.HolFiniteMapExact.lookup) #[nat, item, m]
    let support m := mkAppN (mkConst `Flapjack.HolFiniteMapExact.finiteSupport) #[nat, item, m]
    let .app (.app (.const ``And []) lookupEq) (.app (.app (.const ``And []) supportEq) mapEq) := body
      | return #["map witness must have lookup, support and map equalities"]
    if pointwise then
      let problems ← forallTelescope lookupEq fun keys equation => do
        unless keys.size == 1 do return #["map witness lookup must quantify one key"]
        let key ← keys[0]!.fvarId!.getDecl
        unless key.binderInfo == .default && key.type == nat do return #["map witness key changed"]
        let expected ← mkEq (mkApp (lookup roundtrip) keys[0]!) (mkApp (lookup map) keys[0]!)
        return if equation == expected then #[] else #["map witness pointwise lookup changed"]
      unless problems.isEmpty do return problems
    else
      let expected ← mkEq (lookup roundtrip) (lookup map)
      unless lookupEq == expected do return #["map witness lookup changed"]
    let expectedSupport ← mkEq (support roundtrip) (support map)
    let expectedMap ← mkEq roundtrip map
    unless supportEq == expectedSupport && mapEq == expectedMap do
      return #["map witness support or roundtrip changed"]
    return #[]

/-- Check the two state-carrier roundtrip statements. -/
def tmcCallBlockStateWitnessProblems (type : Expr) : MetaM (Array String) := do
  forallTelescope type fun args body => do
    unless args.size == 2 do return #["state witness must quantify two type parameters"]
    for arg in args do
      let d ← arg.fvarId!.getDecl
      unless d.binderInfo == .implicit && d.type == mkSort (Level.succ Level.zero) do
        return #["state witness type parameter changed"]
    let c := args[0]!
    let ffi := args[1]!
    let exact := mkApp2 (mkConst `Flapjack.Compiler.Backend.BviSem.BviState) c ffi
    let broad := mkApp2 (mkConst `Flapjack.Compiler.Backend.BviSem.BviStateBroad) c ffi
    let .app (.app (.const ``And []) broadRoundtrip) exactRoundtrip := body
      | return #["state witness must have both roundtrips"]
    for (equation, fromBroad) in [(broadRoundtrip, true), (exactRoundtrip, false)] do
      let problems ← forallTelescope equation fun states result => do
        unless states.size == 1 do return #["state roundtrip must quantify one state"]
        let d ← states[0]!.fvarId!.getDecl
        unless d.binderInfo == .default && d.type == (if fromBroad then broad else exact) do
          return #["state roundtrip carrier changed"]
        let toBroad s := mkAppN (mkConst `Flapjack.Compiler.Backend.BviSem.BviState.toBroad) #[c, ffi, s]
        let ofBroad s := mkAppN (mkConst `Flapjack.Compiler.Backend.BviSem.BviState.ofBroad) #[c, ffi, s]
        let roundtrip := if fromBroad then toBroad (ofBroad states[0]!) else ofBroad (toBroad states[0]!)
        let expected ← mkEq roundtrip states[0]!
        return if result == expected then #[] else #["state witness roundtrip changed"]
      unless problems.isEmpty do return problems
    return #[]

/-- Check the fixed theorem and its local canonical map witnesses. This must
run in an environment exposing checked proof bodies; it does not itself
register or validate an attribute or establish cross-language equivalence. -/
def tmcCallBlockDeclarationProblems (decl : Name) : MetaM (Array String) := do
  let expected := `Flapjack.Compiler.Backend.BviTmc.CallBlockCorrectness.evaluate_cb
  let owner := `Flapjack.Compiler.Backend.BviTmc.Proofs.CallBlockCorrectness
  unless decl == expected do return #["call-block audit is restricted to the reviewed theorem"]
  let env ← getEnv
  unless callBlockOwner env decl == owner do return #["call-block theorem has the wrong owner"]
  let some (.thmInfo info) := env.checked.get.find? decl
    | return #["call-block declaration must be a checked theorem"]
  unless info.levelParams.isEmpty do return #["call-block theorem must be monomorphic"]
  let shape ← tmcCallBlockOptimizedResultProblems info.type
  unless shape.isEmpty do return shape
  let inventory ← tmcCallBlockMapInventoryProblems info.type
  unless inventory.isEmpty do return inventory
  for axiomName in (← collectAxioms decl) do
    unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
      return #[s!"call-block theorem depends on unapproved axiom {axiomName}"]
  let imported ← tmcHypothesisDeclarationProblems `Flapjack.Compiler.Backend.BviTmc.Induction.hypothesis
  unless imported.isEmpty do return imported.map ("imported hypothesis: " ++ ·)
  let namespaceName := `Flapjack.Compiler.Backend.BviTmc.CallBlockCorrectness
  let witnesses := #["holFmapAsFiniteSupportRelationWitness_BviState",
    "holFmapAsFiniteSupportUniversalWitness_evaluate_cb_refs",
    "holFmapAsFiniteSupportExistentialWitness_evaluate_cb_ordinaryMap",
    "holFmapAsFiniteSupportExistentialWitness_evaluate_cb_wrapMap",
    "holFmapAsFiniteSupportExistentialWitness_evaluate_cb_auxMap",
    "holFmapAsFiniteSupportExistentialWitness_evaluate_cb_workMap"]
  for i in [:witnesses.size] do
    let name := Name.str namespaceName witnesses[i]!
    unless callBlockOwner env name == owner do return #[s!"{name} has the wrong owner"]
    let some (.thmInfo witness) := env.checked.get.find? name
      | return #[s!"{name} must be a checked theorem"]
    unless witness.levelParams.isEmpty && (← collectAxioms name).isEmpty do
      return #[s!"{name} must be monomorphic and axiom-free"]
    let problems ← if i == 0 then tmcCallBlockStateWitnessProblems witness.type else do
      let nat := mkConst `Nat
      let value := mkConst `Flapjack.Compiler.Backend.BvlSem.Value
      let item := if i == 1 then mkApp (mkConst `Flapjack.Compiler.Backend.BvlSem.Ref) value else nat
      tmcCallBlockMapWitnessProblems witness.type item (i == 1)
    unless problems.isEmpty do return problems.map (s!"{name}: " ++ ·)
  return #[]

end Flapjack
