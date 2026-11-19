module

public meta import Lean
public meta import Lean.Util.CollectAxioms
public meta import Flapjack.HolRef

public meta section

/-! Elaborated audit of the narrow transitive HOL `THE` rendering used by
`joinEnvLocals` and its two odd-insertion theorems. Source comparison remains
necessary; this audit is not a cross-prover equivalence proof. -/
namespace Flapjack
open Lean Meta

private def gcNamespace : Name := `Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
private def joinEnvName : Name := `Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.joinEnv
private def joinEnvLocalsName : Name := `Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.joinEnvLocals

private def typeHeaderProblems (args : Array Expr) : MetaM (Array String) := do
  if args.size < 3 then return #["missing polymorphic and instance binders"]
  let α ← args[0]!.fvarId!.getDecl
  let β ← args[1]!.fvarId!.getDecl
  let inst ← args[2]!.fvarId!.getDecl
  unless α.userName == `α && β.userName == `β && α.binderInfo == .implicit &&
      β.binderInfo == .implicit && α.type == .sort (.succ .zero) && β.type == .sort (.succ .zero) &&
      inst.binderInfo == .instImplicit &&
      inst.type == mkApp (mkConst ``Nonempty [.succ .zero]) args[0]! do
    return #["expected independent α and β with exactly the Nonempty α instance"]
  return #[]

private def ensureBinder (arg : Expr) (name : Name) (type : Expr) : MetaM (Array String) := do
  let decl ← arg.fvarId!.getDecl
  unless decl.userName == name && decl.binderInfo == .default && decl.type == type do
    return #[s!"binder {name} has an unexpected name, visibility or type"]
  return #[]

/-- Check that the generic wrapper delegates to `joinEnv` on the exact maps. -/
def joinEnvLocalsWrapperProblems (info : DefinitionVal) : MetaM (Array String) := do
  lambdaTelescope info.value fun args body => do
    unless args.size == 5 do return #["wrapper must have exactly five binders"]
    let header ← typeHeaderProblems args
    unless header.isEmpty do return header
    let spt := mkConst `Flapjack.Spt
    let left := mkApp spt args[0]!
    let right := mkApp spt args[1]!
    let l ← ensureBinder args[3]! `sl left
    let r ← ensureBinder args[4]! `tl right
    unless l.isEmpty && r.isEmpty do return l ++ r
    let adjusted ← mkAppM `Flapjack.Compiler.Backend.DataToWord.adjustSet #[args[3]!]
    let intersection ← mkAppM `Flapjack.sptInter #[args[4]!, adjusted]
    let alist ← mkAppM `Flapjack.sptToAList #[intersection]
    let expected ← mkAppM joinEnvName #[args[3]!, alist]
    unless body == expected do return #["wrapper must directly call reviewed joinEnv on the exact intersection"]
    return #[]

/-- Check all binders, the odd premise, and the full equality of one theorem. -/
def joinEnvLocalsTheoremProblems (type : Expr) (destination : Bool) : MetaM (Array String) := do
  forallTelescope type fun args result => do
    unless args.size == (if destination then 10 else 8) do
      return #["theorem has an unexpected number of binders"]
    let header ← typeHeaderProblems args
    unless header.isEmpty do return header
    let spt := mkConst `Flapjack.Spt
    let mut expected : Array (Name × Expr) := #[(`n, mkConst ``Nat), (`sl, mkApp spt args[0]!)]
    if destination then expected := expected ++ #[(`dest, mkConst ``Nat), (`w, args[1]!)]
    expected := expected ++ #[(`v, args[1]!), (`ls, mkApp spt args[1]!)]
    for i in [0:expected.size] do
      let (name, ty) := expected[i]!
      let problems ← ensureBinder args[i + 3]! name ty
      unless problems.isEmpty do return problems
    let n := args[3]!
    let sl := args[4]!
    let ls := args[args.size - 2]!
    let v := args[args.size - 3]!
    let odd ← args[args.size - 1]!.fvarId!.getDecl
    let mod ← mkAppM ``Nat.mod #[n, mkNatLit 2]
    let oddExpected ← mkEq mod (mkNatLit 1)
    unless odd.userName == `odd && odd.binderInfo == .default && (← isDefEq odd.type oddExpected) do
      return #["theorem must retain the original odd-key premise"]
    let inserted ← mkAppM `Flapjack.sptInsert #[n, v, ls]
    let (leftTree, rightTree) ← if destination then do
      let dest ← mkAppM `Flapjack.Compiler.Backend.DataToWord.adjustVar #[args[5]!]
      pure (← mkAppM `Flapjack.sptInsert #[dest, args[6]!, inserted],
        ← mkAppM `Flapjack.sptInsert #[dest, args[6]!, ls])
    else pure (inserted, ls)
    let left ← mkAppM joinEnvLocalsName #[sl, leftTree]
    let right ← mkAppM joinEnvLocalsName #[sl, rightTree]
    let expectedResult ← mkEq left right
    unless result == expectedResult do return #["theorem must state the exact joined-local equality"]
    return #[]

/-- Check the exact target, reviewed producer and statement/body; the caller must
also verify each declaration's HOL reference and the manifest. -/
def joinEnvLocalsBundleProblems (target : Name) : MetaM (Array String) := do
  let definition := joinEnvLocalsName
  let odd := `Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.joinEnvLocals_insertOdd
  let destination := `Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.joinEnvLocals_insertDestOdd
  unless #[definition, odd, destination].contains target do return #["unexpected transitive THE target"]
  let env ← getEnv
  let producerRef : HolRef := {
    path := "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml", name := "join_env_def",
    totalFunctionInhabitants := #["α"] }
  unless HolRef.get? env joinEnvName == some producerRef do
    return #["joinEnv must retain its reviewed HOL THE reference"]
  let wrapperRef : HolRef := {
    path := "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml", name := "join_env_locals_def",
    totalFunctionInhabitants := #["α"] }
  unless HolRef.get? env definition == some wrapperRef do
    return #["joinEnvLocals must retain its reviewed HOL reference"]
  let producerOwner := match env.getModuleIdxFor? joinEnvName with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  unless producerOwner == gcNamespace ++ `StackRel do
    return #["joinEnv has the wrong defining module"]
  let mut problems : Array String := #[]
  for name in #[definition, target] do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    if owner != gcNamespace ++ `JoinEnvLocals then
      problems := problems.push s!"{name} has the wrong defining module"
    match env.find? name with
    | some (.defnInfo info) =>
      if name != definition || !info.levelParams.isEmpty then
        problems := problems.push s!"{name} must be the monomorphic wrapper"
      else problems := problems ++ (← joinEnvLocalsWrapperProblems info)
    | some (.thmInfo info) =>
      if name == definition || !info.levelParams.isEmpty then
        problems := problems.push s!"{name} must be a monomorphic theorem"
      else problems := problems ++ (← joinEnvLocalsTheoremProblems info.type (name == destination))
    | _ => problems := problems.push s!"{name} has the wrong declaration kind"
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        problems := problems.push s!"{name} depends on unexpected axiom {axiomName}"
  return problems

end Flapjack
