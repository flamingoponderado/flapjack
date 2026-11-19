module

public meta import Lean

public meta section

/-! Audit the independent, unused existential types in `state_rel_gc_gen`.
This checks only HOL type inhabitance; it does not establish correspondence
of the rest of the theorem to its HOL statement. -/
namespace Flapjack
open Lean Meta

private def containsFVar (e f : Expr) : Bool :=
  (e.find? (fun x => x == f)).isSome

/-- Inspect reducible aliases as well as their written arguments. The checker
    remains a structural guard, not a substitute for reviewing the statement. -/
private partial def containsInhabitation (e : Expr) : MetaM Bool := do
  if e.isConstOf ``Nonempty || e.isConstOf ``Inhabited then return true
  if let some name := e.getAppFn.constName? then
    if let some (.defnInfo info) := (← getEnv).find? name then
      if info.hints == .abbrev then
        if let some expanded ← withTransparency .reducible (unfoldDefinition? e) then
          if ← containsInhabitation expanded then return true
  match e with
  | .app f a => return (← containsInhabitation f) || (← containsInhabitation a)
  | .lam _ t b _ | .forallE _ t b _ =>
      return (← containsInhabitation t) || (← containsInhabitation b)
  | .letE _ t v b _ =>
      return (← containsInhabitation t) || (← containsInhabitation v) || (← containsInhabitation b)
  | .mdata _ b | .proj _ _ b => containsInhabitation b
  | _ => return false

private partial def scanExists (result : Expr) (carriers : Array (Name × Name × Expr))
    (seen : Array Name := #[]) : MetaM (Array String) := do
  let e := result.consumeMData
  if e.getAppFn.isConstOf ``Exists then
    let args := e.getAppArgs
    unless args.size == 2 do return #["malformed Exists"]
    let .lam name domain body _ := args[1]!.consumeMData
      | return #["Exists predicate must be a lambda"]
    if ← containsInhabitation domain then return #["existential domain contains inhabitance"]
    let mut next := seen
    match carriers.find? (fun (_, witness, _) => witness == name) with
    | some (carrierName, _, carrier) =>
      if seen.contains name then return #[s!"duplicate witness {name}"]
      unless domain == carrier && args[0]! == carrier do
        return #[s!"witness {name} must directly have carrier {carrierName}"]
      if body.hasLooseBVar 0 then return #[s!"witness {name} must be unused"]
      next := seen.push name
    | none =>
      for (carrierName, _, carrier) in carriers do
        if containsFVar domain carrier then
          return #[s!"carrier {carrierName} occurs in another existential domain"]
    withLocalDeclD name domain fun x => scanExists (body.instantiate1 x) carriers next
  else
    for (carrierName, witnessName, carrier) in carriers do
      unless seen.contains witnessName do return #[s!"missing witness {witnessName}"]
      if containsFVar e carrier then return #[s!"carrier {carrierName} occurs in conclusion"]
    if ← containsInhabitation e then return #["conclusion contains an inhabitance assumption"]
    return #[]

/-- Check that the HOL-only types occur solely as unused existential domains,
    with one canonical inhabitance instance for each type. -/
def stateRelGcInhabitantProblems (type : Expr) : MetaM (Array String) := do
  forallTelescope type fun args result => do
    let pairs : Array (Name × Name) := #[(`T2, `_t2), (`W1, `_w1), (`W2, `_w2)]
    let mut carriers : Array (Name × Name × Expr) := #[]
    for (carrierName, witnessName) in pairs do
      let foundBinders ← args.filterM fun a => do
        pure ((← a.fvarId!.getDecl).userName == carrierName)
      unless foundBinders.size == 1 do return #[s!"carrier {carrierName} must occur once"]
      let carrier := foundBinders[0]!
      let decl ← carrier.fvarId!.getDecl
      unless (match decl.type.consumeMData with | .sort (.succ _) => true | _ => false) &&
          decl.binderInfo == .implicit do
        return #[s!"carrier {carrierName} must be an implicit Type binder"]
      carriers := carriers.push (carrierName, witnessName, carrier)
    let mut counts : Array Nat := #[0, 0, 0]
    for arg in args do
      let decl ← arg.fvarId!.getDecl
      let ty := decl.type.consumeMData
      if ty.isSort && !#[`C, `F, `T2, `W1, `W2].contains decl.userName then
        return #[s!"unexpected type or proposition binder {decl.userName}"]
      if ty.getAppFn.isConstOf ``Nonempty then
        unless decl.binderInfo == .instImplicit && ty.getAppArgs.size == 1 do
          return #["inhabitance must be an instance binder"]
        let value := ty.getAppArgs[0]!
        let some i := carriers.toList.findIdx? (fun (_, _, carrier) => carrier == value)
          | return #["unlisted inhabitance instance"]
        counts := counts.set! i (counts[i]! + 1)
      else
        if ← containsInhabitation ty then return #["nested or noncanonical inhabitance"]
        for (carrierName, _, carrier) in carriers do
          if containsFVar ty carrier then return #[s!"carrier {carrierName} used outside its instance and witness"]
    unless counts == #[1, 1, 1] do return #["each carrier needs exactly one Nonempty instance"]
    scanExists result carriers

private partial def exactExistsProblems (result : Expr) (expected : Array (Name × Expr))
    (index : Nat := 0) : MetaM (Array String) := do
  let e := result.consumeMData
  if index == expected.size then
    if e.getAppFn.isConstOf ``Exists then return #["unexpected extra existential binder"]
    return #[]
  unless e.getAppFn.isConstOf ``Exists && e.getAppArgs.size == 2 do
    return #[s!"missing existential binder at position {index + 1}"]
  let .lam name domain body _ := e.getAppArgs[1]!.consumeMData
    | return #["existential predicate must be a lambda"]
  let (wantedName, wantedType) := expected[index]!
  unless name == wantedName && (← isDefEq domain wantedType) do
    return #[s!"existential binder {index + 1} has the wrong name or type"]
  withLocalDeclD name domain fun x => exactExistsProblems (body.instantiate1 x) expected (index + 1)

/-- Check the target's entire outer telescope before applying the inhabitance
    audit. This deliberately accepts only this theorem's binder order; it does
    not attempt to establish the remaining statement's HOL correspondence. -/
def stateRelGcTelescopeProblems (type : Expr) : MetaM (Array String) := do
  forallTelescope type fun args result => do
    unless args.size == 19 do return #["expected exactly nineteen outer binders"]
    let names : Array (Option Name) := #[some `width, none, some `C, some `F,
      some `T2, some `W1, some `W2, none, none, none, some `conf, some `l1,
      some `l2, some `s, some `t, some `locs, some `k, some `related, some `premises]
    for i in [0:19] do
      let decl ← args[i]!.fvarId!.getDecl
      if let some name := names[i]! then
        unless decl.userName == name do return #[s!"unexpected binder at position {i + 1}"]
      let expectedInfo := if i == 1 || (7 ≤ i && i ≤ 9) then .instImplicit
        else if i == 0 || (2 ≤ i && i ≤ 6) then .implicit else .default
      unless decl.binderInfo == expectedInfo do
        return #[s!"unexpected binder visibility at position {i + 1}"]
      if 2 ≤ i && i ≤ 6 then
        unless decl.type.consumeMData == .sort (.succ .zero) do
          return #[s!"binder {decl.userName} must be a Type"]
    let width ← args[0]!.fvarId!.getDecl
    unless width.type == mkConst ``Nat do return #["width must have type Nat"]
    let positive ← args[1]!.fvarId!.getDecl
    let expectedPositive ← mkAppM ``NeZero #[args[0]!]
    unless positive.type == expectedPositive do
      return #["width must have its own NeZero instance"]
    let width := args[0]!
    let inst := args[1]!
    let c := args[2]!
    let f := args[3]!
    let conf := args[10]!
    let l1 := args[11]!
    let l2 := args[12]!
    let s := args[13]!
    let t := args[14]!
    let locs := args[15]!
    let k := args[16]!
    let value := mkConst `Flapjack.Compiler.Backend.DataSem.Value
    let wordLoc := mkApp2 (mkConst `Flapjack.WordLocW) width inst
    let noneType := mkApp (mkConst ``List [0]) (mkApp2 (mkConst ``Prod [0, 0]) value wordLoc)
    let none := mkApp (mkConst ``Option.none [0]) noneType
    let expectedRel := mkAppN (mkConst `Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.stateRel)
      #[width, inst, c, f, conf, l1, l2, s, t, none, locs]
    let related ← args[17]!.fvarId!.getDecl
    unless related.type == expectedRel do return #["related must be the exact state relation premise"]
    let store := mkAppN (mkConst `Flapjack.WordSemStateFiniteExact.store) #[width, inst, c, f, t]
    let allocSize := mkApp (mkConst `Flapjack.WordStore.allocSize [0]) (mkConst ``Unit)
    let lookup := mkAppN (mkConst `Flapjack.HolFiniteMapExact.lookup)
      #[mkConst `Flapjack.WordStoreHOL, wordLoc, store, allocSize]
    let allocation := mkAppN (mkConst `Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.gcAllocSize)
      #[width, inst, k]
    let word := mkAppN (mkConst `Flapjack.WordLocW.word) #[width, inst, allocation]
    let someWord := mkApp2 (mkConst ``Option.some [0]) wordLoc word
    let allocEq ← mkEq lookup someWord
    let sourceLocals := mkAppN (mkConst `Flapjack.Compiler.Backend.DataSem.State.locals) #[c, f, s]
    let sourceEmpty := mkApp (mkConst `Flapjack.Spt.ln) value
    let sourceEq ← mkEq sourceLocals sourceEmpty
    let targetLocals := mkAppN (mkConst `Flapjack.WordSemStateFiniteExact.locals) #[width, inst, c, f, t]
    let location := mkAppN (mkConst `Flapjack.WordLocW.loc) #[width, inst, l1, l2]
    let targetSingle := mkApp2 (mkConst `Flapjack.Spt.ls) wordLoc location
    let targetEq ← mkEq targetLocals targetSingle
    let expectedPremises := mkApp2 (mkConst ``And) allocEq (mkApp2 (mkConst ``And) sourceEq targetEq)
    let premises ← args[18]!.fvarId!.getDecl
    unless premises.type == expectedPremises do return #["premises must be the exact three GC premises"]
    let memory ← mkArrow (mkApp (mkConst ``BitVec) width) wordLoc
    let map := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) (mkConst `Flapjack.WordStoreHOL) wordLoc
    let frame := mkApp2 (mkConst `Flapjack.WordSemStackFrame) width inst
    let expected := #[(`_t2, args[4]!), (`wl, mkApp (mkConst ``List [0]) wordLoc),
      (`m, memory), (`st, map), (`_w1, args[5]!), (`_w2, args[6]!),
      (`stack, mkApp (mkConst ``List [0]) frame)]
    let existentialProblems ← exactExistsProblems result expected
    unless existentialProblems.isEmpty do return existentialProblems
    stateRelGcInhabitantProblems type


end Flapjack
