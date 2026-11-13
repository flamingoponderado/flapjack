module

public meta import Lean

public meta section

/-! Prospective elaborated validation for the closure-to-BVL simulation
definition. This check is unconnected to `@[hol]`; ownership, the declaration
signature, codec representations and source correspondence are separate. -/

namespace Flapjack
open Lean Meta

private def simulationExists (expression domain : Expr) (label : String)
    (next : Expr → Expr → MetaM (Array String)) : MetaM (Array String) := do
  let .app (.app (.const ``Exists [Level.succ Level.zero]) actualDomain) predicate := expression
    | return #[s!"{label} must be an existential"]
  unless actualDomain == domain do return #[s!"{label} has the wrong existential carrier"]
  lambdaTelescope predicate fun args body => do
    unless args.size == 1 do return #[s!"{label} must bind exactly one variable"]
    let d ← args[0]!.fvarId!.getDecl
    unless d.binderInfo == BinderInfo.default && d.type == domain do
      return #[s!"{label} has the wrong existential binder"]
    next args[0]! body

private def simulationTrueRelationProblems (relation first second : Expr) : MetaM (Array String) :=
  lambdaTelescope relation fun args body => do
    unless args.size == 2 do return #["result relation must bind two values"]
    let a ← args[0]!.fvarId!.getDecl
    let b ← args[1]!.fvarId!.getDecl
    unless a.binderInfo == BinderInfo.default && b.binderInfo == BinderInfo.default &&
        a.type == first && b.type == second && body == mkConst ``True do
      return #["result relation must be the unconditional true relation"]
    return #[]

/-- Check the full unreduced evaluation-simulation definition body, including
its source premise, target existential, result relation and complete FFI
equality. The caller must first check the actual declaration's owner, kind,
signature, codec, axioms and source correspondence. This function does not
enable a HOL qualifier. -/
def predicateDomainSimulationBodyProblems (type value : Expr) : MetaM (Array String) := do
  unless ← isDefEq (← inferType value) type do
    return #["simulation body does not have the declaration type"]
  lambdaTelescope value fun args body => do
    unless args.size == 14 do return #["simulation body must have exactly fourteen parameters"]
    for i in [:args.size] do
      let d ← args[i]!.fvarId!.getDecl
      let expected := if i < 3 then BinderInfo.implicit else BinderInfo.default
      unless d.binderInfo == expected do return #[s!"simulation parameter {i} has the wrong visibility"]
    let c₁ := args[0]!
    let c₂ := args[1]!
    let ffiType := args[2]!
    let nat := mkConst `Nat
    let sourceValue := mkConst `Flapjack.Compiler.Backend.ClosSem.Value
    let targetValue := mkConst `Flapjack.Compiler.Backend.BvlSem.Value
    let targetExp := mkConst `Flapjack.Compiler.Backend.Bvl.Exp
    let list (t : Expr) := mkApp (mkConst `List [Level.zero]) t
    let nil (t : Expr) := mkApp (mkConst `List.nil [Level.zero]) t
    let sourceResult := mkApp2 (mkConst `Flapjack.SemanticPrimitivesHOL.Result) (list sourceValue) sourceValue
    let targetResult := mkApp2 (mkConst `Flapjack.SemanticPrimitivesHOL.Result) (list targetValue) targetValue
    let sourceState := mkApp2 (mkConst `Flapjack.Compiler.Backend.ClosSem.State) c₁ ffiType
    let targetState := mkApp2 (mkConst `Flapjack.Compiler.Backend.BvlSem.State) c₂ ffiType
    forallTelescope body fun premiseArgs conclusion => do
      unless premiseArgs.size == 4 do return #["source simulation must bind clock, result, state and premise"]
      let expectedDomains := #[nat, sourceResult, sourceState]
      for i in [:premiseArgs.size] do
        let d ← premiseArgs[i]!.fvarId!.getDecl
        unless d.binderInfo == BinderInfo.default do
          return #[s!"source simulation binder {i} must be explicit"]
        if i < 3 && d.type != expectedDomains[i]! then
          return #[s!"source simulation binder {i} has the wrong type"]
      let k := premiseArgs[0]!
      let res₁ := premiseArgs[1]!
      let s₂ := premiseArgs[2]!
      let sourceInitial := mkAppN (mkConst `Flapjack.Compiler.Backend.ClosSem.initialState)
        #[c₁, ffiType, args[3]!, args[4]!, args[5]!, args[6]!, args[7]!, k]
      let sourceEval := mkAppN (mkConst `Flapjack.Compiler.Backend.ClosSem.evaluate)
        #[c₁, ffiType, args[8]!, nil sourceValue, sourceInitial]
      let sourcePair := mkAppN (mkConst `Prod.mk [Level.zero, Level.zero])
        #[sourceResult, sourceState, res₁, s₂]
      let sourceEq := mkApp3 (mkConst `Eq [Level.succ Level.zero])
        (mkApp2 (mkConst `Flapjack.Compiler.Backend.ClosSem.EvalResult) c₁ ffiType) sourceEval sourcePair
      let typeError := mkApp3 (mkConst `Flapjack.SemanticPrimitivesHOL.Result.err)
        (list sourceValue) sourceValue
        (mkApp2 (mkConst `Flapjack.SemanticPrimitivesHOL.ErrorResult.abort) sourceValue
          (mkConst `Flapjack.SemanticPrimitivesHOL.Abort.typeError))
      let safe := mkApp3 (mkConst `Ne [Level.succ Level.zero]) sourceResult res₁ typeError
      let relation := mkAppN args[13]!
        #[args[5]!, args[6]!, args[7]!, args[8]!, args[9]!, args[10]!, args[11]!, args[12]!]
      let premise := mkApp2 (mkConst ``And) sourceEq (mkApp2 (mkConst ``And) safe relation)
      let premiseDecl ← premiseArgs[3]!.fvarId!.getDecl
      unless premiseDecl.type == premise do return #["source evaluation, safety or relation premise changed"]
      simulationExists conclusion nat "target clock" fun ck afterClock =>
        simulationExists afterClock targetResult "target result" fun res₂ afterResult =>
          simulationExists afterResult targetState "target state" fun t₂ targetConclusion => do
            let .app (.app (.const ``And []) evaluation) (.app (.app (.const ``And []) related) ffiEquality) :=
                targetConclusion
              | return #["target conclusion must contain evaluation, result relation and FFI equality"]
            let zero := mkAppN (mkConst `OfNat.ofNat [Level.zero])
              #[nat, Expr.lit (.natVal 0), mkApp (mkConst `instOfNatNat) (Expr.lit (.natVal 0))]
            let start := mkApp2 (mkConst `Option.some [Level.zero]) nat args[12]!
            let call := mkApp3 (mkConst `Flapjack.Compiler.Backend.Bvl.Exp.call) zero start (nil targetExp)
            let program := mkApp3 (mkConst `List.cons [Level.zero]) targetExp call (nil targetExp)
            let addInstance := mkApp2 (mkConst `instHAdd [Level.zero]) nat (mkConst `instAddNat)
            let clock := mkAppN (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero])
              #[nat, nat, nat, addInstance, k, ck]
            let targetInitial := mkAppN (mkConst `Flapjack.Compiler.Backend.BvlSem.initialState)
              #[c₂, ffiType, args[3]!, args[9]!, args[10]!, args[11]!, clock]
            let targetEval := mkAppN (mkConst `Flapjack.Compiler.Backend.BvlSem.evaluate)
              #[c₂, ffiType, program, nil targetValue, targetInitial]
            let targetPair := mkAppN (mkConst `Prod.mk [Level.zero, Level.zero])
              #[targetResult, targetState, res₂, t₂]
            let targetEq := mkApp3 (mkConst `Eq [Level.succ Level.zero])
              (mkApp2 (mkConst `Flapjack.Compiler.Backend.BvlSem.EvalResult) c₂ ffiType) targetEval targetPair
            unless evaluation == targetEq do return #["target evaluation or clock changed"]
            unless related.isAppOfArity `Flapjack.SemanticPrimitivesProps.resultRel 8 do
              return #["target result relation has the wrong head or arity"]
            let relArgs := related.getAppArgs
            unless relArgs[0]! == list sourceValue && relArgs[1]! == list targetValue &&
                relArgs[2]! == sourceValue && relArgs[3]! == targetValue &&
                relArgs[6]! == res₁ && relArgs[7]! == res₂ do
              return #["target result relation has the wrong carriers or values"]
            let listRelErrors ← simulationTrueRelationProblems relArgs[4]! (list sourceValue) (list targetValue)
            let valueRelErrors ← simulationTrueRelationProblems relArgs[5]! sourceValue targetValue
            unless listRelErrors.isEmpty && valueRelErrors.isEmpty do return listRelErrors ++ valueRelErrors
            let sourceFfi := mkAppN (mkConst `Flapjack.Compiler.Backend.ClosSem.State.ffi) #[c₁, ffiType, s₂]
            let targetFfi := mkAppN (mkConst `Flapjack.Compiler.Backend.BvlSem.State.ffi) #[c₂, ffiType, t₂]
            let expectedFfi := mkApp3 (mkConst `Eq [Level.succ Level.zero])
              (mkApp (mkConst `Flapjack.HolFfiState [Level.zero]) ffiType) sourceFfi targetFfi
            unless ffiEquality == expectedFfi do return #["complete FFI equality changed"]
            return #[]

end Flapjack
