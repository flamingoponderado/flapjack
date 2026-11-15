module

public meta import Lean
public meta import Flapjack.HolRef.TmcUniversalBinder

public meta section

/-! Preliminary checks for the telescope and premise of the TMC call-block
simulation. The conclusion, witness proofs and HOL correspondence require
separate checks before any qualifier may use this audit. -/

namespace Flapjack
open Lean Meta

/-- Compare the complete outer telescope and the seven premise conjuncts of
`evaluate_cb`. This is not a check of its conclusion or a HOL equivalence proof. -/
def tmcCallBlockPremiseProblems (type : Expr) : MetaM (Array String) := do
  forallTelescope type fun args _ => do
    unless args.size == 15 do return #["call-block theorem has the wrong outer telescope"]
    let nat := mkConst `Nat
    let c := args[0]!
    let ffi := args[1]!
    let pair := mkApp2 (mkConst `Prod [Level.zero, Level.zero]) nat c
    let state (cfg : Expr) := mkApp2 (mkConst `Flapjack.Compiler.Backend.BviSem.BviState) cfg ffi
    let value := mkConst `Flapjack.Compiler.Backend.BvlSem.Value
    let values := mkApp (mkConst `List [Level.zero]) value
    let map := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) nat nat
    let resultType := mkConst `Flapjack.Compiler.Backend.BviSem.BviResult
    let names := #[`C, `F, `A, `cb, `loc, `f, `opt, `env1, `env2, `source, `target,
      `final, `result, `clock]
    let types := #[mkSort (Level.succ Level.zero), mkSort (Level.succ Level.zero),
      mkSort (Level.succ Level.zero), mkConst `Flapjack.Compiler.Backend.BviTmc.CallBlock,
      nat, map, mkConst `Bool, values, values, state pair, state c, state pair, resultType, nat]
    for i in [:names.size] do
      let binder ← args[i]!.fvarId!.getDecl
      let visibility := if i < 3 then BinderInfo.implicit else BinderInfo.default
      unless binder.userName == names[i]! && binder.binderInfo == visibility && binder.type == types[i]! do
        return #[s!"call-block outer binder {i} has the wrong name, visibility or carrier"]
    let premise ← args[14]!.fvarId!.getDecl
    unless premise.userName == `h && premise.binderInfo == .default do
      return #["call-block theorem has the wrong premise binder"]
    let mut clauses := #[]
    let mut rest := premise.type
    for _ in [:6] do
      match rest with
      | .app (.app (.const ``And []) first) tail =>
        clauses := clauses.push first
        rest := tail
      | _ => return #["call-block premise must contain seven conjuncts"]
    clauses := clauses.push rest
    let cb := args[3]!
    let loc := args[4]!
    let f := args[5]!
    let opt := args[6]!
    let env1 := args[7]!
    let env2 := args[8]!
    let source := args[9]!
    let target := args[10]!
    let final := args[11]!
    let result := args[12]!
    let clock := args[13]!
    let exp := mkConst `Flapjack.Compiler.Backend.Bvi.Exp
    let block := mkApp2 (mkConst `Flapjack.Compiler.Backend.BviTmc.callBlockToBvi) loc cb
    let singleton := mkApp3 (mkConst `List.cons [Level.zero]) exp block (mkApp (mkConst `List.nil [Level.zero]) exp)
    let evaluation := mkAppN (mkConst `Flapjack.Compiler.Backend.BviSem.evaluate)
      #[pair, ffi, singleton, env1, source]
    let output := mkAppN (mkConst `Prod.mk [Level.zero, Level.zero]) #[resultType, state pair, result, final]
    let run := mkApp3 (mkConst ``Eq [Level.succ Level.zero])
      (mkApp2 (mkConst `Flapjack.Compiler.Backend.BviSem.EvalResult) pair ffi) evaluation output
    let length := mkApp2 (mkConst `List.length [Level.zero]) value env1
    let wf := mkApp2 (mkConst `Flapjack.Compiler.Backend.BviTmc.wfBlock) length cb
    let env := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.envRel) #[opt, f, env1, env2]
    let states := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.stateRel) #[c, ffi, f, source, target]
    let sourceClock := mkAppN (mkConst `Flapjack.Compiler.Backend.BviSem.BviState.clock) #[pair, ffi, source]
    let bound := mkAppN (mkConst `LE.le [Level.zero]) #[nat, mkConst `instLENat, sourceClock, clock]
    let errorType := mkConst `Flapjack.Compiler.Backend.BviSem.ExnOrRet
    let abort := mkApp2 (mkConst `Flapjack.SemanticPrimitivesHOL.ErrorResult.abort)
      errorType (mkConst `Flapjack.SemanticPrimitivesHOL.Abort.typeError)
    let typeError := mkApp3 (mkConst `Flapjack.SemanticPrimitivesHOL.Result.err) values errorType abort
    let safe := mkApp3 (mkConst ``Ne [Level.succ Level.zero]) resultType result typeError
    unless clauses.extract 0 6 == #[run, wf, env, states, bound, safe] do
      return #["call-block evaluation, well-formedness, relations, clock or error premise changed"]
    let hypothesisProblems ← forallTelescope clauses[6]! fun boundVars conclusion => do
      unless boundVars.size == 2 do return #["call-block induction premise has the wrong binders"]
      let xs ← boundVars[0]!.fvarId!.getDecl
      let s ← boundVars[1]!.fvarId!.getDecl
      let expressions := mkApp (mkConst `List [Level.zero]) exp
      unless xs.userName == `xs && xs.binderInfo == .default && xs.type == expressions &&
          s.userName == `s && s.binderInfo == .default && s.type == state pair do
        return #["call-block induction premise has the wrong carriers"]
      let expected := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.Induction.hypothesis)
        #[c, ffi, boundVars[0]!, boundVars[1]!, clock]
      unless conclusion == expected do return #["call-block induction predicate changed"]
      return #[]
    return hypothesisProblems

/-- Check the ordinary, non-optimized branch of the call-block simulation.
The optimized wrapper and worker branches require separate checks. -/
def tmcCallBlockOrdinaryProblems (type : Expr) : MetaM (Array String) := do
  let premiseProblems ← tmcCallBlockPremiseProblems type
  unless premiseProblems.isEmpty do return premiseProblems
  forallTelescope type fun args conclusion => do
    let .app (.app (.const ``And []) ordinary) _ := conclusion
      | return #["call-block theorem must contain ordinary and optimized branches"]
    let c := args[0]!
    let ffi := args[1]!
    let cb := args[3]!
    let loc := args[4]!
    let f := args[5]!
    let env2 := args[8]!
    let target := args[10]!
    let final := args[11]!
    let result := args[12]!
    let nat := mkConst `Nat
    let exp := mkConst `Flapjack.Compiler.Backend.Bvi.Exp
    let state := mkApp2 (mkConst `Flapjack.Compiler.Backend.BviSem.BviState) c ffi
    let resultType := mkConst `Flapjack.Compiler.Backend.BviSem.BviResult
    let map := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) nat nat
    let block := mkApp2 (mkConst `Flapjack.Compiler.Backend.BviTmc.callBlockToBvi) loc cb
    let program := mkApp3 (mkConst `List.cons [Level.zero]) exp block (mkApp (mkConst `List.nil [Level.zero]) exp)
    tmcExists ordinary resultType `r fun r afterResult =>
      tmcExists afterResult state `s fun s afterState =>
        tmcExists afterState map `ordinaryMap fun nextMap body => do
          let mut clauses := #[]
          let mut rest := body
          for _ in [:6] do
            match rest with
            | .app (.app (.const ``And []) first) tail =>
              clauses := clauses.push first
              rest := tail
            | _ => return #["ordinary call-block branch must contain seven conjuncts"]
          clauses := clauses.push rest
          unless clauses == tmcResultFrame c ffi program env2 target final result f s nextMap r do
            return #["ordinary call-block simulation changed"]
          return #[]

/-- Check the optimized-code guard and wrapper branch. The auxiliary and
worker branches remain outside this preliminary audit. -/
def tmcCallBlockWrapperProblems (type : Expr) : MetaM (Array String) := do
  let ordinaryProblems ← tmcCallBlockOrdinaryProblems type
  unless ordinaryProblems.isEmpty do return ordinaryProblems
  forallTelescope type fun args conclusion => do
    let .app (.app (.const ``And []) _) optimized := conclusion
      | return #["call-block theorem must contain ordinary and optimized branches"]
    let nat := mkConst `Nat
    let c := args[0]!
    let ffi := args[1]!
    let pair := mkApp2 (mkConst `Prod [Level.zero, Level.zero]) nat c
    let state (cfg : Expr) := mkApp2 (mkConst `Flapjack.Compiler.Backend.BviSem.BviState) cfg ffi
    let cb := args[3]!
    let loc := args[4]!
    let f := args[5]!
    let env2 := args[8]!
    let source := args[9]!
    let target := args[10]!
    let final := args[11]!
    let result := args[12]!
    let code (cfg s : Expr) := mkAppN (mkConst `Flapjack.Compiler.Backend.BviSem.BviState.code) #[cfg, ffi, s]
    forallTelescope optimized fun destArgs body => do
      unless destArgs.size == 2 do return #["optimized call-block branch has the wrong telescope"]
      let dest ← destArgs[0]!.fvarId!.getDecl
      let codePremise ← destArgs[1]!.fvarId!.getDecl
      let expectedCode := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.optimisedCode)
        #[loc, destArgs[0]!, code pair source, code c target]
      unless dest.userName == `dest && dest.binderInfo == .default && dest.type == nat &&
          codePremise.binderInfo == .default && codePremise.type == expectedCode do
        return #["optimized call-block code guard changed"]
      let .app (.app (.const ``And []) wrapper) _ := body
        | return #["optimized call-block branch is missing the wrapper"]
      forallTelescope wrapper fun wrapArgs wrapBody => do
        unless wrapArgs.size == 5 do return #["wrapper branch has the wrong telescope"]
        let cbType := mkConst `Flapjack.Compiler.Backend.BviTmc.CallBlock
        let natList := mkApp (mkConst `List [Level.zero]) nat
        let names := #[`tag, `left, `child, `right]
        let types := #[nat, natList, cbType, natList]
        for i in [:names.size] do
          let binder ← wrapArgs[i]!.fvarId!.getDecl
          unless binder.userName == names[i]! && binder.binderInfo == .default && binder.type == types[i]! do
            return #[s!"wrapper binder {i} has the wrong name, visibility or carrier"]
        let shape ← wrapArgs[4]!.fvarId!.getDecl
        let constructor := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.CallBlock.callBlock)
          #[wrapArgs[0]!, wrapArgs[1]!, wrapArgs[2]!, wrapArgs[3]!]
        let expectedShape := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) cbType cb constructor
        unless shape.binderInfo == .default && shape.type == expectedShape do
          return #["wrapper constructor premise changed"]
        let map := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) nat nat
        let resultType := mkConst `Flapjack.Compiler.Backend.BviSem.BviResult
        let exp := mkConst `Flapjack.Compiler.Backend.Bvi.Exp
        let wrap := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.wrapperBlockSource)
          #[wrapArgs[0]!, wrapArgs[1]!, wrapArgs[2]!, wrapArgs[3]!, destArgs[0]!]
        let program := mkApp3 (mkConst `List.cons [Level.zero]) exp wrap (mkApp (mkConst `List.nil [Level.zero]) exp)
        tmcExists wrapBody (state c) `s fun next afterState =>
          tmcExists afterState map `wrapMap fun nextMap afterMap =>
            tmcExists afterMap resultType `r fun nextResult resultBody => do
              let mut clauses := #[]
              let mut rest := resultBody
              for _ in [:6] do
                match rest with
                | .app (.app (.const ``And []) first) tail =>
                  clauses := clauses.push first
                  rest := tail
                | _ => return #["wrapper branch must contain seven conjuncts"]
              clauses := clauses.push rest
              unless clauses == tmcResultFrame c ffi program env2 target final result f next nextMap nextResult do
                return #["wrapper call-block simulation changed"]
              return #[]

end Flapjack
