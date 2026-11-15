module

public meta import Lean

public meta section

/-! Preliminary elaborated check for the body-bound map in the TMC
induction hypothesis. This does not enable a HOL qualifier: the complete
predicate body, existential scopes, codec witnesses and source correspondence
still require separate checks. -/

namespace Flapjack
open Lean Meta

private def tmcExists (expression domain : Expr) (name : Name)
    (next : Expr → Expr → MetaM (Array String)) : MetaM (Array String) := do
  let .app (.app (.const ``Exists [Level.succ Level.zero]) actualDomain) predicate := expression
    | return #[s!"{name} must be an existential"]
  unless actualDomain == domain do return #[s!"{name} has the wrong carrier"]
  lambdaTelescope predicate fun args body => do
    unless args.size == 1 do return #[s!"{name} must bind one value"]
    let binder ← args[0]!.fvarId!.getDecl
    unless binder.userName == name && binder.binderInfo == .default && binder.type == domain do
      return #[s!"{name} has the wrong binder"]
    next args[0]! body

private def tmcResultFrame (c ffi program environment target final result map next nextMap nextResult : Expr) : Array Expr := Id.run do
  let nat := mkConst `Nat
  let state := mkApp2 (mkConst `Flapjack.Compiler.Backend.BviSem.BviState) c ffi
  let value := mkConst `Flapjack.Compiler.Backend.BvlSem.Value
  let values := mkApp (mkConst `List [Level.zero]) value
  let errorType := mkConst `Flapjack.Compiler.Backend.BviSem.ExnOrRet
  let resultType := mkConst `Flapjack.Compiler.Backend.BviSem.BviResult
  let targetEval := mkAppN (mkConst `Flapjack.Compiler.Backend.BviSem.evaluate)
    #[c, ffi, program, environment, target]
  let targetOutput := mkAppN (mkConst `Prod.mk [Level.zero, Level.zero])
    #[resultType, state, nextResult, next]
  let targetRun := mkApp3 (mkConst ``Eq [Level.succ Level.zero])
    (mkApp2 (mkConst `Flapjack.Compiler.Backend.BviSem.EvalResult) c ffi) targetEval targetOutput
  let valueRel := mkApp (mkConst `Flapjack.Compiler.Backend.BviTmc.valueRel) nextMap
  let listRel := mkApp3 (mkConst `List.Forall₂ [Level.zero, Level.zero]) value value valueRel
  let eor := mkApp (mkConst `Flapjack.Compiler.Backend.BviTmc.ResultRelation.eorRel) nextMap
  let resultRel := mkAppN (mkConst `Flapjack.SemanticPrimitivesProps.resultRel)
    #[values, values, errorType, errorType, listRel, eor, result, nextResult]
  let states := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.stateRel)
    #[c, ffi, nextMap, final, next]
  let submap := mkAppN (mkConst `Flapjack.HolFiniteMapExact.submap) #[nat, nat, map, nextMap]
  let refs (s : Expr) := mkAppN (mkConst `Flapjack.Compiler.Backend.BviSem.BviState.refs) #[c, ffi, s]
  let fresh := mkApp3 (mkConst `Flapjack.Compiler.Backend.BviTmc.onlyFresh) map nextMap (refs target)
  let empty := mkApp2 (mkConst `EmptyCollection.emptyCollection [Level.zero])
    (mkApp (mkConst `Set [Level.zero]) nat)
    (mkApp (mkConst `Set.instEmptyCollection [Level.zero]) nat)
  let unchanged := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.holesUnchangedExcept)
    #[nat, nat, value, map, refs target, refs next, empty]
  let notFinal := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.holesStillNotFinalised)
    #[nat, nat, value, map, refs target, refs next]
  return #[targetRun, resultRel, states, submap, fresh, unchanged, notFinal]

private def tmcWorkerProblems (worker c ffi xs env1 env2 target final result map loc dest opt : Expr) : MetaM (Array String) := do
  let nat := mkConst `Nat
  let value := mkConst `Flapjack.Compiler.Backend.BvlSem.Value
  let values := mkApp (mkConst `List [Level.zero]) value
  let exp := mkConst `Flapjack.Compiler.Backend.Bvi.Exp
  let resultType := mkConst `Flapjack.Compiler.Backend.BviSem.BviResult
  let state := mkApp2 (mkConst `Flapjack.Compiler.Backend.BviSem.BviState) c ffi
  let pointerMap := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) nat nat
  let refs (s : Expr) := mkAppN (mkConst `Flapjack.Compiler.Backend.BviSem.BviState.refs) #[c, ffi, s]
  let lengthEnv := mkApp2 (mkConst `List.length [Level.zero]) value env1
  forallTelescope worker fun args conclusion => do
    unless args.size == 3 do return #["worker simulation binders changed"]
    let enabled ← args[0]!.fvarId!.getDecl
    let hole ← args[1]!.fvarId!.getDecl
    let assumptions ← args[2]!.fvarId!.getDecl
    let eqOpt := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst `Bool) opt (mkConst `Bool.true)
    unless enabled.binderInfo == .default && enabled.type == eqOpt &&
        hole.userName == `holePtr && hole.binderInfo == .default && hole.type == nat &&
        assumptions.binderInfo == .default do
      return #["worker simulation binders changed"]
    let .app (.app (.const ``And []) initialHole)
        (.app (.app (.const ``And []) notFinal) pointerEq) := assumptions.type
      | return #["worker simulation premises changed"]
    let initialProblems ← tmcExists initialHole value `c fun v body => do
      let expected := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.holeHasVal)
        #[map, env1, env2, refs target, v]
      return if body == expected then #[] else #["worker initial hole value changed"]
    unless initialProblems.isEmpty do return initialProblems
    let expectedNotFinal := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.holeNotFinalised)
      #[nat, value, refs target, args[1]!]
    unless pointerEq.isAppOfArity ``Eq 3 do return #["worker pointer premise changed"]
    let selected := pointerEq.getAppArgs[1]!
    unless selected.isAppOfArity `Flapjack.holEl 4 && selected.getAppArgs[0]! == value &&
        selected.getAppArgs[2]! == lengthEnv && selected.getAppArgs[3]! == env2 do
      return #["worker pointer selection changed"]
    unless ← isDefEq (← inferType selected.getAppArgs[1]!)
        (mkApp (mkConst ``Nonempty [Level.succ Level.zero]) value) do
      return #["worker pointer selection has the wrong inhabitation witness"]
    let ptr := mkApp2 (mkConst `Flapjack.Compiler.Backend.BvlSem.Value.refPtr)
      (mkConst `Bool.false) args[1]!
    let expectedPointer := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) value selected ptr
    unless notFinal == expectedNotFinal && pointerEq == expectedPointer do
      return #["worker hole or pointer premise changed"]
    tmcExists conclusion resultType `workResult fun workResult afterResult =>
      tmcExists afterResult pointerMap `workMap fun workMap afterMap =>
        tmcExists afterMap state `workState fun workState workBody => do
          let mut clauses := #[]
          let mut resultCase := workBody
          for _ in [:7] do
            match resultCase with
            | .app (.app (.const ``And []) first) rest =>
              clauses := clauses.push first
              resultCase := rest
            | _ => return #["worker simulation must contain the seven original conjuncts"]
          let some head := clauses[0]!.find? (fun e => e.isAppOfArity `Flapjack.holHd 3)
            | return #["worker head selection missing"]
          unless head.getAppArgs[0]! == exp && head.getAppArgs[2]! == xs do
            return #["worker head selection changed"]
          unless ← isDefEq (← inferType head.getAppArgs[1]!)
              (mkApp (mkConst ``Nonempty [Level.succ Level.zero]) exp) do
            return #["worker head selection has the wrong inhabitation witness"]
          let literal := Expr.lit (.natVal 1)
          let one := mkAppN (mkConst `OfNat.ofNat [Level.zero])
            #[nat, literal, mkApp (mkConst `instOfNatNat) literal]
          let addInst := mkApp2 (mkConst `instHAdd [Level.zero]) nat (mkConst `instAddNat)
          let nextIndex := mkAppN (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero])
            #[nat, nat, nat, addInst, lengthEnv, one]
          let rewritten := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.rewriteWorkerSource)
            #[loc, dest, lengthEnv, nextIndex, lengthEnv, head]
          let program := mkApp3 (mkConst `List.cons [Level.zero]) exp rewritten
            (mkApp (mkConst `List.nil [Level.zero]) exp)
          let evaluation := mkAppN (mkConst `Flapjack.Compiler.Backend.BviSem.evaluate)
            #[c, ffi, program, env2, target]
          let output := mkAppN (mkConst `Prod.mk [Level.zero, Level.zero])
            #[resultType, state, workResult, workState]
          let run := mkApp3 (mkConst ``Eq [Level.succ Level.zero])
            (mkApp2 (mkConst `Flapjack.Compiler.Backend.BviSem.EvalResult) c ffi) evaluation output
          let relation := mkApp3 (mkConst `Flapjack.Compiler.Backend.BviTmc.ResultRelation.optResRel)
            workMap result workResult
          let states := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.stateRel)
            #[c, ffi, workMap, final, workState]
          let submap := mkAppN (mkConst `Flapjack.HolFiniteMapExact.submap) #[nat, nat, map, workMap]
          let fresh := mkApp3 (mkConst `Flapjack.Compiler.Backend.BviTmc.onlyFresh) map workMap (refs target)
          let singleton := mkAppN (mkConst `Singleton.singleton [Level.zero, Level.zero])
            #[nat, mkApp (mkConst `Set [Level.zero]) nat,
              mkApp (mkConst `Set.instSingletonSet [Level.zero]) nat, args[1]!]
          let unchanged := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.holesUnchangedExcept)
            #[nat, nat, value, map, refs target, refs workState, singleton]
          let still := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.holesStillNotFinalised)
            #[nat, nat, value, map, refs target, refs workState]
          unless clauses == #[run, relation, states, submap, fresh, unchanged, still] do
            return #["worker target simulation changed"]
          forallTelescope resultCase fun resultArgs resultConclusion => do
            unless resultArgs.size == 2 do return #["worker result case changed"]
            let returned ← resultArgs[0]!.fvarId!.getDecl
            let equality ← resultArgs[1]!.fvarId!.getDecl
            let resultValues := mkApp3 (mkConst `List.cons [Level.zero]) value resultArgs[0]!
              (mkApp (mkConst `List.nil [Level.zero]) value)
            let successful := mkApp3 (mkConst `Flapjack.SemanticPrimitivesHOL.Result.val)
              values (mkConst `Flapjack.Compiler.Backend.BviSem.ExnOrRet) resultValues
            let expectedEquality := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) resultType result successful
            unless returned.userName == `resValue && returned.binderInfo == .default && returned.type == value &&
                equality.binderInfo == .default && equality.type == expectedEquality do
              return #["worker result premise changed"]
            tmcExists resultConclusion value `resValue' fun resultValue afterValue => do
              let refType := mkApp (mkConst `Flapjack.Compiler.Backend.BvlSem.Ref) value
              let erased := mkAppN (mkConst `Flapjack.HolFiniteMapExact.eraseEq)
                #[nat, refType, mkConst `instDecidableEqNat, refs workState, args[1]!]
              let block := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.mutableBlockRel)
                #[workMap, refs target, erased, resultArgs[0]!, resultValue]
              let holeValue := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.holeHasVal)
                #[map, env1, env2, refs workState, resultValue]
              unless afterValue == mkApp2 (mkConst ``And) block holeValue do
                return #["worker result relation or final hole changed"]
              return #[]

/-- Check the elaborated TMC induction predicate's telescopes, clock guard,
simulation premise and ordinary, wrapper and worker simulations. The caller
must independently validate map-scope inventory, codec and declaration ownership. -/
def tmcHypothesisUniversalBinderProblems (type value : Expr) : MetaM (Array String) := do
  unless ← isDefEq (← inferType value) type do
    return #["predicate body has the wrong declaration type"]
  lambdaTelescope value fun parameters body => do
    unless parameters.size == 5 do
      return #["predicate must have five outer binders"]
    let nat := mkConst `Nat
    let c := parameters[0]!
    let ffi := parameters[1]!
    let pair := mkApp2 (mkConst `Prod [Level.zero, Level.zero]) nat c
    let state (cfg : Expr) := mkApp2 (mkConst `Flapjack.Compiler.Backend.BviSem.BviState) cfg ffi
    let values := mkApp (mkConst `List [Level.zero]) (mkConst `Flapjack.Compiler.Backend.BvlSem.Value)
    let expressions := mkApp (mkConst `List [Level.zero]) (mkConst `Flapjack.Compiler.Backend.Bvi.Exp)
    let outerNames := #[`C, `F, `xs, `source, `clock]
    let outerTypes := #[mkSort (Level.succ Level.zero), mkSort (Level.succ Level.zero),
      expressions, state pair, nat]
    for i in [:outerNames.size] do
      let binder ← parameters[i]!.fvarId!.getDecl
      let visibility := if i < 2 then BinderInfo.implicit else BinderInfo.default
      unless binder.userName == outerNames[i]! && binder.binderInfo == visibility &&
          binder.type == outerTypes[i]! do
        return #[s!"outer binder {i} has the wrong name, visibility or carrier"]
    forallTelescope body fun binders conclusion => do
      unless binders.size == 10 do
        return #["predicate body has the wrong universal telescope"]
      let map := binders[5]!
      let mapDecl ← map.fvarId!.getDecl
      let expectedMap := mkApp2 (mkConst `Flapjack.HolFiniteMapExact)
        (mkConst `Nat) (mkConst `Nat)
      unless mapDecl.userName == `f && mapDecl.binderInfo == .default && mapDecl.type == expectedMap do
        return #["universal f must be explicit and have the canonical Nat-to-Nat map carrier"]
      let expectedNames := #[`env1, `result, `final, `opt, `f, `target, `env2, `loc]
      let expectedTypes := #[values, mkConst `Flapjack.Compiler.Backend.BviSem.BviResult,
        state pair, mkConst `Bool, expectedMap, state c, values, nat]
      for i in [:expectedNames.size] do
        let binder ← binders[i + 1]!.fvarId!.getDecl
        unless binder.userName == expectedNames[i]! && binder.binderInfo == .default &&
            binder.type == expectedTypes[i]! do
          return #[s!"universal binder {i + 1} has the wrong name, visibility or carrier"]
      let guard ← binders[0]!.fvarId!.getDecl
      let premise ← binders[9]!.fvarId!.getDecl
      let sourceClock := mkAppN (mkConst `Flapjack.Compiler.Backend.BviSem.BviState.clock)
        #[pair, ffi, parameters[3]!]
      let expectedGuard := mkAppN (mkConst `LT.lt [Level.zero])
        #[nat, mkConst `instLTNat, sourceClock, parameters[4]!]
      unless guard.binderInfo == .default && premise.binderInfo == .default &&
          guard.type == expectedGuard && (← isProp premise.type) do
        return #["clock guard or simulation premise has the wrong shape"]
      let mut clauses := #[]
      let mut remainder := premise.type
      for _ in [:5] do
        match remainder with
        | .app (.app (.const ``And []) first) rest =>
          clauses := clauses.push first
          remainder := rest
        | _ => return #["simulation premise must contain the six original conjuncts"]
      clauses := clauses.push remainder
      let env1 := binders[1]!
      let result := binders[2]!
      let final := binders[3]!
      let opt := binders[4]!
      let target := binders[6]!
      let env2 := binders[7]!
      let xs := parameters[2]!
      let source := parameters[3]!
      let resultType := mkConst `Flapjack.Compiler.Backend.BviSem.BviResult
      let evaluation := mkAppN (mkConst `Flapjack.Compiler.Backend.BviSem.evaluate)
        #[pair, ffi, xs, env1, source]
      let output := mkAppN (mkConst `Prod.mk [Level.zero, Level.zero])
        #[resultType, state pair, result, final]
      let expectedEvaluation := mkApp3 (mkConst ``Eq [Level.succ Level.zero])
        (mkApp2 (mkConst `Flapjack.Compiler.Backend.BviSem.EvalResult) pair ffi) evaluation output
      let expectedEnv := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.envRel) #[opt, map, env1, env2]
      let expectedStates := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.stateRel)
        #[c, ffi, map, source, target]
      unless clauses[0]! == expectedEvaluation && clauses[1]! == expectedEnv &&
          clauses[3]! == expectedStates do
        return #["simulation evaluation, environment or state relation changed"]
      let allSafe ← forallTelescope clauses[2]! fun args conclusion => do
        unless args.size == 2 do return false
        let expression ← args[0]!.fvarId!.getDecl
        let membership ← args[1]!.fvarId!.getDecl
        let exp := mkConst `Flapjack.Compiler.Backend.Bvi.Exp
        let expectedMember := mkAppN (mkConst `Membership.mem [Level.zero, Level.zero])
          #[exp, expressions, mkApp (mkConst `List.instMembership [Level.zero]) exp, xs, args[0]!]
        return expression.binderInfo == .default && expression.type == exp &&
          membership.binderInfo == .default && membership.type == expectedMember &&
          conclusion == mkApp (mkConst `Flapjack.Compiler.Backend.BviTmc.noMutcons) args[0]!
      unless allSafe do return #["no-mutcons premise changed"]
      let singleton ← forallTelescope clauses[4]! fun args conclusion => do
        unless args.size == 1 do return false
        let assumption ← args[0]!.fvarId!.getDecl
        let eqBool := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst `Bool) opt (mkConst `Bool.true)
        let length := mkApp2 (mkConst `List.length [Level.zero])
          (mkConst `Flapjack.Compiler.Backend.Bvi.Exp) xs
        let oneLiteral := Expr.lit (.natVal 1)
        let one := mkAppN (mkConst `OfNat.ofNat [Level.zero])
          #[nat, oneLiteral, mkApp (mkConst `instOfNatNat) oneLiteral]
        let lengthEq := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) nat length one
        return assumption.binderInfo == .default && assumption.type == eqBool && conclusion == lengthEq
      unless singleton do return #["optimized singleton premise changed"]
      let errorType := mkConst `Flapjack.Compiler.Backend.BviSem.ExnOrRet
      let abort := mkApp2 (mkConst `Flapjack.SemanticPrimitivesHOL.ErrorResult.abort)
        errorType (mkConst `Flapjack.SemanticPrimitivesHOL.Abort.typeError)
      let typeError := mkApp3 (mkConst `Flapjack.SemanticPrimitivesHOL.Result.err) values errorType abort
      let safe := mkApp3 (mkConst ``Ne [Level.succ Level.zero]) resultType result typeError
      unless clauses[5]! == safe do return #["source type-error premise changed"]
      unless (premise.type.find? (· == map)).isSome && (conclusion.find? (· == map)).isSome do
        return #["universal f must occur in both the premise and conclusion"]
      tmcExists conclusion (state c) `next fun next afterState =>
        tmcExists afterState expectedMap `nextMap fun nextMap afterMap =>
          tmcExists afterMap resultType `nextResult fun nextResult ordinary => do
            let mut ordinaryClauses := #[]
            let mut optimized := ordinary
            for _ in [:7] do
              match optimized with
              | .app (.app (.const ``And []) first) rest =>
                ordinaryClauses := ordinaryClauses.push first
                optimized := rest
              | _ => return #["ordinary simulation must contain the seven original conjuncts"]
            unless ordinaryClauses == tmcResultFrame c ffi xs env2 target final result map next nextMap nextResult do
              return #["ordinary target simulation changed"]
            forallTelescope optimized fun args body => do
              unless args.size == 2 do return #["optimized branch entry changed"]
              let dest ← args[0]!.fvarId!.getDecl
              let code ← args[1]!.fvarId!.getDecl
              let codeField (cfg s : Expr) :=
                mkAppN (mkConst `Flapjack.Compiler.Backend.BviSem.BviState.code) #[cfg, ffi, s]
              let expectedCode := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.optimisedCode)
                #[binders[8]!, args[0]!, codeField pair source, codeField c target]
              unless dest.userName == `locOpt && dest.binderInfo == .default && dest.type == nat &&
                  code.binderInfo == .default && code.type == expectedCode do
                return #["optimized branch entry changed"]
              let .app (.app (.const ``And []) wrapper) worker := body
                | return #["optimized wrapper and worker branches must both be present"]
              let wrapperProblems ← forallTelescope wrapper fun wrapArgs wrapConclusion => do
                unless wrapArgs.size == 2 do return #["wrapper simulation binders changed"]
                let wrap ← wrapArgs[0]!.fvarId!.getDecl
                let assumption ← wrapArgs[1]!.fvarId!.getDecl
                let exp := mkConst `Flapjack.Compiler.Backend.Bvi.Exp
                let lengthExp := mkApp2 (mkConst `List.length [Level.zero]) exp xs
                let literal := Expr.lit (.natVal 1)
                let one := mkAppN (mkConst `OfNat.ofNat [Level.zero])
                  #[nat, literal, mkApp (mkConst `instOfNatNat) literal]
                let singleton := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) nat lengthExp one
                let lengthEnv := mkApp2 (mkConst `List.length [Level.zero])
                  (mkConst `Flapjack.Compiler.Backend.BvlSem.Value) env1
                let .app (.app (.const ``And []) _) actualRewriteEq := assumption.type
                  | return #["wrapper simulation premise changed"]
                unless actualRewriteEq.isAppOfArity ``Eq 3 do
                  return #["wrapper simulation premise changed"]
                let actualRewrite := actualRewriteEq.getAppArgs[1]!
                unless actualRewrite.isAppOfArity `Flapjack.Compiler.Backend.BviTmc.rewriteWrapperSource 4 do
                  return #["wrapper simulation premise changed"]
                let head := actualRewrite.getAppArgs[3]!
                unless head.isAppOfArity `Flapjack.holHd 3 && head.getAppArgs[0]! == exp &&
                    head.getAppArgs[2]! == xs do
                  return #["wrapper head selection changed"]
                let inhabitedType := mkApp (mkConst ``Nonempty [Level.succ Level.zero]) exp
                unless ← isDefEq (← inferType head.getAppArgs[1]!) inhabitedType do
                  return #["wrapper head selection has the wrong inhabitation witness"]
                let rewritten := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.rewriteWrapperSource)
                  #[binders[8]!, args[0]!, lengthEnv, head]
                let optionExp := mkApp (mkConst `Option [Level.zero]) exp
                let someWrap := mkApp2 (mkConst `Option.some [Level.zero]) exp wrapArgs[0]!
                let rewriteEq := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) optionExp rewritten someWrap
                let expectedAssumption := mkApp2 (mkConst ``And) singleton rewriteEq
                unless wrap.userName == `wrap && wrap.binderInfo == .default && wrap.type == exp &&
                    assumption.binderInfo == .default && assumption.type == expectedAssumption do
                  return #["wrapper simulation premise changed"]
                tmcExists wrapConclusion (state c) `wrapState fun wrapState afterWrapState =>
                  tmcExists afterWrapState expectedMap `wrapMap fun wrapMap afterWrapMap =>
                    tmcExists afterWrapMap resultType `wrapResult fun wrapResult wrapBody => do
                      let mut wrapClauses := #[]
                      let mut last := wrapBody
                      for _ in [:6] do
                        match last with
                        | .app (.app (.const ``And []) first) rest =>
                          wrapClauses := wrapClauses.push first
                          last := rest
                        | _ => return #["wrapper simulation must contain the seven original conjuncts"]
                      wrapClauses := wrapClauses.push last
                      let nil := mkApp (mkConst `List.nil [Level.zero]) exp
                      let program := mkApp3 (mkConst `List.cons [Level.zero]) exp wrapArgs[0]! nil
                      unless wrapClauses == tmcResultFrame c ffi program env2 target final result map
                          wrapState wrapMap wrapResult do
                        return #["wrapper target simulation changed"]
                      return #[]
              unless wrapperProblems.isEmpty do return wrapperProblems
              tmcWorkerProblems worker c ffi xs env1 env2 target final result map binders[8]! args[0]! opt

end Flapjack
