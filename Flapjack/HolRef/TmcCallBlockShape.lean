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

/-- Check the auxiliary and worker entry telescopes and premises, including the
existential result carriers. Their result bodies require a separate audit. -/
def tmcCallBlockWorkerEntryProblems (type : Expr) : MetaM (Array String) := do
  let earlier ← tmcCallBlockWrapperProblems type
  unless earlier.isEmpty do return earlier
  forallTelescope type fun args conclusion => do
    let .app (.app (.const ``And []) _) optimized := conclusion
      | return #["missing optimized branch"]
    forallTelescope optimized fun _ body => do
      let .app (.app (.const ``And []) _)
          (.app (.app (.const ``And []) auxiliary) worker) := body
        | return #["optimized branches must be wrapper, auxiliary and worker"]
      let nat := mkConst `Nat
      let value := mkConst `Flapjack.Compiler.Backend.BvlSem.Value
      let values := mkApp (mkConst `List [Level.zero]) value
      let refType := mkApp (mkConst `Flapjack.Compiler.Backend.BvlSem.Ref) value
      let refMap := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) nat refType
      let map := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) nat nat
      let c := args[0]!
      let ffi := args[1]!
      let pair := mkApp2 (mkConst `Prod [Level.zero, Level.zero]) nat c
      let state (cfg : Expr) := mkApp2 (mkConst `Flapjack.Compiler.Backend.BviSem.BviState) cfg ffi
      let refs (cfg s : Expr) := mkAppN (mkConst `Flapjack.Compiler.Backend.BviSem.BviState.refs) #[cfg, ffi, s]
      let f := args[5]!
      let env1 := args[7]!
      let env2 := args[8]!
      let targetRefs := refs c args[10]!
      let resultType := mkConst `Flapjack.Compiler.Backend.BviSem.BviResult
      let pointerProblems (e slot environment ptr : Expr) : MetaM (Array String) := do
        unless e.isAppOfArity ``Eq 3 do return #["pointer premise is not an equality"]
        let selected := e.getAppArgs[1]!
        unless selected.isAppOfArity `Flapjack.holEl 4 && selected.getAppArgs[0]! == value &&
            selected.getAppArgs[2]! == slot && selected.getAppArgs[3]! == environment do
          return #["pointer selection changed"]
        unless ← isDefEq (← inferType selected.getAppArgs[1]!)
            (mkApp (mkConst ``Nonempty [Level.succ Level.zero]) value) do
          return #["pointer selection has the wrong inhabitation witness"]
        let expectedPtr := mkApp2 (mkConst `Flapjack.Compiler.Backend.BvlSem.Value.refPtr)
          (mkConst `Bool.false) ptr
        unless e == mkApp3 (mkConst ``Eq [Level.succ Level.zero]) value selected expectedPtr do
          return #["pointer equality changed"]
        return #[]
      let auxProblems ← forallTelescope auxiliary fun xs rest => do
        unless xs.size == 6 do return #["auxiliary entry telescope changed"]
        let names := #[`refs, `extras, `slot, `idx, `ptr]
        let types := #[refMap, values, nat, nat, nat]
        for i in [:names.size] do
          let d ← xs[i]!.fvarId!.getDecl
          unless d.userName == names[i]! && d.binderInfo == .default && d.type == types[i]! do
            return #[s!"auxiliary binder {i} changed"]
        let premise ← xs[5]!.fvarId!.getDecl
        unless premise.binderInfo == .default do return #["auxiliary premise visibility changed"]
        let .app (.app (.const ``And []) stateRel)
            (.app (.app (.const ``And []) hole)
              (.app (.app (.const ``And []) domain) pointer)) := premise.type
          | return #["auxiliary premise conjuncts changed"]
        let expectedState := mkApp3 (mkConst `Flapjack.Compiler.Backend.BviTmc.stateRefRel)
          f (refs pair args[9]!) xs[0]!
        let domainOf (m : Expr) := mkAppN (mkConst `Flapjack.HolFiniteMapExact.domain) #[nat, refType, m]
        let set := mkApp (mkConst `Set [Level.zero]) nat
        let expectedDomain := mkAppN (mkConst `LE.le [Level.zero])
          #[set, mkApp (mkConst `Set.instLE [Level.zero]) nat, domainOf targetRefs, domainOf xs[0]!]
        unless stateRel == expectedState && domain == expectedDomain do
          return #["auxiliary state relation or domain premise changed"]
        let holeProblems ← tmcExists hole value `c fun v holeBody => do
          let expected := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.CallBlockEnvironment.allocHoleHasVal)
            #[nat, value, f, xs[0]!, xs[1]!, xs[2]!, xs[3]!, v]
          return if holeBody == expected then #[] else #["auxiliary initial hole changed"]
        unless holeProblems.isEmpty do return holeProblems
        let ptrProblems ← pointerProblems pointer xs[2]! xs[1]! xs[4]!
        unless ptrProblems.isEmpty do return ptrProblems
        tmcExists rest resultType `r fun _ afterResult =>
          tmcExists afterResult (state c) `s fun _ afterState =>
            tmcExists afterState map `auxMap fun _ _ => return #[]
      unless auxProblems.isEmpty do return auxProblems
      forallTelescope worker fun xs rest => do
        unless xs.size == 6 do return #["worker entry telescope changed"]
        let enabled ← xs[0]!.fvarId!.getDecl
        let expectedEnabled := mkApp3 (mkConst ``Eq [Level.succ Level.zero])
          (mkConst `Bool) args[6]! (mkConst `Bool.true)
        unless enabled.binderInfo == .default && enabled.type == expectedEnabled do
          return #["worker optimization guard changed"]
        let names := #[`slot, `idx, `_work, `ptr]
        let types := #[nat, nat, args[2]!, nat]
        for i in [:names.size] do
          let d ← xs[i + 1]!.fvarId!.getDecl
          unless d.userName == names[i]! && d.binderInfo == .default && d.type == types[i]! do
            return #[s!"worker binder {i} changed"]
        let premise ← xs[5]!.fvarId!.getDecl
        unless premise.binderInfo == .default do return #["worker premise visibility changed"]
        let .app (.app (.const ``And []) slotEq)
            (.app (.app (.const ``And []) idxEq)
              (.app (.app (.const ``And []) hole)
                (.app (.app (.const ``And []) notFinal) pointer))) := premise.type
          | return #["worker premise conjuncts changed"]
        let length := mkApp2 (mkConst `List.length [Level.zero]) value env1
        let literal := Expr.lit (.natVal 1)
        let one := mkAppN (mkConst `OfNat.ofNat [Level.zero])
          #[nat, literal, mkApp (mkConst `instOfNatNat) literal]
        let add := mkAppN (mkConst `HAdd.hAdd [Level.zero, Level.zero, Level.zero])
          #[nat, nat, nat, mkApp2 (mkConst `instHAdd [Level.zero]) nat (mkConst `instAddNat), length, one]
        let eq (x y : Expr) := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) nat x y
        let expectedNotFinal := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.holeNotFinalised)
          #[nat, value, targetRefs, xs[4]!]
        unless slotEq == eq xs[1]! length && idxEq == eq xs[2]! add && notFinal == expectedNotFinal do
          return #["worker index or hole premise changed"]
        let holeProblems ← tmcExists hole value `c fun v holeBody => do
          let expected := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.holeHasVal)
            #[f, env1, env2, targetRefs, v]
          return if holeBody == expected then #[] else #["worker initial hole changed"]
        unless holeProblems.isEmpty do return holeProblems
        let ptrProblems ← pointerProblems pointer xs[1]! env2 xs[4]!
        unless ptrProblems.isEmpty do return ptrProblems
        tmcExists rest resultType `r fun _ afterResult =>
          tmcExists afterResult map `workMap fun _ afterMap =>
            tmcExists afterMap (state c) `s fun _ _ => return #[]

private def tmcCallBlockOptimizedFrameProblems
    (body c ffi program environment start originalTarget final result f frameRefs ptr next nextMap nextResult : Expr)
    (finalHole : Expr → Expr) : MetaM (Array String) := do
  let nat := mkConst `Nat
  let value := mkConst `Flapjack.Compiler.Backend.BvlSem.Value
  let values := mkApp (mkConst `List [Level.zero]) value
  let resultType := mkConst `Flapjack.Compiler.Backend.BviSem.BviResult
  let state := mkApp2 (mkConst `Flapjack.Compiler.Backend.BviSem.BviState) c ffi
  let refs (s : Expr) := mkAppN (mkConst `Flapjack.Compiler.Backend.BviSem.BviState.refs) #[c, ffi, s]
  let mut clauses := #[]
  let mut tail := body
  for _ in [:7] do
    match tail with
    | .app (.app (.const ``And []) first) rest =>
      clauses := clauses.push first
      tail := rest
    | _ => return #["optimized result must have seven frame conjuncts and a success case"]
  let evaluation := mkAppN (mkConst `Flapjack.Compiler.Backend.BviSem.evaluate)
    #[c, ffi, program, environment, start]
  let output := mkAppN (mkConst `Prod.mk [Level.zero, Level.zero]) #[resultType, state, nextResult, next]
  let run := mkApp3 (mkConst ``Eq [Level.succ Level.zero])
    (mkApp2 (mkConst `Flapjack.Compiler.Backend.BviSem.EvalResult) c ffi) evaluation output
  let relation := mkApp3 (mkConst `Flapjack.Compiler.Backend.BviTmc.ResultRelation.optResRel)
    nextMap result nextResult
  let states := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.stateRel) #[c, ffi, nextMap, final, next]
  let submap := mkAppN (mkConst `Flapjack.HolFiniteMapExact.submap) #[nat, nat, f, nextMap]
  let fresh := mkApp3 (mkConst `Flapjack.Compiler.Backend.BviTmc.onlyFresh) f nextMap frameRefs
  let singleton := mkAppN (mkConst `Singleton.singleton [Level.zero, Level.zero])
    #[nat, mkApp (mkConst `Set [Level.zero]) nat, mkApp (mkConst `Set.instSingletonSet [Level.zero]) nat, ptr]
  let unchanged := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.holesUnchangedExcept)
    #[nat, nat, value, f, frameRefs, refs next, singleton]
  let still := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.holesStillNotFinalised)
    #[nat, nat, value, f, frameRefs, refs next]
  unless clauses == #[run, relation, states, submap, fresh, unchanged, still] do
    return #["optimized evaluation or result frame changed"]
  forallTelescope tail fun xs conclusion => do
    unless xs.size == 2 do return #["optimized singleton-success case changed"]
    let returned ← xs[0]!.fvarId!.getDecl
    let premise ← xs[1]!.fvarId!.getDecl
    let singletonValue := mkApp3 (mkConst `List.cons [Level.zero]) value xs[0]!
      (mkApp (mkConst `List.nil [Level.zero]) value)
    let success := mkApp3 (mkConst `Flapjack.SemanticPrimitivesHOL.Result.val)
      values (mkConst `Flapjack.Compiler.Backend.BviSem.ExnOrRet) singletonValue
    let equality := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) resultType result success
    unless returned.userName == `v && returned.binderInfo == .default && returned.type == value &&
        premise.binderInfo == .default && premise.type == equality do
      return #["optimized singleton-success premise changed"]
    tmcExists conclusion value `v' fun v' resultBody => do
      let refType := mkApp (mkConst `Flapjack.Compiler.Backend.BvlSem.Ref) value
      let erased := mkAppN (mkConst `Flapjack.HolFiniteMapExact.eraseEq)
        #[nat, refType, mkConst `instDecidableEqNat, refs next, ptr]
      let block := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.mutableBlockRel)
        #[nextMap, refs originalTarget, erased, xs[0]!, v']
      unless resultBody == mkApp2 (mkConst ``And) block (finalHole v') do
        return #["optimized success relation or final hole changed"]
      return #[]

/-- Check both optimized execution frames and singleton-success conclusions.
This audits the theorem type only; declaration and HOL correspondence checks
remain necessary before a qualifier can use it. -/
def tmcCallBlockOptimizedResultProblems (type : Expr) : MetaM (Array String) := do
  let entry ← tmcCallBlockWorkerEntryProblems type
  unless entry.isEmpty do return entry
  forallTelescope type fun args conclusion => do
    let .app (.app (.const ``And []) _) optimized := conclusion
      | return #["missing optimized branch"]
    forallTelescope optimized fun destArgs body => do
      let .app (.app (.const ``And []) _)
          (.app (.app (.const ``And []) auxiliary) worker) := body
        | return #["missing optimized result branches"]
      let nat := mkConst `Nat
      let value := mkConst `Flapjack.Compiler.Backend.BvlSem.Value
      let values := mkApp (mkConst `List [Level.zero]) value
      let exp := mkConst `Flapjack.Compiler.Backend.Bvi.Exp
      let c := args[0]!
      let ffi := args[1]!
      let state := mkApp2 (mkConst `Flapjack.Compiler.Backend.BviSem.BviState) c ffi
      let resultType := mkConst `Flapjack.Compiler.Backend.BviSem.BviResult
      let map := mkApp2 (mkConst `Flapjack.HolFiniteMapExact) nat nat
      let refs (s : Expr) := mkAppN (mkConst `Flapjack.Compiler.Backend.BviSem.BviState.refs) #[c, ffi, s]
      let cb := args[3]!
      let f := args[5]!
      let env1 := args[7]!
      let env2 := args[8]!
      let target := args[10]!
      let final := args[11]!
      let result := args[12]!
      let program (e : Expr) := mkApp3 (mkConst `List.cons [Level.zero]) exp e
        (mkApp (mkConst `List.nil [Level.zero]) exp)
      let auxiliaryProblems ← forallTelescope auxiliary fun xs rest => do
        let field (name : Name) := mkAppN (mkConst name) #[c, ffi, target]
        let start := mkAppN (mkConst `Flapjack.Compiler.Backend.BviSem.BviState.mk)
          #[c, ffi, xs[0]!, field `Flapjack.Compiler.Backend.BviSem.BviState.clock,
            field `Flapjack.Compiler.Backend.BviSem.BviState.global,
            field `Flapjack.Compiler.Backend.BviSem.BviState.compile,
            field `Flapjack.Compiler.Backend.BviSem.BviState.compileOracle,
            field `Flapjack.Compiler.Backend.BviSem.BviState.code,
            field `Flapjack.Compiler.Backend.BviSem.BviState.ffi]
        let length := mkApp2 (mkConst `List.length [Level.zero]) value xs[1]!
        let shifted := mkApp2 (mkConst `Flapjack.Compiler.Backend.BviTmc.shiftBlock) length cb
        let rewritten := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.workerAuxSource)
          #[shifted, destArgs[0]!, xs[2]!, xs[3]!]
        let appendInst := mkApp2 (mkConst `instHAppendOfAppend [Level.zero]) values
          (mkApp (mkConst `List.instAppend [Level.zero]) value)
        let environment := mkAppN (mkConst `HAppend.hAppend [Level.zero, Level.zero, Level.zero])
          #[values, values, values, appendInst, xs[1]!, env2]
        tmcExists rest resultType `r fun r afterResult =>
          tmcExists afterResult state `s fun s afterState =>
            tmcExists afterState map `auxMap fun g resultBody => do
              let finalHole v := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.CallBlockEnvironment.allocHoleHasVal)
                #[nat, value, f, refs s, xs[1]!, xs[2]!, xs[3]!, v]
              tmcCallBlockOptimizedFrameProblems resultBody c ffi (program rewritten) environment start
                target final result f xs[0]! xs[4]! s g r finalHole
      unless auxiliaryProblems.isEmpty do return auxiliaryProblems
      forallTelescope worker fun xs rest => do
        let rewritten := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.workerBlockSource)
          #[cb, destArgs[0]!, xs[1]!, xs[2]!]
        tmcExists rest resultType `r fun r afterResult =>
          tmcExists afterResult map `workMap fun g afterMap =>
            tmcExists afterMap state `s fun s resultBody => do
              let finalHole v := mkAppN (mkConst `Flapjack.Compiler.Backend.BviTmc.holeHasVal)
                #[f, env1, env2, refs s, v]
              tmcCallBlockOptimizedFrameProblems resultBody c ffi (program rewritten) env2 target
                target final result f (refs target) xs[4]! s g r finalHole

end Flapjack
