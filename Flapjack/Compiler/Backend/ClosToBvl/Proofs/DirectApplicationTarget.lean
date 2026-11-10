module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateApp

@[expose] public section

/-! Installed-code facts for known-location closure calls. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- The code pointer in a related recursive closure is its source location,
shifted by the stub count and the recursive function index. -/
theorem clRel_recclosure_direct_address {maxApp : Nat} {fs : Nat → Prop}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {captured : List ClosSem.Value} {fields : List BvlSem.Value} {ptr index arity : Nat}
    {functions : List (Nat × ClosLang.Exp)} {body : ClosLang.Exp} {target : BvlSem.Value}
    (related : clRel maxApp fs refs code (captured, fields) (.recclosure (some ptr) [] captured functions index) target)
    (found : functions[index]? = some (arity, body)) :
    ∃ payload, target = .block 30
      (.codePtr ((ptr + 2 * index) + numStubs maxApp) :: .number (Int.ofNat (arity - 1)) :: payload) := by
  cases related with
  | singletonRec bound positive loc vars compiled installed lookup =>
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl⟩ := found
    exact ⟨fields, by simp⟩
  | @mutualRec exps entries ps rs loc r env ys k expsEq psEq positions values fresh stored many indexBound locations vars installed =>
    have entryBound : index < entries.length := by simpa [expsEq] using indexBound
    have entryEq : (entries[index]'entryBound).1 = (arity, body) := by
      have h : functions[index]? = some (arity, body) := found
      rw [expsEq, List.getElem?_map, List.getElem?_eq_getElem entryBound] at h
      simpa using h
    have entryAddress : (entries[index]'entryBound).2 = ptr + numStubs maxApp + 2 * index := by
      have actual : ps[index]? = some (entries[index]'entryBound).2 := by
        simp [psEq, List.getElem?_map, List.getElem?_eq_getElem entryBound]
      have expected : ps[index]? = some (ptr + numStubs maxApp + 2 * index) := by
        simp [positions, entryBound]
      exact Option.some.inj (actual.symm.trans expected)
    subst rs
    rw [Flapjack.holEl_eq_getElem index _ (by simpa using entryBound)]
    simp only [List.getElem_map]
    cases h : entries[index]'entryBound with
    | mk pair label =>
      have pairEq : pair = (arity, body) := by simpa [h] using entryEq
      have labelEq : label = (ptr + 2 * index) + numStubs maxApp := by
        have := entryAddress
        simp only [h] at this
        omega
      subst pair
      subst label
      exact ⟨_, rfl⟩

/-- A related recursive closure resolves its known-location target call with
one extra argument for the closure block itself. -/
theorem vRel_recclosure_direct_findCode {maxApp ptr index arity : Nat}
    {f : HolFiniteMapExact Nat Nat} {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)}
    {code : Spt (Nat × Bvl.Exp)} {captured : List ClosSem.Value}
    {functions : List (Nat × ClosLang.Exp)} {sourceBody : ClosLang.Exp} {target : BvlSem.Value}
    {sourceArgs : List ClosSem.Value} {targetArgs : List BvlSem.Value}
    (related : vRel maxApp f refs code (.recclosure (some ptr) [] captured functions index) target)
    (found : functions[index]? = some (arity, sourceBody))
    (argsRel : List.Forall₂ (vRel maxApp f refs code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity) :
    ∃ entry, BvlSem.findCode (some ((ptr + 2 * index) + numStubs maxApp))
      (targetArgs ++ [target]) code = some (targetArgs ++ [target], entry) := by
  obtain ⟨fields, _, closure⟩ := vRel_recclosure_original related
  obtain ⟨expectedPayload, expectedShape⟩ := clRel_recclosure_direct_address closure found
  obtain ⟨address, payload, entry, actualShape, lookup⟩ := clRel_recclosure_target_code closure found
  have addressEq : address = (ptr + 2 * index) + numStubs maxApp := by
    have equal := actualShape.symm.trans expectedShape
    simp only [BvlSem.Value.block.injEq, List.cons.injEq, BvlSem.Value.codePtr.injEq] at equal
    exact equal.2.1
  subst address
  have length : targetArgs.length = arity := argsRel.length_eq.symm.trans arityMatch
  exact ⟨entry, by simp [BvlSem.findCode, lookup, length]⟩

/-- A related ordinary closure resolves its known-location target call with
one extra argument for the closure block itself. -/
theorem vRel_ordinary_direct_findCode {maxApp ptr arity : Nat}
    {f : HolFiniteMapExact Nat Nat} {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)}
    {code : Spt (Nat × Bvl.Exp)} {captured : List ClosSem.Value} {sourceBody : ClosLang.Exp}
    {target : BvlSem.Value} {sourceArgs : List ClosSem.Value} {targetArgs : List BvlSem.Value}
    (related : vRel maxApp f refs code (.closure (some ptr) [] captured arity sourceBody) target)
    (argsRel : List.Forall₂ (vRel maxApp f refs code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity) :
    ∃ entry, BvlSem.findCode (some (ptr + numStubs maxApp)) (targetArgs ++ [target]) code =
      some (targetArgs ++ [target], entry) := by
  obtain ⟨fields, _, closure⟩ := vRel_ordinary_closure related
  cases closure with
  | closure bound positive locations vars compiled installed lookup =>
    have length : targetArgs.length = arity := argsRel.length_eq.symm.trans arityMatch
    have has : ∃ entry, sptLookup (ptr + numStubs maxApp) code = some (arity + 1, entry) := ⟨_, lookup⟩
    obtain ⟨entry, entryLookup⟩ := has
    exact ⟨entry, by simp [BvlSem.findCode, entryLookup, length]⟩

/-- Whenever a related closure accepts a known-location application, the
compiled direct call resolves to installed code with the right arity. -/
theorem vRel_direct_findCode {maxApp address : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {function : ClosSem.Value} {target : BvlSem.Value} {sourceArgs : List ClosSem.Value}
    {targetArgs : List BvlSem.Value} {application : ClosSem.AppKind}
    (related : vRel maxApp f refs code function target)
    (argsRel : List.Forall₂ (vRel maxApp f refs code) sourceArgs targetArgs)
    (found : ClosSem.destClosure maxApp (some address) function sourceArgs = some application) :
    ∃ entry, BvlSem.findCode (some (address + numStubs maxApp)) (targetArgs ++ [target]) code =
      some (targetArgs ++ [target], entry) := by
  cases function <;> simp only [ClosSem.destClosure] at found <;> try contradiction
  case closure location supplied captured arity body =>
    have shape := ClosSem.destClosure_direct_closure maxApp address location supplied captured sourceArgs arity body application (by
      simpa only [ClosSem.destClosure] using found)
    obtain ⟨rfl, rfl, arityEq, _, _⟩ := shape
    exact vRel_ordinary_direct_findCode related argsRel arityEq.symm
  case recclosure location supplied captured functions index =>
    have shape := ClosSem.destClosure_direct_recclosure maxApp address location supplied captured sourceArgs functions index application (by
      simpa only [ClosSem.destClosure] using found)
    obtain ⟨arity, body, selected, locationEq, rfl, arityEq, _, _⟩ := shape
    cases location with
    | none => simp at locationEq
    | some ptr =>
      simp only [Option.map, Option.some.injEq] at locationEq
      subst address
      have call := vRel_recclosure_direct_findCode related selected argsRel arityEq.symm
      simpa [Nat.add_comm] using call

/-- A successfully selected known-location closure has the target block
layout expected by an exact generic closure call. -/
theorem vRel_direct_shape {maxApp address : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {function : ClosSem.Value} {target : BvlSem.Value} {sourceArgs : List ClosSem.Value}
    {targetArgs : List BvlSem.Value} {application : ClosSem.AppKind}
    (related : vRel maxApp f refs code function target)
    (argsRel : List.Forall₂ (vRel maxApp f refs code) sourceArgs targetArgs)
    (found : ClosSem.destClosure maxApp (some address) function sourceArgs = some application) :
    ∃ payload, target = .block 30 (.codePtr (address + numStubs maxApp) ::
      .number (Int.ofNat (targetArgs.length - 1)) :: payload) := by
  have argLength : targetArgs.length = sourceArgs.length := argsRel.length_eq.symm
  cases function <;> simp only [ClosSem.destClosure] at found <;> try contradiction
  case closure location supplied captured arity body =>
    have shape := ClosSem.destClosure_direct_closure maxApp address location supplied captured sourceArgs arity body application (by
      simpa only [ClosSem.destClosure] using found)
    obtain ⟨rfl, rfl, arityEq, _, _⟩ := shape
    obtain ⟨fields, _, closure⟩ := vRel_ordinary_closure related
    cases closure with
    | closure _ _ _ _ _ _ _ => exact ⟨fields, by simp [argLength, arityEq]⟩
  case recclosure location supplied captured functions index =>
    have shape := ClosSem.destClosure_direct_recclosure maxApp address location supplied captured sourceArgs functions index application (by
      simpa only [ClosSem.destClosure] using found)
    obtain ⟨arity, body, selected, locationEq, rfl, arityEq, _, _⟩ := shape
    cases location with
    | none => simp at locationEq
    | some ptr =>
      simp only [Option.map, Option.some.injEq] at locationEq
      subst address
      obtain ⟨fields, _, closure⟩ := vRel_recclosure_original related
      obtain ⟨payload, targetEq⟩ := clRel_recclosure_direct_address closure selected
      exact ⟨payload, by simpa [argLength, arityEq, Nat.add_comm] using targetEq⟩

/-- Generated direct-call argument variables read the same values as the
exact generic closure-call path. -/
theorem evaluate_directCall_env {C F : Type} (s : BvlSem.State C F)
    (values rest : List BvlSem.Value) (closure : BvlSem.Value) (address : Nat) (body : Bvl.Exp)
    (nonempty : values ≠ [])
    (found : BvlSem.findCode (some address) (values ++ [closure]) s.code = some (values ++ [closure], body)) :
    BvlSem.evaluate [.call (values.length - 1) (some address)
      ((List.range values.length).map Bvl.Exp.var ++ [.var values.length])]
      (values ++ [closure] ++ rest) s =
      if s.clock < values.length then (.err (.abort .timeoutError), { s with clock := 0 })
      else BvlSem.evaluate [body] (values ++ [closure]) (BvlSem.decClock values.length s) := by
  let env := values ++ [closure] ++ rest
  have argsRun : BvlSem.evaluate ((List.range values.length).map Bvl.Exp.var) env s = (.val values, s) := by
    have bound : values.length ≤ env.length := by simp [env]
    simpa [env] using evaluate_rangeVars values.length env s bound
  have closureRun : BvlSem.evaluate [.var values.length] env s = (.val [closure], s) := by
    simp [BvlSem.evaluate, env]
  have arguments : BvlSem.evaluate ((List.range values.length).map Bvl.Exp.var ++ [.var values.length]) env s =
      (.val (values ++ [closure]), s) := by
    change BvlSem.evaluateTuple (((List.range values.length).map Bvl.Exp.var ++ [.var values.length]), env, s) = _
    rw [BvlProps.evaluateAppend]
    simp [BvlSem.evaluateTuple, argsRun, closureRun]
  have count : values.length - 1 + 1 = values.length := by
    cases values <;> simp_all
  change BvlSem.evaluate [.call (values.length - 1) (some address)
    ((List.range values.length).map Bvl.Exp.var ++ [.var values.length])] env s = _
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, arguments]
  simp [found, count]

/-- A direct target call and the exact generic closure call execute the same
installed entry at the same clock when the source accepted the location. -/
theorem evaluate_directCall_eq_generic {C F : Type} (s : BvlSem.State C F)
    (maxApp address : Nat) (f : HolFiniteMapExact Nat Nat)
    (function : ClosSem.Value) (target : BvlSem.Value)
    (sourceArgs : List ClosSem.Value) (targetArgs rest : List BvlSem.Value) (application : ClosSem.AppKind)
    (related : vRel maxApp f s.refs s.code function target)
    (argsRel : List.Forall₂ (vRel maxApp f s.refs s.code) sourceArgs targetArgs)
    (found : ClosSem.destClosure maxApp (some address) function sourceArgs = some application)
    (nonempty : targetArgs ≠ []) :
    BvlSem.evaluate [.call (targetArgs.length - 1) (some (address + numStubs maxApp))
      ((List.range targetArgs.length).map Bvl.Exp.var ++ [.var targetArgs.length])]
      (targetArgs ++ [target] ++ rest) s =
    BvlSem.evaluate [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)]
      (targetArgs ++ [target] ++ rest) s := by
  obtain ⟨payload, targetEq⟩ := vRel_direct_shape related argsRel found
  obtain ⟨entry, targetFound⟩ := vRel_direct_findCode related argsRel found
  have lookup : sptLookup (address + numStubs maxApp) s.code = some (targetArgs.length + 1, entry) := by
    cases h : sptLookup (address + numStubs maxApp) s.code with
    | none => simp [BvlSem.findCode, h] at targetFound
    | some pair =>
      obtain ⟨arity, expression⟩ := pair
      simp [BvlSem.findCode, h] at targetFound
      obtain ⟨arityEq, entryEq⟩ := targetFound
      subst arity
      subst expression
      rfl
  have direct := evaluate_directCall_env s targetArgs rest target (address + numStubs maxApp) entry nonempty targetFound
  rw [direct, targetEq]
  exact (evaluate_mkClCall_direct_env s targetArgs rest 30 (address + numStubs maxApp) payload entry nonempty lookup).symm

/-- The arity bound carried by related closures also bounds a successful
known-location application's argument count. -/
theorem vRel_direct_args_bound {maxApp address : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {function : ClosSem.Value} {target : BvlSem.Value} {sourceArgs : List ClosSem.Value}
    {application : ClosSem.AppKind}
    (related : vRel maxApp f refs code function target)
    (found : ClosSem.destClosure maxApp (some address) function sourceArgs = some application) :
    sourceArgs.length ≤ maxApp := by
  cases function <;> simp only [ClosSem.destClosure] at found <;> try contradiction
  case closure location supplied captured arity body =>
    have shape := ClosSem.destClosure_direct_closure maxApp address location supplied captured sourceArgs arity body application (by
      simpa only [ClosSem.destClosure] using found)
    obtain ⟨rfl, rfl, arityEq, _, _⟩ := shape
    obtain ⟨fields, _, closure⟩ := vRel_ordinary_closure related
    cases closure with
    | closure bound _ _ _ _ _ _ => simpa [arityEq] using bound
  case recclosure location supplied captured functions index =>
    have shape := ClosSem.destClosure_direct_recclosure maxApp address location supplied captured sourceArgs functions index application (by
      simpa only [ClosSem.destClosure] using found)
    obtain ⟨arity, body, selected, locationEq, rfl, arityEq, _, _⟩ := shape
    cases location with
    | none => simp at locationEq
    | some ptr =>
      obtain ⟨fields, _, closure⟩ := vRel_recclosure_original related
      have bound := (clRel_recclosure_arity closure selected).1
      simpa [arityEq] using bound

/-- A known-location closure application is simulated by the direct target
call using the bounded induction hypothesis for source closure bodies. -/
theorem evaluateApp_direct_simulation_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (address clockBound : Nat) (function : ClosSem.Value) (target : BvlSem.Value)
    (sourceArgs : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (application : ClosSem.AppKind) (result : Result (List ClosSem.Value) ClosSem.Value)
    (clockBounded : s.clock ≤ clockBound)
    (found : ClosSem.destClosure s.maxApp (some address) function sourceArgs = some application)
    (run : ClosSem.evaluateApp (some address) function sourceArgs s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code function target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceArgs targetArgs)
    (bodyIH : ∀ body : ClosLang.Exp, expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [.call (targetArgs.length - 1) (some (address + numStubs s.maxApp))
        ((List.range targetArgs.length).map Bvl.Exp.var ++ [.var targetArgs.length])] := by
  have bound := vRel_direct_args_bound functionRel found
  have sourceNonempty : sourceArgs ≠ [] := by
    cases application with
    | partialApp value => exact False.elim (ClosSem.destClosure_direct_not_partial _ _ _ _ _ found)
    | fullApp body env remaining =>
      have h := ClosSem.destClosure_full_remaining_lt s.maxApp (some address) function sourceArgs env remaining body found
      intro empty
      simp [empty] at h
  have targetNonempty : targetArgs ≠ [] := by
    intro empty
    have length := argsRel.length_eq
    simp [empty] at length
    exact sourceNonempty length
  have genericRun : ClosSem.evaluateApp none function sourceArgs s = (result, sFinal) := by
    rw [← ClosSem.evaluateApp_direct_eq_generic address function sourceArgs s application bound found]
    exact run
  have post := applicationSimulationThrough_of_body_simulationBelow clockBound bodyIH sourceArgs sourceNonempty
    s sFinal t f function target targetArgs rest result clockBounded genericRun noType states annotations functionRel argsRel
  obtain ⟨extra, targetResult, tFinal, fFinal, targetRun, resultRelated, finalStates, map, frame,
    finalAnnotations, finalClock⟩ := post
  refine ⟨extra, targetResult, tFinal, fFinal, ?_, resultRelated, finalStates, map, frame, finalAnnotations, finalClock⟩
  have same := evaluate_directCall_eq_generic { t with clock := s.clock + extra } s.maxApp address f function target
    sourceArgs targetArgs rest application (by simpa using functionRel) (by simpa using argsRel) found targetNonempty
  rw [same]
  exact targetRun


/-- Compose argument, function, and known-location call simulations. -/
theorem evaluatePost_app_direct_success {C F : Type}
    (s sArgs sFunction sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (address : Nat) (application : ClosSem.AppKind) (sourceArgs : List ClosLang.Exp) (sourceFunction : ClosLang.Exp)
    (targetArgs : List Bvl.Exp) (targetFunction : Bvl.Exp) (values : List ClosSem.Value)
    (function : ClosSem.Value) (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate sourceArgs sourceEnv s = (.val values, sArgs))
    (functionRun : ClosSem.evaluate [sourceFunction] sourceEnv sArgs = (.val [function], sFunction))
    (selected : ClosSem.destClosure sFunction.maxApp (some address) function values = some application)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv)
    (argsPost : evaluatePost s sArgs t targetEnv f (.val values) targetArgs)
    (functionIH : ∀ (tArgs : BvlSem.State C F) (fArgs : HolFiniteMapExact Nat Nat),
      stateRel fArgs sArgs tArgs → envRel sArgs.maxApp fArgs tArgs.refs tArgs.code sourceEnv targetEnv →
      codeAnnotations sArgs → sptSubspt t.code tArgs.code →
      evaluatePost sArgs sFunction tArgs targetEnv fArgs (.val [function]) [targetFunction])
    (appIH : ∀ (targetValues : List BvlSem.Value) (targetClosure : BvlSem.Value)
      (tFunction : BvlSem.State C F) (fFunction : HolFiniteMapExact Nat Nat),
      stateRel fFunction sFunction tFunction → codeAnnotations sFunction →
      List.Forall₂ (vRel sFunction.maxApp fFunction tFunction.refs tFunction.code) values targetValues →
      vRel sFunction.maxApp fFunction tFunction.refs tFunction.code function targetClosure →
      evaluatePost sFunction sFinal tFunction (targetValues ++ [targetClosure] ++ targetEnv) fFunction result
        [.call (targetValues.length - 1) (some (address + numStubs sFunction.maxApp))
          ((List.range targetValues.length).map Bvl.Exp.var ++ [.var targetValues.length])]) :
    evaluatePost s sFinal t targetEnv f result [appTarget s.maxApp (some address) targetArgs targetFunction] := by
  have maxArgs : sArgs.maxApp = s.maxApp := by
    have h := (ClosProps.evaluate_const (C := C) (F := F)).1 sourceArgs sourceEnv s
    rw [argsRun] at h
    exact h
  have maxFunction : sFunction.maxApp = sArgs.maxApp := by
    have h := (ClosProps.evaluate_const (C := C) (F := F)).1 [sourceFunction] sourceEnv sArgs
    rw [functionRun] at h
    exact h
  obtain ⟨clock1, argsResult, tArgs, fArgs, targetArgsRun, argsRel, states1, map1, frame1,
    annotations1, clocks1, growth1, env1⟩ :=
      evaluatePost_environment s sArgs t sourceEnv targetEnv f (.val values) targetArgs envRelated argsPost
  cases argsResult with
  | err error => simp [resultRel] at argsRel
  | val targetValues =>
    have argsRel1 : List.Forall₂ (vRel sArgs.maxApp fArgs tArgs.refs tArgs.code) values targetValues := by
      simpa [resultRel, maxArgs] using argsRel
    have envArgs : envRel sArgs.maxApp fArgs tArgs.refs tArgs.code sourceEnv targetEnv := by
      simpa [maxArgs] using env1
    obtain ⟨clock2, functionResult, tFunction, fFunction, targetFunctionRun, functionRel, states2, map2,
      frame2, annotations2, clocks2⟩ := functionIH tArgs fArgs states1 envArgs annotations1 growth1
    cases functionResult with
    | err error => simp [resultRel] at functionRel
    | val targetFunctions =>
      have singleton : List.Forall₂ (vRel sFunction.maxApp fFunction tFunction.refs tFunction.code)
          [function] targetFunctions := by simpa [resultRel, maxFunction] using functionRel
      cases singleton with
      | @cons _ targetClosure _ _ headRel tail =>
        cases tail
        have growth2 : sptSubspt tArgs.code tFunction.code :=
          BvlProps.evaluateMono [targetFunction] targetEnv { tArgs with clock := sArgs.clock + clock2 }
            (.val [targetClosure]) tFunction targetFunctionRun
        have argsRel2 : List.Forall₂ (vRel sFunction.maxApp fFunction tFunction.refs tFunction.code)
            values targetValues := by
          apply argsRel1.imp
          intro a b head
          simpa [maxFunction] using vRel_grow head map2 frame2 growth2
        obtain ⟨clock3, targetResult, tFinal, fFinal, targetCallRun, related, states3, map3, frame3,
          annotations3, clocks3⟩ := appIH targetValues targetClosure tFunction fFunction states2 annotations2 argsRel2 headRel
        have targetLength : targetValues.length = targetArgs.length :=
          BvlSem.evaluate_length targetArgs targetEnv { t with clock := s.clock + clock1 } tArgs targetValues targetArgsRun
        have shiftArgs := BvlProps.evaluate_addClock targetArgs targetEnv { t with clock := s.clock + clock1 }
          tArgs (.val targetValues) (clock2 + clock3) targetArgsRun (by simp)
        have runArgs : BvlSem.evaluate targetArgs targetEnv { t with clock := s.clock + (clock1 + clock2 + clock3) } =
            (.val targetValues, { tArgs with clock := sArgs.clock + (clock2 + clock3) }) := by
          simpa [Nat.add_assoc, clocks1] using shiftArgs
        have shiftFunction := BvlProps.evaluate_addClock [targetFunction] targetEnv
          { tArgs with clock := sArgs.clock + clock2 } tFunction (.val [targetClosure]) clock3 targetFunctionRun (by simp)
        have runFunction : BvlSem.evaluate [targetFunction] targetEnv
            { tArgs with clock := sArgs.clock + (clock2 + clock3) } =
            (.val [targetClosure], { tFunction with clock := sFunction.clock + clock3 }) := by
          simpa [Nat.add_assoc, clocks2] using shiftFunction
        refine ⟨clock1 + clock2 + clock3, targetResult, tFinal, fFinal, ?_, ?_, states3,
          HolFiniteMapExact.submap_trans (HolFiniteMapExact.submap_trans map1 map2) map3,
          unmappedRefsSubmap_trans (unmappedRefsSubmap_trans frame1 frame2) frame3, annotations3, clocks3⟩
        · obtain ⟨entry, targetFound⟩ := vRel_direct_findCode headRel argsRel2 selected
          have targetNonempty : targetValues ≠ [] := by
            intro empty
            have sourceLength := argsRel2.length_eq
            have valueEmpty : values = [] := by simpa [empty] using sourceLength
            cases application with
            | partialApp value => exact ClosSem.destClosure_direct_not_partial _ _ _ _ _ selected
            | fullApp body env rest =>
              have shorter := ClosSem.destClosure_full_remaining_lt sFunction.maxApp (some address)
                function values env rest body selected
              simp [valueEmpty] at shorter
          have targetFound' : BvlSem.findCode (some (address + numStubs s.maxApp))
              (targetValues ++ [targetClosure]) tFunction.code = some (targetValues ++ [targetClosure], entry) := by
            simpa [maxFunction, maxArgs] using targetFound
          rw [evaluate_appTarget_direct _ _ _ _ _ _ _ _ _ _ _ runArgs runFunction (by simpa using targetFound')]
          have callRun := evaluate_directCall_env { tFunction with clock := sFunction.clock + clock3 }
            targetValues targetEnv targetClosure (address + numStubs s.maxApp) entry targetNonempty (by simpa using targetFound')
          rw [maxFunction, maxArgs, callRun] at targetCallRun
          have count : targetArgs.length - 1 + 1 = targetValues.length := by
            have positive := List.length_pos_iff.mpr targetNonempty
            omega
          simpa [count] using targetCallRun
        · simpa [maxFunction, maxArgs] using related


/-- A nonempty known-location application that avoids a type error must
select a closure case. -/
theorem evaluateApp_direct_destClosure_some {C F : Type} (s sFinal : ClosSem.State C F)
    (address : Nat) (value : ClosSem.Value) (args : List ClosSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (nonempty : args ≠ []) (run : ClosSem.evaluateApp (some address) value args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) :
    ∃ application, ClosSem.destClosure s.maxApp (some address) value args = some application := by
  cases args with
  | nil => contradiction
  | cons head tail =>
    cases selected : ClosSem.destClosure s.maxApp (some address) value (head :: tail) with
    | none =>
      rw [ClosSem.evaluateApp, selected] at run
      change (.err (.abort .typeError), s) = (result, sFinal) at run
      cases run
      exact False.elim (noType rfl)
    | some application => exact ⟨application, rfl⟩


/-- A successful direct application expression follows from its bounded subexpressions and closure bodies. -/
theorem expressionSimulation_app_direct_success_belowBound {C F : Type}
    (s sArgs sFunction sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (clockBound appBound : Nat)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (trace : BackendCommon.Tra) (address : Nat) (args : List ClosLang.Exp) (function : ClosLang.Exp)
    (values : List ClosSem.Value) (functionValue : ClosSem.Value)
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate args sourceEnv s = (.val values, sArgs))
    (functionRun : ClosSem.evaluate [function] sourceEnv sArgs =
      (.val [functionValue], sFunction))
    (run : ClosSem.evaluate [.app trace (some address) function args] sourceEnv s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (clockBounded : s.clock < clockBound) (callerBound : s.clock ≤ appBound)
    (compile : compileExpsHOL s.maxApp [.app trace (some address) function args] aux = (compiled, finalAux))
    (locations : ClosProps.everyFnLocationSome [.app trace (some address) function args]) (annotations : codeAnnotations s)
    (vars : ClosProps.everyFnVarsSome [.app trace (some address) function args]) (installed : codeInstalled finalAux t.code)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv) (states : stateRel f s t)
    (argsIH : expressionSimulationBelow (C := C) (F := F) clockBound args)
    (functionIH : expressionSimulationBelow (C := C) (F := F) clockBound [function])
    (bodyIH : ∀ body : ClosLang.Exp, expressionSimulationBelow (C := C) (F := F) appBound [body])
    :
    evaluatePost s sFinal t targetEnv f result compiled := by
  have nonempty : args ≠ [] := by
    intro empty
    subst args
    simp [ClosSem.evaluate] at run
    exact noType run.1.symm
  have valuesNonempty : values ≠ [] := by
    intro empty
    have h := (ClosSem.evaluate_length (C := C) (F := F)).1 args sourceEnv s sArgs values argsRun
    simp [empty] at h
    apply nonempty
    cases args with
    | nil => rfl
    | cons head tail => simp at h
  have appRun : ClosSem.evaluateApp (some address) functionValue values sFunction =
      (result, sFinal) := by
    have notEmpty : args.isEmpty = false := by cases args <;> simp_all
    rw [ClosSem.evaluate] at run
    simp only [notEmpty, Bool.false_eq_true, ↓reduceIte] at run
    rw [ClosSem.fixClock_evaluate, argsRun] at run
    dsimp only at run
    rw [ClosSem.fixClock_evaluate, functionRun] at run
    exact run
  obtain ⟨application, selected⟩ := evaluateApp_direct_destClosure_some sFunction sFinal address functionValue values result valuesNonempty appRun noType
  cases functionCompile : compileExpHOL s.maxApp function aux with
  | mk targetFunction middleAux =>
    cases argsCompile : compileExpListHOL s.maxApp args middleAux with
    | mk targetArgs lastAux =>
      have whole := compile_appTarget s.maxApp trace (some address) function args aux middleAux lastAux
        targetFunction targetArgs functionCompile argsCompile
      have equal := compile.symm.trans whole
      cases equal
      have argsCompiled : compileExpsHOL s.maxApp args middleAux = (targetArgs, finalAux) := by
        rw [compileExps_eq_list]
        exact argsCompile
      have functionCompiled : compileExpsHOL s.maxApp [function] aux = ([targetFunction], middleAux) := by
        rw [compileExps_eq_list]
        simp [compileExpListHOL, functionCompile]
      have functionInstalled : codeInstalled middleAux t.code :=
        compileExps_codeInstalled s.maxApp args middleAux finalAux targetArgs t.code argsCompiled installed
      have locationsParts : ClosProps.fnLocationSomeExp function ∧ ClosProps.everyFnLocationSome args := by
        simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
      have varsParts : ClosProps.fnVarsSomeExp function ∧ ClosProps.everyFnVarsSome args := by
        simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using vars
      have argsPost := argsIH s sArgs t sourceEnv targetEnv f middleAux finalAux targetArgs (.val values)
        clockBounded argsRun (by simp) argsCompiled locationsParts.2 annotations varsParts.2 installed envRelated states
      apply evaluatePost_app_direct_success s sArgs sFunction sFinal t sourceEnv targetEnv f address application args function
        targetArgs targetFunction values functionValue result argsRun functionRun selected envRelated argsPost
      · intro tArgs fArgs statesArgs envArgs annotationsArgs growth
        have maxApp : sArgs.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        have argsClock : sArgs.clock < clockBound := by
          have h := ClosSem.evaluate_clock_le args sourceEnv s
          rw [argsRun] at h
          dsimp only at h
          omega
        exact functionIH sArgs sFunction tArgs sourceEnv targetEnv fArgs aux middleAux [targetFunction]
          (.val [functionValue]) argsClock functionRun (by simp)
          (by simpa [maxApp] using functionCompiled)
          (by simpa [ClosProps.everyFnLocationSome] using locationsParts.1) annotationsArgs
          (by simpa [ClosProps.everyFnVarsSome] using varsParts.1)
          (codeInstalled_subspt functionInstalled growth) envArgs statesArgs

      · intro targetValues targetClosure tFunction fFunction functionStates functionAnnotations argsRel functionRel
        have functionClock : sFunction.clock ≤ appBound := by
          have first := ClosSem.evaluate_clock_le args sourceEnv s
          rw [argsRun] at first
          have second := ClosSem.evaluate_clock_le [function] sourceEnv sArgs
          rw [functionRun] at second
          dsimp only at first second
          omega
        exact evaluateApp_direct_simulation_below sFunction sFinal tFunction fFunction address appBound
          functionValue targetClosure values targetValues targetEnv application result functionClock selected appRun noType
          functionStates functionAnnotations functionRel argsRel bodyIH



/-- Known-location applications preserve the bounded simulation. -/
theorem expressionSimulation_app_direct_case_bounded {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (clockBound appBound : Nat)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (trace : BackendCommon.Tra) (address : Nat) (args : List ClosLang.Exp) (function : ClosLang.Exp)
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.app trace (some address) function args] sourceEnv s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (clockBounded : s.clock < clockBound) (callerBound : s.clock ≤ appBound)
    (compile : compileExpsHOL s.maxApp [.app trace (some address) function args] aux = (compiled, finalAux))
    (locations : ClosProps.everyFnLocationSome [.app trace (some address) function args]) (annotations : codeAnnotations s)
    (vars : ClosProps.everyFnVarsSome [.app trace (some address) function args]) (installed : codeInstalled finalAux t.code)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv) (states : stateRel f s t)
    (argsIH : expressionSimulationBelow (C := C) (F := F) clockBound args)
    (functionIH : expressionSimulationBelow (C := C) (F := F) clockBound [function])
    (bodyIH : ∀ body : ClosLang.Exp, expressionSimulationBelow (C := C) (F := F) appBound [body]) :
    evaluatePost s sFinal t targetEnv f result compiled := by
  have nonempty : args ≠ [] := by
    intro empty
    subst args
    simp [ClosSem.evaluate] at run
    exact noType run.1.symm
  have notEmpty : args.isEmpty = false := by cases args <;> simp_all
  cases argsRun : ClosSem.evaluate args sourceEnv s with
  | mk argsResult sArgs =>
    cases argsResult with
    | err error =>
      have sourceRun := run
      rw [ClosSem.evaluate] at sourceRun
      simp only [notEmpty, Bool.false_eq_true, ↓reduceIte] at sourceRun
      rw [ClosSem.fixClock_evaluate, argsRun] at sourceRun
      simp only at sourceRun
      cases sourceRun
      exact expressionSimulation_app_preCall_error_case_below s sFinal t clockBound sourceEnv targetEnv f trace (some address) args function
        aux finalAux compiled (.err error) run noType clockBounded (Or.inl ⟨error, argsRun⟩) compile locations annotations vars
        installed envRelated states argsIH functionIH
    | val values =>
      cases functionRun : ClosSem.evaluate [function] sourceEnv sArgs with
      | mk functionResult sFunction =>
        cases functionResult with
        | err error =>
          have sourceRun := run
          rw [ClosSem.evaluate] at sourceRun
          simp only [notEmpty, Bool.false_eq_true, ↓reduceIte] at sourceRun
          rw [ClosSem.fixClock_evaluate, argsRun] at sourceRun
          dsimp only at sourceRun
          rw [ClosSem.fixClock_evaluate, functionRun] at sourceRun
          simp only at sourceRun
          cases sourceRun
          exact expressionSimulation_app_preCall_error_case_below s sFinal t clockBound sourceEnv targetEnv f trace (some address) args function
            aux finalAux compiled (.err error) run noType clockBounded (Or.inr ⟨values, sArgs, error, argsRun, functionRun⟩)
            compile locations annotations vars installed envRelated states argsIH functionIH
        | val functions =>
          have functionLength : functions.length = 1 := by
            have h := (ClosSem.evaluate_length (C := C) (F := F)).1 [function] sourceEnv sArgs sFunction functions functionRun
            simpa using h
          cases functions with
          | nil => simp at functionLength
          | cons functionValue tail =>
            cases tail with
            | cons head tail => simp at functionLength
            | nil =>
              exact expressionSimulation_app_direct_success_belowBound s sArgs sFunction sFinal t clockBound appBound sourceEnv targetEnv f
                trace address args function values functionValue aux finalAux compiled result argsRun functionRun run noType clockBounded callerBound
                compile locations annotations vars installed envRelated states argsIH functionIH bodyIH


/-- A known-location application follows from the structural hypotheses at
the current bound and the closure-body hypothesis at the predecessor bound. -/
theorem expressionSimulationBelow_directApp_succ {C F : Type} (clockBound : Nat)
    (trace : BackendCommon.Tra) (address : Nat) (args : List ClosLang.Exp) (function : ClosLang.Exp)
    (argsIH : expressionSimulationBelow (C := C) (F := F) (clockBound + 1) args)
    (functionIH : expressionSimulationBelow (C := C) (F := F) (clockBound + 1) [function])
    (bodyIH : ∀ body : ClosLang.Exp, expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    expressionSimulationBelow (C := C) (F := F) (clockBound + 1) [.app trace (some address) function args] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result clockBounded run noType compile
    locations annotations vars installed envRelated states
  exact expressionSimulation_app_direct_case_bounded s sFinal t (clockBound + 1) clockBound
    sourceEnv targetEnv f trace address args function aux finalAux compiled result run noType clockBounded (by omega)
    compile locations annotations vars installed envRelated states argsIH functionIH bodyIH

/-- Applications with either inferred or explicit locations share the same
successor-clock induction hypotheses. -/
theorem expressionSimulationBelow_app_any_succ {C F : Type} (clockBound : Nat)
    (trace : BackendCommon.Tra) (location : Option Nat) (args : List ClosLang.Exp) (function : ClosLang.Exp)
    (argsIH : expressionSimulationBelow (C := C) (F := F) (clockBound + 1) args)
    (functionIH : expressionSimulationBelow (C := C) (F := F) (clockBound + 1) [function])
    (bodyIH : ∀ body : ClosLang.Exp, expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    expressionSimulationBelow (C := C) (F := F) (clockBound + 1) [.app trace location function args] := by
  cases location with
  | none => exact expressionSimulationBelow_app_succ clockBound trace args function argsIH functionIH bodyIH
  | some address => exact expressionSimulationBelow_directApp_succ clockBound trace address args function argsIH functionIH bodyIH

end Flapjack.Compiler.Backend.ClosToBvl
