import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ChainEvaluation
import Flapjack.Compiler.Backend.Semantics.BvlProps.ApplyClock

/-! Installation expression cases of the closure-to-BVL simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

private instance : Nonempty ClosSem.Value := ⟨ClosSem.unitValue⟩

private theorem reverse_related {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (related : List.Forall₂ R xs ys) : List.Forall₂ R xs.reverse ys.reverse := by
  have appendRel : ∀ {a c : List α} {b d : List β}, List.Forall₂ R a b →
      List.Forall₂ R c d → List.Forall₂ R (a ++ c) (b ++ d) := by
    intro a c b d first second
    induction first with
    | nil => exact second
    | cons head tail ih => exact .cons head ih
  induction related with
  | nil => exact .nil
  | cons head tail ih => simpa using appendRel ih (.cons head .nil)

/-- Errors from the installation argument list propagate through the target
installation operation and its generated indirect call. -/
theorem evaluatePost_install_args_error {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (targetArgs : List Bvl.Exp) (error : ErrorResult ClosSem.Value)
    (post : evaluatePost s sFinal t targetEnv f (.err error) targetArgs) :
    evaluatePost s sFinal t targetEnv f (.err error) [.call 0 none [.op .install targetArgs]] := by
  obtain ⟨extra, targetResult, tFinal, fFinal, run, related, states, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨extra, .err targetError, tFinal, fFinal, ?_, related, states, map, refs, annotations, clocks⟩
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- Successful installation and execution of the installed body compose with
the argument simulation and the generated indirect target call. -/
theorem evaluatePost_install_success {C F : Type}
    (s sArgs sInstalled sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (sourceArgs : List ClosLang.Exp) (targetArgs : List Bvl.Exp)
    (values : List ClosSem.Value) (expressions : List ClosLang.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value) (clockBound : Nat)
    (argsRun : ClosSem.evaluate sourceArgs sourceEnv s = (.val values, sArgs))
    (installRun : ClosSem.doInstall values.reverse sArgs = (.val expressions, sInstalled))
    (bodyRun : ClosSem.evaluate expressions [] sInstalled = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bound : s.clock ≤ clockBound)
    (argsPost : evaluatePost s sArgs t targetEnv f (.val values) targetArgs)
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound expressions) :
    evaluatePost s sFinal t targetEnv f
      (match result with | .err error => .err error | .val vs => .val [Flapjack.holLast vs])
      [.call 0 none [.op .install targetArgs]] := by
  have maxApp : sArgs.maxApp = s.maxApp := by
    have h := (ClosProps.evaluate_const (C := C) (F := F)).1 sourceArgs sourceEnv s
    rw [argsRun] at h
    exact h
  have argsBound : sArgs.clock ≤ clockBound := by
    have h := ClosSem.evaluate_clock_le sourceArgs sourceEnv s
    rw [argsRun] at h
    dsimp only at h
    omega
  obtain ⟨clock1, targetResult, tArgs, fArgs, targetRun, related, states, map1, refs1,
    annotations, clocks⟩ := argsPost
  cases targetResult with
  | err error => simp [resultRel] at related
  | val targetValues =>
    have valuesRel : List.Forall₂ (vRel sArgs.maxApp fArgs tArgs.refs tArgs.code)
        values.reverse targetValues.reverse := by
      simpa [resultRel, maxApp] using reverse_related related
    obtain ⟨auxiliary, start, body, extra, finalResult, tFinal, fFinal,
      targetInstall, found, bodyTargetRun, resultRelated, finalStates, map2, refs2,
      finalAnnotations, finalClocks⟩ :=
        install_success_body_simulation sArgs sInstalled sFinal tArgs fArgs values.reverse targetValues.reverse
          expressions result clockBound installRun bodyRun noType argsBound valuesRel states annotations bodyIH
    dsimp only at targetInstall found bodyTargetRun refs2
    let targetNext := { tArgs with
      code := sptUnion tArgs.code (sptFromAList (compileInc sArgs.maxApp (expressions, auxiliary)))
      compileOracle := fun n => tArgs.compileOracle (n + 1) }
    have shifted := BvlProps.evaluate_addClock targetArgs targetEnv
      { t with clock := s.clock + clock1 } tArgs (.val targetValues) extra targetRun (by simp)
    have runArgs : BvlSem.evaluate targetArgs targetEnv { t with clock := s.clock + (clock1 + extra) } =
        (.val targetValues, { tArgs with clock := sArgs.clock + extra }) := by
      simpa [Nat.add_assoc, clocks] using shifted
    have shiftedInstall := BvlProps.doInstall_setClock targetValues.reverse tArgs (sArgs.clock + extra)
    rw [targetInstall] at shiftedInstall
    have install' : BvlSem.doInstall (R := BvlSem.Value) targetValues.reverse { tArgs with clock := sArgs.clock + extra } =
        .val (.codePtr (start + numStubs sArgs.maxApp), { targetNext with clock := sArgs.clock + extra }) := by
      simpa [BvlProps.setClockResult, targetNext] using shiftedInstall
    have found' : BvlSem.findCode none [.codePtr (start + numStubs sArgs.maxApp)]
        { targetNext with clock := sArgs.clock + extra }.code = some ([], body) := by
      simpa [targetNext] using found
    have successClock := ClosSem.doInstall_success_clock values.reverse sArgs sInstalled expressions installRun
    have positive : sArgs.clock + extra ≠ 0 := by omega
    have nonzero : sArgs.clock ≠ 0 := by omega
    have clockEq : sArgs.clock + extra - 1 = sInstalled.clock + extra := by omega
    refine ⟨clock1 + extra, chainResult finalResult, tFinal, fFinal, ?_, ?_, finalStates,
      relocationSubmap_trans map1 map2, ?_, finalAnnotations, finalClocks⟩
    · rw [evaluate_install_target_call _ _ _ _ _ _ _ _ runArgs install' found']
      simpa [targetNext, positive, nonzero, BvlSem.decClock, clockEq] using bodyTargetRun
    · cases result <;> simpa [maxApp] using resultRelated
    · exact unmappedRefsSubmap_trans refs1 (by simpa [targetNext] using refs2)

/-- A valid installation at zero source clock updates both code states and
then times out at the generated indirect call. -/
theorem evaluatePost_install_timeout {C F : Type}
    (s sArgs sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (sourceArgs : List ClosLang.Exp) (targetArgs : List Bvl.Exp)
    (values : List ClosSem.Value)
    (argsRun : ClosSem.evaluate sourceArgs sourceEnv s = (.val values, sArgs))
    (installRun : ClosSem.doInstall values.reverse sArgs = (.err (.abort .timeoutError), sFinal))
    (argsPost : evaluatePost s sArgs t targetEnv f (.val values) targetArgs) :
    evaluatePost s sFinal t targetEnv f (.err (.abort .timeoutError)) [.call 0 none [.op .install targetArgs]] := by
  have maxApp : sArgs.maxApp = s.maxApp := by
    have h := (ClosProps.evaluate_const (C := C) (F := F)).1 sourceArgs sourceEnv s
    rw [argsRun] at h
    exact h
  obtain ⟨clock, targetResult, tArgs, fArgs, targetRun, related, states, map, refs,
    annotations, clocks⟩ := argsPost
  cases targetResult with
  | err error => simp [resultRel] at related
  | val targetValues =>
    have valuesRel : List.Forall₂ (vRel sArgs.maxApp fArgs tArgs.refs tArgs.code)
        values.reverse targetValues.reverse := by
      simpa [resultRel, maxApp] using reverse_related related
    obtain ⟨sourceBytes, sourceWords, bytes, words, config, expressions, auxiliary, nextConfig,
      valuesEq, bytesRun, wordsRun, sourceHead, compiledBytes, sourceNext, nonempty, _, _, nextEq, resultEq⟩ :=
        install_source_inv sArgs sFinal values.reverse (.err (.abort .timeoutError)) installRun (by simp)
    have zero : sArgs.clock = 0 := by
      split at resultEq <;> simp_all
    have targetZero : tArgs.clock = 0 := by omega
    have oracle := states.2.2.2.2.2.2.2.2.2.2.2.1
    have nextStates := install_stateRel sArgs tArgs fArgs config expressions auxiliary sourceHead states
    have nextAnnotations := install_codeAnnotations sArgs tArgs config expressions auxiliary sourceHead annotations oracle
    rw [valuesEq] at valuesRel
    generalize targetEq : targetValues.reverse = targets at valuesRel
    cases valuesRel with
    | cons bytesRel tailRel =>
      cases tailRel with
      | cons wordsRel tailRel =>
        cases tailRel
        obtain ⟨start, body, tail, extracted, program, targetInstall⟩ :=
          install_target_run sArgs tArgs fArgs sourceBytes sourceWords _ _ bytes words config nextConfig
            expressions auxiliary bytesRel wordsRel bytesRun wordsRun sourceHead sourceNext compiledBytes oracle
        obtain ⟨start', body', tail', extracted', program', found⟩ :=
          install_main_findCode sArgs tArgs config expressions auxiliary sourceHead oracle
        have startEq : start' = start := extracted'.symm.trans extracted
        subst start'
        rw [program] at program'
        simp only [extracted, List.cons.injEq, Prod.mk.injEq, true_and] at program'
        obtain ⟨bodyEq, _⟩ := program'
        subst body'
        let targetNext := { tArgs with
          code := sptUnion tArgs.code (sptFromAList (compileInc sArgs.maxApp (expressions, auxiliary)))
          compileOracle := fun n => tArgs.compileOracle (n + 1) }
        have install' : BvlSem.doInstall (R := BvlSem.Value) targetValues.reverse tArgs =
            .val (.codePtr (start + numStubs sArgs.maxApp), targetNext) := by
          simpa [targetNext, extracted, targetEq] using targetInstall
        have found' : BvlSem.findCode none [.codePtr (start + numStubs sArgs.maxApp)] targetNext.code = some ([], body) := by
          simpa [targetNext, extracted] using found
        refine ⟨clock, .err (.abort .timeoutError), targetNext, fArgs, ?_, by simp [resultRel, excRel], ?_, map,
          ?_, ?_, ?_⟩
        · rw [evaluate_install_target_call _ _ _ _ _ _ _ _ targetRun install' found']
          simp [targetNext, targetZero]
        · simpa [nextEq, targetNext] using nextStates
        · simpa [targetNext] using refs
        · simpa [nextEq, codeAnnotations] using nextAnnotations
        · simp [nextEq, targetNext, zero, targetZero]

/-- The installation expression case, using the smaller-clock induction
hypothesis for code obtained from the dynamic compilation oracle. -/
theorem expressionSimulationBelow_install_succ {C F : Type} (clockBound : Nat)
    (trace : BackendCommon.Tra) (args : List ClosLang.Exp)
    (argsIH : expressionSimulationBelow (C := C) (F := F) (clockBound + 1) args)
    (bodyIH : ∀ expressions, expressionSimulationBelow (C := C) (F := F) clockBound expressions) :
    expressionSimulationBelow (C := C) (F := F) (clockBound + 1) [.op trace .install args] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result clockBounded run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases argsCompile : compileExpListHOL s.maxApp args aux with
  | mk targetArgs aux1 =>
    have argsCompiled : compileExpsHOL s.maxApp args aux = (targetArgs, aux1) := by
      rw [compileExps_eq_list]
      exact argsCompile
    have wholeCompiled : compileExpsHOL s.maxApp [.op trace .install args] aux =
        ([.call 0 none [.op .install targetArgs]], aux1) := by
      rw [compileExps_eq_list]
      simp [compileExpListHOL, compileExpHOL, argsCompile]
    have equal := compile.symm.trans wholeCompiled
    cases equal
    have argsLoc : ClosProps.everyFnLocationSome args := by
      simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
    have argsVars : ClosProps.everyFnVarsSome args := by
      simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using varsAnnotated
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
    cases argsRun : ClosSem.evaluate args sourceEnv s with
    | mk argsResult sArgs =>
      rw [argsRun] at run
      cases argsResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact evaluatePost_install_args_error s sArgs t targetEnv f targetArgs error
          (argsIH s sArgs t sourceEnv targetEnv f aux finalAux targetArgs (.err error)
            clockBounded argsRun noTypeError argsCompiled argsLoc annotations argsVars installed envRelated states)
      | val values =>
        dsimp only at run
        have argsPost := argsIH s sArgs t sourceEnv targetEnv f aux finalAux targetArgs (.val values)
          clockBounded argsRun (by simp) argsCompiled argsLoc annotations argsVars installed envRelated states
        cases installRun : ClosSem.doInstall values.reverse sArgs with
        | mk installResult sInstalled =>
          rw [installRun] at run
          cases installResult with
          | err error =>
            simp at run
            rcases run with ⟨rfl, rfl⟩
            have noType : (.err error : Result (List ClosLang.Exp) ClosSem.Value) ≠ .err (.abort .typeError) := by
              simpa using noTypeError
            obtain ⟨_, _, _, _, _, expressions, _, _, _, _, _, _, _, _, _, _, _, _, shape⟩ :=
              install_source_inv sArgs sInstalled values.reverse (.err error) installRun noType
            have errorEq : error = .abort .timeoutError := by
              split at shape <;> simp_all
            subst error
            exact evaluatePost_install_timeout s sArgs sInstalled t sourceEnv targetEnv f args targetArgs values
              argsRun installRun argsPost
          | val expressions =>
            dsimp only at run
            cases bodyRun : ClosSem.evaluate expressions [] sInstalled with
            | mk bodyResult sLast =>
              rw [bodyRun] at run
              cases bodyResult with
              | err error =>
                simp at run
                rcases run with ⟨rfl, rfl⟩
                exact evaluatePost_install_success s sArgs sInstalled sLast t sourceEnv targetEnv f args targetArgs
                  values expressions (.err error) clockBound argsRun installRun bodyRun noTypeError (by omega)
                  argsPost (bodyIH expressions)
              | val output =>
                simp at run
                rcases run with ⟨rfl, rfl⟩
                exact evaluatePost_install_success s sArgs sInstalled sLast t sourceEnv targetEnv f args targetArgs
                  values expressions (.val output) clockBound argsRun installRun bodyRun (by simp) (by omega)
                  argsPost (bodyIH expressions)

end Flapjack.Compiler.Backend.ClosToBvl
