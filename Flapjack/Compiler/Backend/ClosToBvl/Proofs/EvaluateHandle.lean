module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateLet

@[expose] public section

/-! Exception-handler case of the closure-to-BVL simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- A returned value passes unchanged through a target handler. -/
theorem evaluatePost_handle_value {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (body handler : Bvl.Exp) (values : List ClosSem.Value)
    (post : evaluatePost s sFinal t targetEnv f (.val values) [body]) :
    evaluatePost s sFinal t targetEnv f (.val values) [.handle body handler] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | err error => simp [resultRel] at related
  | val targetValues =>
    refine ⟨clock, .val targetValues, tFinal, fFinal, ?_, related, state, map, refs, annotations, clocks⟩
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- An abort passes unchanged through a target handler. -/
theorem evaluatePost_handle_abort {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (body handler : Bvl.Exp) (reason : Abort)
    (post : evaluatePost s sFinal t targetEnv f (.err (.abort reason)) [body]) :
    evaluatePost s sFinal t targetEnv f (.err (.abort reason)) [.handle body handler] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err error =>
    cases error with
    | raise value => simp [resultRel, excRel] at related
    | abort targetReason =>
      refine ⟨clock, .err (.abort targetReason), tFinal, fFinal, ?_, related, state, map, refs, annotations, clocks⟩
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- A raised payload extends both related environments before the handler is
simulated, with sufficient clock supplied to both stages. -/
theorem evaluatePost_handle_raise {C F : Type}
    (s sMiddle sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (sourceBody : ClosLang.Exp) (targetBody targetHandler : Bvl.Exp)
    (value : ClosSem.Value) (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyRun : ClosSem.evaluate [sourceBody] sourceEnv s = (.err (.raise value), sMiddle))
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv)
    (bodyPost : evaluatePost s sMiddle t targetEnv f (.err (.raise value)) [targetBody])
    (handlerIH : ∀ (targetValue : BvlSem.Value) (tMiddle : BvlSem.State C F)
      (fMiddle : HolFiniteMapExact Nat Nat), stateRel fMiddle sMiddle tMiddle →
      envRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code (value :: sourceEnv) (targetValue :: targetEnv) →
      codeAnnotations sMiddle → sptSubspt t.code tMiddle.code →
      evaluatePost sMiddle sFinal tMiddle (targetValue :: targetEnv) fMiddle result [targetHandler]) :
    evaluatePost s sFinal t targetEnv f result [.handle targetBody targetHandler] := by
  have maxApp : sMiddle.maxApp = s.maxApp := by
    have h := (ClosProps.evaluate_const (C := C) (F := F)).1 [sourceBody] sourceEnv s
    rw [bodyRun] at h
    exact h
  obtain ⟨clock1, targetResult, tMiddle, fMiddle, targetRun1, related1, state1, map1, refs1,
    annotations1, clocks1, code1, env1⟩ :=
      evaluatePost_environment s sMiddle t sourceEnv targetEnv f (.err (.raise value)) [targetBody] envRelated bodyPost
  cases targetResult with
  | val values => simp [resultRel] at related1
  | err error =>
    cases error with
    | abort reason => simp [resultRel, excRel] at related1
    | raise targetValue =>
      have envMiddle : envRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code
          (value :: sourceEnv) (targetValue :: targetEnv) := by
        simpa [maxApp, envRel, resultRel, excRel] using And.intro related1 env1
      obtain ⟨clock2, result2, tFinal, fFinal, targetRun2, related2, state2, map2, refs2,
        annotations2, clocks2⟩ := handlerIH targetValue tMiddle fMiddle state1 envMiddle annotations1 code1
      have shifted := BvlProps.evaluate_addClock [targetBody] targetEnv
        { t with clock := s.clock + clock1 } tMiddle (.err (.raise targetValue)) clock2 targetRun1 (by simp)
      have runBody : BvlSem.evaluate [targetBody] targetEnv
          { t with clock := s.clock + (clock1 + clock2) } =
          (.err (.raise targetValue), { tMiddle with clock := sMiddle.clock + clock2 }) := by
        simpa [Nat.add_assoc, clocks1] using shifted
      refine ⟨clock1 + clock2, result2, tFinal, fFinal, ?_, ?_, state2,
        HolFiniteMapExact.submap_trans map1 map2, unmappedRefsSubmap_trans refs1 refs2, annotations2, clocks2⟩
      · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, runBody]
        exact targetRun2
      · simpa [maxApp] using related2

/-- Bounded simulation for exception handlers, including the handler clock bound. -/
theorem expressionSimulationBelow_handle {C F : Type} (clockBound : Nat) (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp)
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body])
    (handlerIH : expressionSimulationBelow (C := C) (F := F) clockBound [handler]) :
    expressionSimulationBelow (C := C) (F := F) clockBound [.handle trace body handler] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result clockBounded run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases bodyCompile : compileExpHOL s.maxApp body aux with
  | mk targetBody auxMiddle =>
    cases handlerCompile : compileExpHOL s.maxApp handler auxMiddle with
    | mk targetHandler auxLast =>
      have bodyCompiled : compileExpsHOL s.maxApp [body] aux = ([targetBody], auxMiddle) := by
        rw [compileExps_eq_list]
        simp [compileExpListHOL, bodyCompile]
      have handlerCompiled : compileExpsHOL s.maxApp [handler] auxMiddle = ([targetHandler], auxLast) := by
        rw [compileExps_eq_list]
        simp [compileExpListHOL, handlerCompile]
      have wholeCompiled : compileExpsHOL s.maxApp [.handle trace body handler] aux =
          ([.handle targetBody targetHandler], auxLast) := by
        rw [compileExps_eq_list]
        simp [compileExpListHOL, compileExpHOL, bodyCompile, handlerCompile]
      have equal := compile.symm.trans wholeCompiled
      cases equal
      have bodyInstalled : codeInstalled auxMiddle t.code :=
        compileExps_codeInstalled s.maxApp [handler] auxMiddle finalAux [targetHandler] t.code handlerCompiled installed
      have locs : ClosProps.fnLocationSomeExp body ∧ ClosProps.fnLocationSomeExp handler := by
        simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
      have vars : ClosProps.fnVarsSomeExp body ∧ ClosProps.fnVarsSomeExp handler := by
        simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using varsAnnotated
      have bodyLoc : ClosProps.everyFnLocationSome [body] := by simpa [ClosProps.everyFnLocationSome] using locs.1
      have handlerLoc : ClosProps.everyFnLocationSome [handler] := by simpa [ClosProps.everyFnLocationSome] using locs.2
      have bodyVars : ClosProps.everyFnVarsSome [body] := by simpa [ClosProps.everyFnVarsSome] using vars.1
      have handlerVars : ClosProps.everyFnVarsSome [handler] := by simpa [ClosProps.everyFnVarsSome] using vars.2
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
      cases bodyRun : ClosSem.evaluate [body] sourceEnv s with
      | mk bodyResult sMiddle =>
        rw [bodyRun] at run
        cases bodyResult with
        | val values =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          exact evaluatePost_handle_value s sMiddle t targetEnv f targetBody targetHandler values
            (bodyIH s sMiddle t sourceEnv targetEnv f aux auxMiddle [targetBody] (.val values)
              clockBounded bodyRun (by simp) bodyCompiled bodyLoc annotations bodyVars bodyInstalled envRelated states)
        | err error =>
          cases error with
          | abort reason =>
            simp at run
            rcases run with ⟨rfl, rfl⟩
            exact evaluatePost_handle_abort s sMiddle t targetEnv f targetBody targetHandler reason
              (bodyIH s sMiddle t sourceEnv targetEnv f aux auxMiddle [targetBody] (.err (.abort reason))
                clockBounded bodyRun noTypeError bodyCompiled bodyLoc annotations bodyVars bodyInstalled envRelated states)
          | raise value =>
            have handlerRun : ClosSem.evaluate [handler] (value :: sourceEnv) sMiddle = (result, sFinal) := run
            have bodyPost := bodyIH s sMiddle t sourceEnv targetEnv f aux auxMiddle [targetBody] (.err (.raise value))
              clockBounded bodyRun (by simp) bodyCompiled bodyLoc annotations bodyVars bodyInstalled envRelated states
            apply evaluatePost_handle_raise s sMiddle sFinal t sourceEnv targetEnv f body targetBody targetHandler
              value result bodyRun envRelated bodyPost
            intro targetValue tMiddle fMiddle middleStates middleEnv middleAnnotations growth
            have maxApp : sMiddle.maxApp = s.maxApp := by
              have h := (ClosProps.evaluate_const (C := C) (F := F)).1 [body] sourceEnv s
              rw [bodyRun] at h
              exact h
            have handlerCompiled' : compileExpsHOL sMiddle.maxApp [handler] auxMiddle = ([targetHandler], finalAux) := by
              simpa [maxApp] using handlerCompiled
            have middleClock : sMiddle.clock < clockBound := by
              have h := ClosSem.evaluate_clock_le [body] sourceEnv s
              rw [bodyRun] at h
              dsimp only at h
              omega
            exact handlerIH sMiddle sFinal tMiddle (value :: sourceEnv) (targetValue :: targetEnv) fMiddle
              auxMiddle finalAux [targetHandler] result middleClock handlerRun noTypeError handlerCompiled' handlerLoc
              middleAnnotations handlerVars (codeInstalled_subspt installed growth) middleEnv middleStates


end Flapjack.Compiler.Backend.ClosToBvl
