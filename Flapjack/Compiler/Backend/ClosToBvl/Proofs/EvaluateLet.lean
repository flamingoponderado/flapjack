import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateSequence

/-! Let-binding case of the closure-to-BVL expression simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- Related binding lists can be prepended to related environments. -/
theorem envRel_prepend {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {values : List ClosSem.Value} {targetValues : List BvlSem.Value}
    {env : List ClosSem.Value} {targetEnv : List BvlSem.Value}
    (valuesRel : List.Forall₂ (vRel maxApp f refs code) values targetValues)
    (envRelated : envRel maxApp f refs code env targetEnv) :
    envRel maxApp f refs code (values ++ env) (targetValues ++ targetEnv) := by
  induction valuesRel with
  | nil => exact envRelated
  | cons head tail ih => exact ⟨head, ih⟩

/-- An error in the bindings exits the target let with the same postcondition. -/
theorem evaluatePost_let_error {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (bindings : List Bvl.Exp) (body : Bvl.Exp)
    (error : ErrorResult ClosSem.Value)
    (post : evaluatePost s sFinal t targetEnv f (.err error) bindings) :
    evaluatePost s sFinal t targetEnv f (.err error) [.let bindings body] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨clock, .err targetError, tFinal, fFinal, ?_, related, state, map, refs, annotations, clocks⟩
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- Combine a successful binding simulation with the body simulation, after
extending the environment and aligning the target clocks. -/
theorem evaluatePost_let_success {C F : Type}
    (s sMiddle sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (sourceBindings : List ClosLang.Exp)
    (targetBindings : List Bvl.Exp) (targetBody : Bvl.Exp)
    (values : List ClosSem.Value) (result : Result (List ClosSem.Value) ClosSem.Value)
    (bindingRun : ClosSem.evaluate sourceBindings sourceEnv s = (.val values, sMiddle))
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv)
    (bindingPost : evaluatePost s sMiddle t targetEnv f (.val values) targetBindings)
    (bodyIH : ∀ (targetValues : List BvlSem.Value) (tMiddle : BvlSem.State C F)
      (fMiddle : HolFiniteMapExact Nat Nat), stateRel fMiddle sMiddle tMiddle →
      envRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code (values ++ sourceEnv) (targetValues ++ targetEnv) →
      codeAnnotations sMiddle → sptSubspt t.code tMiddle.code →
      evaluatePost sMiddle sFinal tMiddle (targetValues ++ targetEnv) fMiddle result [targetBody]) :
    evaluatePost s sFinal t targetEnv f result [.let targetBindings targetBody] := by
  have maxApp : sMiddle.maxApp = s.maxApp := by
    have h := (ClosProps.evaluate_const (C := C) (F := F)).1 sourceBindings sourceEnv s
    rw [bindingRun] at h
    exact h
  obtain ⟨clock1, targetResult, tMiddle, fMiddle, targetRun1, related1, state1, map1, refs1,
    annotations1, clocks1, code1, env1⟩ :=
      evaluatePost_environment s sMiddle t sourceEnv targetEnv f (.val values) targetBindings envRelated bindingPost
  cases targetResult with
  | err error => simp [resultRel] at related1
  | val targetValues =>
    have envMiddle : envRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code
        (values ++ sourceEnv) (targetValues ++ targetEnv) := by
      simpa [maxApp] using envRel_prepend related1 env1
    obtain ⟨clock2, result2, tFinal, fFinal, targetRun2, related2, state2, map2, refs2,
      annotations2, clocks2⟩ := bodyIH targetValues tMiddle fMiddle state1 envMiddle annotations1 code1
    have shifted := BvlProps.evaluate_addClock targetBindings targetEnv
      { t with clock := s.clock + clock1 } tMiddle (.val targetValues) clock2 targetRun1 (by simp)
    have runBindings : BvlSem.evaluate targetBindings targetEnv
        { t with clock := s.clock + (clock1 + clock2) } =
        (.val targetValues, { tMiddle with clock := sMiddle.clock + clock2 }) := by
      simpa [Nat.add_assoc, clocks1] using shifted
    refine ⟨clock1 + clock2, result2, tFinal, fFinal, ?_, ?_, state2,
      relocationSubmap_trans map1 map2, unmappedRefsSubmap_trans refs1 refs2, annotations2, clocks2⟩
    · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, runBindings]
      exact targetRun2
    · simpa [maxApp] using related2

/-- The let case follows from the binding-list and body induction
hypotheses, including the source compiler's accumulator and code-installation
conditions. This candidate remains untagged until evaluator and carrier
correspondence is reviewed. -/
theorem expressionSimulation_let {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp)
    (bindingsIH : expressionSimulation (C := C) (F := F) bindings)
    (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    expressionSimulation (C := C) (F := F) [.let trace bindings body] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases bindingsCompile : compileExpListHOL s.maxApp bindings aux with
  | mk targetBindings auxMiddle =>
    have bindingsCompiled : compileExpsHOL s.maxApp bindings aux = (targetBindings, auxMiddle) := by
      rw [compileExps_eq_list]
      exact bindingsCompile
    cases bodyCompile : compileExpHOL s.maxApp body auxMiddle with
    | mk targetBody auxLast =>
      have bodyCompiled : compileExpsHOL s.maxApp [body] auxMiddle = ([targetBody], auxLast) := by
        rw [compileExps_eq_list]
        simp [compileExpListHOL, bodyCompile]
      have wholeCompiled : compileExpsHOL s.maxApp [.let trace bindings body] aux =
          ([.let targetBindings targetBody], auxLast) := by
        rw [compileExps_eq_list]
        simp [compileExpListHOL, compileExpHOL, bindingsCompile, bodyCompile]
      have equal := compile.symm.trans wholeCompiled
      cases equal
      have bindingsInstalled : codeInstalled auxMiddle t.code :=
        compileExps_codeInstalled s.maxApp [body] auxMiddle finalAux [targetBody] t.code bodyCompiled installed
      have locationParts : ClosProps.fnLocationSomeExp body ∧ ClosProps.everyFnLocationSome bindings := by
        simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
      have varParts : ClosProps.fnVarsSomeExp body ∧ ClosProps.everyFnVarsSome bindings := by
        simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using varsAnnotated
      have bindingsLocations : ClosProps.everyFnLocationSome bindings := locationParts.2
      have bodyLocations : ClosProps.everyFnLocationSome [body] := by
        simpa [ClosProps.everyFnLocationSome] using locationParts.1
      have bindingsVars : ClosProps.everyFnVarsSome bindings := varParts.2
      have bodyVars : ClosProps.everyFnVarsSome [body] := by
        simpa [ClosProps.everyFnVarsSome] using varParts.1
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
      cases bindingRun : ClosSem.evaluate bindings sourceEnv s with
      | mk bindingResult sMiddle =>
        rw [bindingRun] at run
        cases bindingResult with
        | err error =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          exact evaluatePost_let_error s sMiddle t targetEnv f targetBindings targetBody error
            (bindingsIH s sMiddle t sourceEnv targetEnv f aux auxMiddle targetBindings (.err error)
              bindingRun noTypeError bindingsCompiled bindingsLocations annotations bindingsVars
              bindingsInstalled envRelated states)
        | val values =>
          have bodyRun : ClosSem.evaluate [body] (values ++ sourceEnv) sMiddle = (result, sFinal) := run
          have bindingsPost := bindingsIH s sMiddle t sourceEnv targetEnv f aux auxMiddle targetBindings (.val values)
            bindingRun (by simp) bindingsCompiled bindingsLocations annotations bindingsVars
            bindingsInstalled envRelated states
          apply evaluatePost_let_success s sMiddle sFinal t sourceEnv targetEnv f bindings targetBindings targetBody
            values result bindingRun envRelated bindingsPost
          intro targetValues tMiddle fMiddle middleStates middleEnv middleAnnotations growth
          have maxApp : sMiddle.maxApp = s.maxApp := by
            have h := (ClosProps.evaluate_const (C := C) (F := F)).1 bindings sourceEnv s
            rw [bindingRun] at h
            exact h
          have bodyCompiled' : compileExpsHOL sMiddle.maxApp [body] auxMiddle = ([targetBody], finalAux) := by
            simpa [maxApp] using bodyCompiled
          exact bodyIH sMiddle sFinal tMiddle (values ++ sourceEnv) (targetValues ++ targetEnv) fMiddle
            auxMiddle finalAux [targetBody] result bodyRun noTypeError bodyCompiled' bodyLocations
            middleAnnotations bodyVars (codeInstalled_subspt installed growth) middleEnv middleStates

end Flapjack.Compiler.Backend.ClosToBvl
