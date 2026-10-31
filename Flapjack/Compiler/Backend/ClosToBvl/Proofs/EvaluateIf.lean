import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateLet

/-! Conditional case of the closure-to-BVL expression simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- Related values decode to the same Boolean whenever the source decodes. -/
theorem vRel_asBool {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {source : ClosSem.Value} {target : BvlSem.Value} {choice : Bool}
    (related : vRel maxApp f refs code source target)
    (decoded : ClosSem.asBool source = some choice) : BvlSem.asBool target = some choice := by
  cases source <;> simp [ClosSem.asBool] at decoded
  case block tag values =>
    cases values with
    | cons value values => simp at decoded
    | nil =>
      cases tag with
      | zero =>
        simp at decoded
        subst choice
        cases related with
        | block elements =>
          cases elements
          rfl
        | closure _ closure => cases closure
        | partialClosure _ _ _ _ _ added _ closure => cases closure <;> simp [addArgs] at added
      | succ tag =>
        cases tag with
        | zero =>
          simp at decoded
          subst choice
          cases related with
          | block elements =>
            cases elements
            rfl
          | closure _ closure => cases closure
          | partialClosure _ _ _ _ _ added _ closure => cases closure <;> simp [addArgs] at added
        | succ tag => simp at decoded

/-- An error from the condition propagates through the target conditional. -/
theorem evaluatePost_if_error {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (condition yes no : Bvl.Exp)
    (error : ErrorResult ClosSem.Value)
    (post : evaluatePost s sFinal t targetEnv f (.err error) [condition]) :
    evaluatePost s sFinal t targetEnv f (.err error) [.ifThenElse condition yes no] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨clock, .err targetError, tFinal, fFinal, ?_, related, state, map, refs, annotations, clocks⟩
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- Compose a successful Boolean condition with its selected branch. -/
theorem evaluatePost_if_success {C F : Type}
    (s sMiddle sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (sourceCondition : ClosLang.Exp)
    (targetCondition targetYes targetNo : Bvl.Exp)
    (value : ClosSem.Value) (choice : Bool) (result : Result (List ClosSem.Value) ClosSem.Value)
    (conditionRun : ClosSem.evaluate [sourceCondition] sourceEnv s = (.val [value], sMiddle))
    (decoded : ClosSem.asBool value = some choice)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv)
    (conditionPost : evaluatePost s sMiddle t targetEnv f (.val [value]) [targetCondition])
    (branchIH : ∀ (tMiddle : BvlSem.State C F) (fMiddle : HolFiniteMapExact Nat Nat),
      stateRel fMiddle sMiddle tMiddle → envRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code sourceEnv targetEnv →
      codeAnnotations sMiddle → sptSubspt t.code tMiddle.code →
      evaluatePost sMiddle sFinal tMiddle targetEnv fMiddle result [if choice then targetYes else targetNo]) :
    evaluatePost s sFinal t targetEnv f result [.ifThenElse targetCondition targetYes targetNo] := by
  have maxApp : sMiddle.maxApp = s.maxApp := by
    have h := (ClosProps.evaluate_const (C := C) (F := F)).1 [sourceCondition] sourceEnv s
    rw [conditionRun] at h
    exact h
  obtain ⟨clock1, targetResult, tMiddle, fMiddle, targetRun1, related1, state1, map1, refs1,
    annotations1, clocks1, code1, env1⟩ :=
      evaluatePost_environment s sMiddle t sourceEnv targetEnv f (.val [value]) [targetCondition] envRelated conditionPost
  cases targetResult with
  | err error => simp [resultRel] at related1
  | val targetValues =>
    cases related1 with
    | @cons a targetValue sourceTail targetTail valueRel restRel =>
      cases restRel
      have targetDecoded := vRel_asBool valueRel decoded
      have envMiddle : envRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code sourceEnv targetEnv := by
        simpa [maxApp] using env1
      obtain ⟨clock2, result2, tFinal, fFinal, targetRun2, related2, state2, map2, refs2,
        annotations2, clocks2⟩ := branchIH tMiddle fMiddle state1 envMiddle annotations1 code1
      have shifted := BvlProps.evaluate_addClock [targetCondition] targetEnv
        { t with clock := s.clock + clock1 } tMiddle (.val [targetValue]) clock2 targetRun1 (by simp)
      have runCondition : BvlSem.evaluate [targetCondition] targetEnv
          { t with clock := s.clock + (clock1 + clock2) } =
          (.val [targetValue], { tMiddle with clock := sMiddle.clock + clock2 }) := by
        simpa [Nat.add_assoc, clocks1] using shifted
      refine ⟨clock1 + clock2, result2, tFinal, fFinal, ?_, ?_, state2,
        relocationSubmap_trans map1 map2, unmappedRefsSubmap_trans refs1 refs2, annotations2, clocks2⟩
      · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, runCondition]
        cases choice <;> simp_all
      · simpa [maxApp] using related2

/-- The conditional case follows from the condition and branch induction
hypotheses, including generated-code installation. This candidate is untagged
pending review of the evaluators and state carriers. -/
theorem expressionSimulation_if {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp)
    (conditionIH : expressionSimulation (C := C) (F := F) [condition])
    (yesIH : expressionSimulation (C := C) (F := F) [yes])
    (noIH : expressionSimulation (C := C) (F := F) [no]) :
    expressionSimulation (C := C) (F := F) [.ifThenElse trace condition yes no] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases conditionCompile : compileExpHOL s.maxApp condition aux with
  | mk targetCondition aux1 =>
    cases yesCompile : compileExpHOL s.maxApp yes aux1 with
    | mk targetYes aux2 =>
      cases noCompile : compileExpHOL s.maxApp no aux2 with
      | mk targetNo aux3 =>
        have conditionCompiled : compileExpsHOL s.maxApp [condition] aux = ([targetCondition], aux1) := by
          rw [compileExps_eq_list]
          simp [compileExpListHOL, conditionCompile]
        have yesCompiled : compileExpsHOL s.maxApp [yes] aux1 = ([targetYes], aux2) := by
          rw [compileExps_eq_list]
          simp [compileExpListHOL, yesCompile]
        have noCompiled : compileExpsHOL s.maxApp [no] aux2 = ([targetNo], aux3) := by
          rw [compileExps_eq_list]
          simp [compileExpListHOL, noCompile]
        have wholeCompiled : compileExpsHOL s.maxApp [.ifThenElse trace condition yes no] aux =
            ([.ifThenElse targetCondition targetYes targetNo], aux3) := by
          rw [compileExps_eq_list]
          simp [compileExpListHOL, compileExpHOL, conditionCompile, yesCompile, noCompile]
        have equal := compile.symm.trans wholeCompiled
        cases equal
        have yesInstalled : codeInstalled aux2 t.code :=
          compileExps_codeInstalled s.maxApp [no] aux2 finalAux [targetNo] t.code noCompiled installed
        have conditionInstalled : codeInstalled aux1 t.code :=
          compileExps_codeInstalled s.maxApp [yes] aux1 aux2 [targetYes] t.code yesCompiled yesInstalled
        have locs : ClosProps.fnLocationSomeExp condition ∧ ClosProps.fnLocationSomeExp yes ∧
            ClosProps.fnLocationSomeExp no := by
          simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
        have vars : ClosProps.fnVarsSomeExp condition ∧ ClosProps.fnVarsSomeExp yes ∧
            ClosProps.fnVarsSomeExp no := by
          simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using varsAnnotated
        have conditionLoc : ClosProps.everyFnLocationSome [condition] := by simpa [ClosProps.everyFnLocationSome] using locs.1
        have yesLoc : ClosProps.everyFnLocationSome [yes] := by simpa [ClosProps.everyFnLocationSome] using locs.2.1
        have noLoc : ClosProps.everyFnLocationSome [no] := by simpa [ClosProps.everyFnLocationSome] using locs.2.2
        have conditionVars : ClosProps.everyFnVarsSome [condition] := by simpa [ClosProps.everyFnVarsSome] using vars.1
        have yesVars : ClosProps.everyFnVarsSome [yes] := by simpa [ClosProps.everyFnVarsSome] using vars.2.1
        have noVars : ClosProps.everyFnVarsSome [no] := by simpa [ClosProps.everyFnVarsSome] using vars.2.2
        rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
        cases conditionRun : ClosSem.evaluate [condition] sourceEnv s with
        | mk conditionResult sMiddle =>
          rw [conditionRun] at run
          cases conditionResult with
          | err error =>
            simp at run
            rcases run with ⟨rfl, rfl⟩
            exact evaluatePost_if_error s sMiddle t targetEnv f targetCondition targetYes targetNo error
              (conditionIH s sMiddle t sourceEnv targetEnv f aux aux1 [targetCondition] (.err error)
                conditionRun noTypeError conditionCompiled conditionLoc annotations conditionVars
                conditionInstalled envRelated states)
          | val values =>
            obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value condition sourceEnv s sMiddle values conditionRun
            dsimp only at run
            cases decoded : ClosSem.asBool value with
            | none =>
              simp [decoded] at run
              exact False.elim (noTypeError run.1.symm)
            | some choice =>
              have conditionPost := conditionIH s sMiddle t sourceEnv targetEnv f aux aux1 [targetCondition] (.val [value])
                conditionRun (by simp) conditionCompiled conditionLoc annotations conditionVars conditionInstalled envRelated states
              apply evaluatePost_if_success s sMiddle sFinal t sourceEnv targetEnv f condition targetCondition targetYes targetNo
                value choice result conditionRun decoded envRelated conditionPost
              intro tMiddle fMiddle middleStates middleEnv middleAnnotations growth
              have maxApp : sMiddle.maxApp = s.maxApp := by
                have h := (ClosProps.evaluate_const (C := C) (F := F)).1 [condition] sourceEnv s
                rw [conditionRun] at h
                exact h
              cases choice with
              | false =>
                have branchRun : ClosSem.evaluate [no] sourceEnv sMiddle = (result, sFinal) := by simpa [decoded] using run
                have branchCompiled : compileExpsHOL sMiddle.maxApp [no] aux2 = ([targetNo], finalAux) := by simpa [maxApp] using noCompiled
                exact noIH sMiddle sFinal tMiddle sourceEnv targetEnv fMiddle aux2 finalAux [targetNo] result
                  branchRun noTypeError branchCompiled noLoc middleAnnotations noVars (codeInstalled_subspt installed growth)
                  middleEnv middleStates
              | true =>
                have branchRun : ClosSem.evaluate [yes] sourceEnv sMiddle = (result, sFinal) := by simpa [decoded] using run
                have branchCompiled : compileExpsHOL sMiddle.maxApp [yes] aux1 = ([targetYes], aux2) := by simpa [maxApp] using yesCompiled
                exact yesIH sMiddle sFinal tMiddle sourceEnv targetEnv fMiddle aux1 aux2 [targetYes] result
                  branchRun noTypeError branchCompiled yesLoc middleAnnotations yesVars (codeInstalled_subspt yesInstalled growth)
                  middleEnv middleStates

end Flapjack.Compiler.Backend.ClosToBvl
