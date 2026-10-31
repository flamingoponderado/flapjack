import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateSequence
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Thunk

/-! Thunk allocation in the closure-to-BVL simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

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

/-- Argument errors propagate through thunk allocation. -/
theorem evaluatePost_allocThunk_error {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (mode : AstHOL.ThunkMode) (args : List Bvl.Exp)
    (error : ErrorResult ClosSem.Value) (post : evaluatePost s sFinal t targetEnv f (.err error) args) :
    evaluatePost s sFinal t targetEnv f (.err error) [.op (.thunkOp (.allocThunk mode)) args] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨clock, .err targetError, tFinal, fFinal, ?_, related, state, map, refs, annotations, clocks⟩
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- Successful thunk allocation preserves the expression simulation. -/
theorem evaluatePost_allocThunk_success {C F : Type} (s sMiddle sLast : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (mode : AstHOL.ThunkMode) (targetArgs : List Bvl.Exp)
    (values : List ClosSem.Value) (value : ClosSem.Value)
    (post : evaluatePost s sMiddle t targetEnv f (.val values) targetArgs)
    (run : ClosSem.doApp (.thunkOp (.allocThunk mode)) values.reverse sMiddle = .val (value, sLast))
    (maxApp : sMiddle.maxApp = s.maxApp) :
    evaluatePost s sLast t targetEnv f (.val [value]) [.op (.thunkOp (.allocThunk mode)) targetArgs] := by
  obtain ⟨initial, argsEq, good, valueEq, stateEq⟩ := allocThunk_success mode values.reverse sMiddle sLast value run
  obtain ⟨clock, targetResult, tMiddle, fMiddle, targetRun, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | err error => simp [resultRel] at related
  | val targetValues =>
    have argsRel : List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code)
        [initial] targetValues.reverse := by
      simpa [resultRel, maxApp, argsEq] using reverse_related related
    generalize reversed : targetValues.reverse = targetList at argsRel
    cases argsRel with
    | cons initialRel tail =>
      cases tail
      have allocated := alloc_thunk_related sMiddle tMiddle fMiddle mode initial _ state initialRel good
      subst value
      subst sLast
      let sourcePtr := ClosSem.leastUnusedRef sMiddle.refs
      let targetPtr := BvlSem.leastUnusedRef tMiddle.refs
      let newMap := fMiddle.updateEq (sourcePtr, targetPtr)
      change _ ∧ BvlSem.doApp (.thunkOp (.allocThunk mode)) [_] tMiddle =
        .val (.refPtr false targetPtr, _) ∧ stateRel newMap _ _ ∧
        vRel sMiddle.maxApp newMap _ _ (.refPtr false sourcePtr) (.refPtr false targetPtr) ∧
        relocationSubmap fMiddle newMap ∧ unmappedRefsSubmap tMiddle.refs _ fMiddle newMap at allocated
      refine ⟨clock, .val [.refPtr false targetPtr], _, newMap, ?_, ?_, allocated.2.2.1,
        relocationSubmap_trans map allocated.2.2.2.2.1,
        unmappedRefsSubmap_trans refs allocated.2.2.2.2.2, annotations, clocks⟩
      · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, targetRun]
        simp [reversed, allocated.2.1]
      · exact .cons (by simpa [maxApp] using allocated.2.2.2.1) .nil

/-- The thunk allocation expression case follows from the argument-list
induction hypothesis. This candidate remains untagged pending review of the
semantic carriers and the assembled pass theorem. -/
theorem expressionSimulation_allocThunk {C F : Type} (trace : BackendCommon.Tra)
    (mode : AstHOL.ThunkMode) (args : List ClosLang.Exp)
    (argsIH : expressionSimulation (C := C) (F := F) args) :
    expressionSimulation (C := C) (F := F) [.op trace (.thunkOp (.allocThunk mode)) args] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases argsCompile : compileExpListHOL s.maxApp args aux with
  | mk targetArgs aux1 =>
    have argsCompiled : compileExpsHOL s.maxApp args aux = (targetArgs, aux1) := by
      rw [compileExps_eq_list]
      exact argsCompile
    have wholeCompiled : compileExpsHOL s.maxApp [.op trace (.thunkOp (.allocThunk mode)) args] aux =
        ([.op (.thunkOp (.allocThunk mode)) targetArgs], aux1) := by
      rw [compileExps_eq_list]
      simp [compileExpListHOL, compileExpHOL, argsCompile, compileOp]
    have equal := compile.symm.trans wholeCompiled
    cases equal
    have argsLoc : ClosProps.everyFnLocationSome args := by
      simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
    have argsVars : ClosProps.everyFnVarsSome args := by
      simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using varsAnnotated
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
    cases argsRun : ClosSem.evaluate args sourceEnv s with
    | mk argsResult sMiddle =>
      rw [argsRun] at run
      cases argsResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact evaluatePost_allocThunk_error s sMiddle t targetEnv f mode targetArgs error
          (argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.err error)
            argsRun noTypeError argsCompiled argsLoc annotations argsVars installed envRelated states)
      | val values =>
        have maxApp : sMiddle.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        have argsPost := argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.val values)
          argsRun (by simp) argsCompiled argsLoc annotations argsVars installed envRelated states
        cases appRun : ClosSem.doApp (.thunkOp (.allocThunk mode)) values.reverse sMiddle with
        | err error =>
          have errorEq := allocThunk_error mode values.reverse sMiddle error appRun
          simp [appRun] at run
          apply False.elim
          apply noTypeError
          simpa [errorEq] using run.1.symm
        | val pair =>
          obtain ⟨value, last⟩ := pair
          simp [appRun] at run
          rcases run with ⟨rfl, rfl⟩
          exact evaluatePost_allocThunk_success s sMiddle last t targetEnv f mode targetArgs values value argsPost appRun maxApp


/-- Argument errors propagate through thunk updates. -/
theorem evaluatePost_updateThunk_error {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (mode : AstHOL.ThunkMode) (args : List Bvl.Exp)
    (error : ErrorResult ClosSem.Value) (post : evaluatePost s sFinal t targetEnv f (.err error) args) :
    evaluatePost s sFinal t targetEnv f (.err error) [.op (.thunkOp (.updateThunk mode)) args] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨clock, .err targetError, tFinal, fFinal, ?_, related, state, map, refs, annotations, clocks⟩
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- Successful thunk updates preserve the expression simulation. -/
theorem evaluatePost_updateThunk_success {C F : Type} (s sMiddle sLast : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (mode : AstHOL.ThunkMode) (targetArgs : List Bvl.Exp)
    (values : List ClosSem.Value) (value : ClosSem.Value)
    (post : evaluatePost s sMiddle t targetEnv f (.val values) targetArgs)
    (run : ClosSem.doApp (.thunkOp (.updateThunk mode)) values.reverse sMiddle = .val (value, sLast))
    (maxApp : sMiddle.maxApp = s.maxApp) :
    evaluatePost s sLast t targetEnv f (.val [value]) [.op (.thunkOp (.updateThunk mode)) targetArgs] := by
  obtain ⟨ptr, initial, old, argsEq, good, found, valueEq, stateEq⟩ := updateThunk_success mode values.reverse sMiddle sLast value run
  obtain ⟨clock, targetResult, tMiddle, fMiddle, targetRun, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | err error => simp [resultRel] at related
  | val targetValues =>
    have argsRel : List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code)
        [.refPtr false ptr, initial] targetValues.reverse := by
      simpa [resultRel, maxApp, argsEq] using reverse_related related
    generalize reversed : targetValues.reverse = targetList at argsRel
    cases argsRel with
    | cons ptrRel tail =>
      cases tail with
      | cons valueRel tail =>
        cases tail
        obtain ⟨targetPtr, rfl, mapped⟩ := vRel_refPtr_inv ptrRel
        have updated := updateThunk_related sMiddle tMiddle fMiddle mode ptr targetPtr mapped old found initial _ state valueRel good
        subst value
        subst sLast
        change _ ∧ BvlSem.doApp (.thunkOp (.updateThunk mode)) [.refPtr false targetPtr, _] tMiddle =
          .val (BvlSem.unitValue, _) ∧ stateRel fMiddle _ _ ∧
          vRel sMiddle.maxApp fMiddle _ _ ClosSem.unitValue BvlSem.unitValue ∧
          unmappedRefsSubmap tMiddle.refs _ fMiddle fMiddle at updated
        refine ⟨clock, .val [BvlSem.unitValue], _, fMiddle, ?_, ?_, updated.2.2.1,
          map, unmappedRefsSubmap_trans refs updated.2.2.2.2, annotations, clocks⟩
        · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, targetRun]
          simp [reversed, updated.2.1]
        · exact .cons (by simpa [maxApp] using updated.2.2.2.1) .nil

/-- The thunk update expression case follows from the argument-list
induction hypothesis. This candidate remains untagged pending review of the
semantic carriers and the assembled pass theorem. -/
theorem expressionSimulation_updateThunk {C F : Type} (trace : BackendCommon.Tra)
    (mode : AstHOL.ThunkMode) (args : List ClosLang.Exp)
    (argsIH : expressionSimulation (C := C) (F := F) args) :
    expressionSimulation (C := C) (F := F) [.op trace (.thunkOp (.updateThunk mode)) args] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases argsCompile : compileExpListHOL s.maxApp args aux with
  | mk targetArgs aux1 =>
    have argsCompiled : compileExpsHOL s.maxApp args aux = (targetArgs, aux1) := by
      rw [compileExps_eq_list]
      exact argsCompile
    have wholeCompiled : compileExpsHOL s.maxApp [.op trace (.thunkOp (.updateThunk mode)) args] aux =
        ([.op (.thunkOp (.updateThunk mode)) targetArgs], aux1) := by
      rw [compileExps_eq_list]
      simp [compileExpListHOL, compileExpHOL, argsCompile, compileOp]
    have equal := compile.symm.trans wholeCompiled
    cases equal
    have argsLoc : ClosProps.everyFnLocationSome args := by
      simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
    have argsVars : ClosProps.everyFnVarsSome args := by
      simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using varsAnnotated
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
    cases argsRun : ClosSem.evaluate args sourceEnv s with
    | mk argsResult sMiddle =>
      rw [argsRun] at run
      cases argsResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact evaluatePost_updateThunk_error s sMiddle t targetEnv f mode targetArgs error
          (argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.err error)
            argsRun noTypeError argsCompiled argsLoc annotations argsVars installed envRelated states)
      | val values =>
        have maxApp : sMiddle.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        have argsPost := argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.val values)
          argsRun (by simp) argsCompiled argsLoc annotations argsVars installed envRelated states
        cases appRun : ClosSem.doApp (.thunkOp (.updateThunk mode)) values.reverse sMiddle with
        | err error =>
          have errorEq := updateThunk_error mode values.reverse sMiddle error appRun
          simp [appRun] at run
          apply False.elim
          apply noTypeError
          simpa [errorEq] using run.1.symm
        | val pair =>
          obtain ⟨value, last⟩ := pair
          simp [appRun] at run
          rcases run with ⟨rfl, rfl⟩
          exact evaluatePost_updateThunk_success s sMiddle last t targetEnv f mode targetArgs values value argsPost appRun maxApp


end Flapjack.Compiler.Backend.ClosToBvl
