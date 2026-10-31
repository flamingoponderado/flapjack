import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateSequence
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.MappedRefsUpdate

/-! Mapped memory update cases of the closure-to-BVL simulation candidate. -/
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

/-- Argument errors propagate through a byte write. -/
theorem evaluatePost_updateByte_error {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (args : List Bvl.Exp) (error : ErrorResult ClosSem.Value)
    (post : evaluatePost s sFinal t targetEnv f (.err error) args) :
    evaluatePost s sFinal t targetEnv f (.err error) [.op (.memOp .updateByte) args] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨clock, .err targetError, tFinal, fFinal, ?_, related, state, map, refs, annotations, clocks⟩
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- A successful byte update preserves the expression simulation. -/
theorem evaluatePost_updateByte_success {C F : Type} (s sMiddle sLast : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (targetArgs : List Bvl.Exp)
    (values : List ClosSem.Value) (value : ClosSem.Value)
    (post : evaluatePost s sMiddle t targetEnv f (.val values) targetArgs)
    (run : ClosSem.doApp (.memOp .updateByte) values.reverse sMiddle = .val (value, sLast))
    (maxApp : sMiddle.maxApp = s.maxApp) :
    evaluatePost s sLast t targetEnv f (.val [value]) [.op (.memOp .updateByte) targetArgs] := by
  obtain ⟨flag, ptr, index, number, bytes, byte, argsEq, found, nonnegative, inBounds,
    valid, valueEq, stateEq⟩ := updateByte_success values.reverse sMiddle sLast value run
  obtain ⟨clock, targetResult, tMiddle, fMiddle, targetRun, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | err error => simp [resultRel] at related
  | val targetValues =>
    have argsRel : List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code)
        [.refPtr flag ptr, .number index, .number number] targetValues.reverse := by
      simpa [resultRel, maxApp, argsEq] using reverse_related related
    cases reversed : targetValues.reverse with
    | nil => rw [reversed] at argsRel; cases argsRel
    | cons targetPtrValue tail =>
      cases tail with
      | nil => rw [reversed] at argsRel; cases argsRel with | cons _ tail => cases tail
      | cons targetIndex tail =>
        cases tail with
        | nil => rw [reversed] at argsRel; cases argsRel with | cons _ tail => cases tail with | cons _ tail => cases tail
        | cons targetNumber rest =>
          rw [reversed] at argsRel
          cases argsRel with
          | cons ptrRel tail =>
            cases tail with
            | cons indexRel tail =>
              cases tail with
              | cons numberRel tail =>
                cases tail
                obtain ⟨targetPtr, rfl, mapped⟩ := vRel_refPtr_inv ptrRel
                have indexEq := vRel_number_inv indexRel
                have numberEq := vRel_number_inv numberRel
                subst targetIndex
                subst targetNumber
                have updated := doApp_updateByte_related sMiddle tMiddle fMiddle state flag ptr targetPtr mapped
                  bytes found index number nonnegative inBounds byte valid
                subst value
                subst sLast
                let targetNext := { tMiddle with refs := tMiddle.refs.updateEq (targetPtr, .byteArray false (bytes.set index.toNat byte)) }
                change _ ∧ BvlSem.doApp (.memOp .updateByte) [.refPtr flag targetPtr, .number index, .number number] tMiddle =
                  .val (BvlSem.unitValue, targetNext) ∧ stateRel fMiddle _ targetNext ∧
                  vRel sMiddle.maxApp fMiddle targetNext.refs targetNext.code ClosSem.unitValue BvlSem.unitValue ∧
                  unmappedRefsSubmap tMiddle.refs targetNext.refs fMiddle fMiddle at updated
                refine ⟨clock, .val [BvlSem.unitValue], targetNext, fMiddle, ?_, ?_, updated.2.2.1,
                  map, unmappedRefsSubmap_trans refs updated.2.2.2.2, annotations, clocks⟩
                · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, targetRun]
                  simp [reversed, updated.2.1]
                · exact .cons (by simpa [maxApp] using updated.2.2.2.1) .nil

/-- The mutable-byte update expression case follows from the argument-list
induction hypothesis. This candidate remains untagged pending review of the
semantic carriers and the assembled pass theorem. -/
theorem expressionSimulation_updateByte {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp)
    (argsIH : expressionSimulation (C := C) (F := F) args) :
    expressionSimulation (C := C) (F := F) [.op trace (.memOp .updateByte) args] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases argsCompile : compileExpListHOL s.maxApp args aux with
  | mk targetArgs aux1 =>
    have argsCompiled : compileExpsHOL s.maxApp args aux = (targetArgs, aux1) := by
      rw [compileExps_eq_list]
      exact argsCompile
    have wholeCompiled : compileExpsHOL s.maxApp [.op trace (.memOp .updateByte) args] aux =
        ([.op (.memOp .updateByte) targetArgs], aux1) := by
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
        exact evaluatePost_updateByte_error s sMiddle t targetEnv f targetArgs error
          (argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.err error)
            argsRun noTypeError argsCompiled argsLoc annotations argsVars installed envRelated states)
      | val values =>
        have maxApp : sMiddle.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        have argsPost := argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.val values)
          argsRun (by simp) argsCompiled argsLoc annotations argsVars installed envRelated states
        cases appRun : ClosSem.doApp (.memOp .updateByte) values.reverse sMiddle with
        | err error =>
          have errorEq := updateByte_error values.reverse sMiddle error appRun
          simp [appRun] at run
          apply False.elim
          apply noTypeError
          simpa [errorEq] using run.1.symm
        | val pair =>
          obtain ⟨value, last⟩ := pair
          simp [appRun] at run
          rcases run with ⟨rfl, rfl⟩
          exact evaluatePost_updateByte_success s sMiddle last t targetEnv f targetArgs values value argsPost appRun maxApp


/-- Argument errors propagate through a array write. -/
theorem evaluatePost_updateArray_error {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (args : List Bvl.Exp) (error : ErrorResult ClosSem.Value)
    (post : evaluatePost s sFinal t targetEnv f (.err error) args) :
    evaluatePost s sFinal t targetEnv f (.err error) [.op (.memOp .update) args] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨clock, .err targetError, tFinal, fFinal, ?_, related, state, map, refs, annotations, clocks⟩
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- A successful array update preserves the expression simulation. -/
theorem evaluatePost_updateArray_success {C F : Type} (s sMiddle sLast : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (targetArgs : List Bvl.Exp)
    (values : List ClosSem.Value) (value : ClosSem.Value)
    (post : evaluatePost s sMiddle t targetEnv f (.val values) targetArgs)
    (run : ClosSem.doApp (.memOp .update) values.reverse sMiddle = .val (value, sLast))
    (maxApp : sMiddle.maxApp = s.maxApp) :
    evaluatePost s sLast t targetEnv f (.val [value]) [.op (.memOp .update) targetArgs] := by
  obtain ⟨flag, ptr, index, fields, stored, argsEq, found, nonnegative, inBounds, valueEq, stateEq⟩ := updateArray_success values.reverse sMiddle sLast value run
  obtain ⟨clock, targetResult, tMiddle, fMiddle, targetRun, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | err error => simp [resultRel] at related
  | val targetValues =>
    have argsRel : List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code)
        [.refPtr flag ptr, .number index, stored] targetValues.reverse := by
      simpa [resultRel, maxApp, argsEq] using reverse_related related
    cases reversed : targetValues.reverse with
    | nil => rw [reversed] at argsRel; cases argsRel
    | cons targetPtrValue tail =>
      cases tail with
      | nil => rw [reversed] at argsRel; cases argsRel with | cons _ tail => cases tail
      | cons targetIndex tail =>
        cases tail with
        | nil => rw [reversed] at argsRel; cases argsRel with | cons _ tail => cases tail with | cons _ tail => cases tail
        | cons targetNumber rest =>
          rw [reversed] at argsRel
          cases argsRel with
          | cons ptrRel tail =>
            cases tail with
            | cons indexRel tail =>
              cases tail with
              | cons numberRel tail =>
                cases tail
                obtain ⟨targetPtr, rfl, mapped⟩ := vRel_refPtr_inv ptrRel
                have indexEq := vRel_number_inv indexRel
                subst targetIndex
                obtain ⟨targetFields, updated⟩ := doApp_updateArray_related sMiddle tMiddle fMiddle state flag ptr targetPtr mapped
                  fields found index nonnegative inBounds stored targetNumber numberRel
                subst value
                subst sLast
                let targetNext := { tMiddle with refs := tMiddle.refs.updateEq (targetPtr, .valueArray (targetFields.set index.toNat targetNumber)) }
                change _ ∧ BvlSem.doApp (.memOp .update) [.refPtr flag targetPtr, .number index, targetNumber] tMiddle =
                  .val (BvlSem.unitValue, targetNext) ∧ stateRel fMiddle _ targetNext ∧
                  vRel sMiddle.maxApp fMiddle targetNext.refs targetNext.code ClosSem.unitValue BvlSem.unitValue ∧
                  unmappedRefsSubmap tMiddle.refs targetNext.refs fMiddle fMiddle at updated
                refine ⟨clock, .val [BvlSem.unitValue], targetNext, fMiddle, ?_, ?_, updated.2.2.1,
                  map, unmappedRefsSubmap_trans refs updated.2.2.2.2, annotations, clocks⟩
                · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, targetRun]
                  simp [reversed, updated.2.1]
                · exact .cons (by simpa [maxApp] using updated.2.2.2.1) .nil

/-- The mutable-array update expression case follows from the argument-list
induction hypothesis. This candidate remains untagged pending review of the
semantic carriers and the assembled pass theorem. -/
theorem expressionSimulation_updateArray {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp)
    (argsIH : expressionSimulation (C := C) (F := F) args) :
    expressionSimulation (C := C) (F := F) [.op trace (.memOp .update) args] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases argsCompile : compileExpListHOL s.maxApp args aux with
  | mk targetArgs aux1 =>
    have argsCompiled : compileExpsHOL s.maxApp args aux = (targetArgs, aux1) := by
      rw [compileExps_eq_list]
      exact argsCompile
    have wholeCompiled : compileExpsHOL s.maxApp [.op trace (.memOp .update) args] aux =
        ([.op (.memOp .update) targetArgs], aux1) := by
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
        exact evaluatePost_updateArray_error s sMiddle t targetEnv f targetArgs error
          (argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.err error)
            argsRun noTypeError argsCompiled argsLoc annotations argsVars installed envRelated states)
      | val values =>
        have maxApp : sMiddle.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        have argsPost := argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.val values)
          argsRun (by simp) argsCompiled argsLoc annotations argsVars installed envRelated states
        cases appRun : ClosSem.doApp (.memOp .update) values.reverse sMiddle with
        | err error =>
          have errorEq := updateArray_error values.reverse sMiddle error appRun
          simp [appRun] at run
          apply False.elim
          apply noTypeError
          simpa [errorEq] using run.1.symm
        | val pair =>
          obtain ⟨value, last⟩ := pair
          simp [appRun] at run
          rcases run with ⟨rfl, rfl⟩
          exact evaluatePost_updateArray_success s sMiddle last t targetEnv f targetArgs values value argsPost appRun maxApp


end Flapjack.Compiler.Backend.ClosToBvl
