import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateSequence
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Ffi

/-! Foreign-call expression case of the closure-to-BVL simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps
open Flapjack.Basis.Pure.MlString

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

/-- Argument errors propagate through the target foreign call. -/
theorem evaluatePost_ffi_error {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (name : MlString) (args : List Bvl.Exp)
    (error : ErrorResult ClosSem.Value) (post : evaluatePost s sFinal t targetEnv f (.err error) args) :
    evaluatePost s sFinal t targetEnv f (.err error) [.op (.ffi name) args] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨clock, .err targetError, tFinal, fFinal, ?_, related, state, map, refs, annotations, clocks⟩
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- Foreign calls preserve the evaluator postcondition for either a returning
oracle or a terminal FFI event. -/
theorem evaluatePost_ffi_call {C F : Type} (s sMiddle sLast : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (name : MlString) (targetArgs : List Bvl.Exp)
    (values : List ClosSem.Value) (result : Result (List ClosSem.Value) ClosSem.Value)
    (post : evaluatePost s sMiddle t targetEnv f (.val values) targetArgs)
    (run : (match ClosSem.doApp (.ffi name) values.reverse sMiddle with
      | .err error => (.err error, sMiddle)
      | .val (value, next) => (.val [value], next)) = (result, sLast))
    (noType : result ≠ .err (.abort .typeError)) (maxApp : sMiddle.maxApp = s.maxApp) :
    evaluatePost s sLast t targetEnv f result [.op (.ffi name) targetArgs] := by
  have notTypeApp : ClosSem.doApp (.ffi name) values.reverse sMiddle ≠ .err (.abort .typeError) := by
    intro bad
    simp [bad] at run
    exact noType run.1.symm
  obtain ⟨config, bytes, flag, ptr, argsEq, sourceFound⟩ := ffi_ready name values.reverse sMiddle notTypeApp
  obtain ⟨clock, targetResult, tMiddle, fMiddle, targetRun, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | err error => simp [resultRel] at related
  | val targetValues =>
    have argsRel : List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code)
        [.byteVector config, .refPtr flag ptr] targetValues.reverse := by
      simpa [resultRel, maxApp, argsEq] using reverse_related related
    generalize reversed : targetValues.reverse = targetList at argsRel
    cases argsRel with
    | cons configRel tail =>
      cases tail with
      | cons ptrRel tail =>
        cases tail
        obtain ⟨configPtr, rfl, configFound⟩ := vRel_byteVector_inv configRel
        obtain ⟨targetPtr, rfl, mapped⟩ := vRel_refPtr_inv ptrRel
        have valid := ffi_valid_related sMiddle tMiddle fMiddle state name config bytes configPtr flag ptr targetPtr
          configFound mapped sourceFound
        cases ffiCall : callFFIHOL sMiddle.ffi (.extCall name) config bytes with
        | ret ffi updated =>
          rw [ffiCall] at valid
          obtain ⟨sourceApp, targetApp, nextState, valueRel, frame⟩ := valid
          rw [argsEq, sourceApp] at run
          simp at run
          rcases run with ⟨rfl, rfl⟩
          let targetNext := { tMiddle with refs := tMiddle.refs.updateEq (targetPtr, .byteArray false updated), ffi := ffi }
          refine ⟨clock, .val [BvlSem.unitValue], targetNext, fMiddle, ?_, ?_, nextState, map,
            unmappedRefsSubmap_trans refs frame, annotations, clocks⟩
          · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, targetRun]
            simp [reversed, targetApp, targetNext]
          · exact .cons (by simpa [maxApp] using valueRel) .nil
        | final event =>
          rw [ffiCall] at valid
          obtain ⟨sourceApp, targetApp⟩ := valid
          rw [argsEq, sourceApp] at run
          simp at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨clock, .err (.abort (.ffiError event)), tMiddle, fMiddle, ?_, ?_, state, map, refs, annotations, clocks⟩
          · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, targetRun]
            simp [reversed, targetApp]
          · simp [resultRel, excRel]

/-- The foreign-call expression case follows from the argument-list
induction hypothesis. This candidate is untagged pending semantic-carrier
review and assembly of the pass theorem. -/
theorem expressionSimulation_ffi {C F : Type} (trace : BackendCommon.Tra)
    (name : MlString) (args : List ClosLang.Exp)
    (argsIH : expressionSimulation (C := C) (F := F) args) :
    expressionSimulation (C := C) (F := F) [.op trace (.ffi name) args] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases argsCompile : compileExpListHOL s.maxApp args aux with
  | mk targetArgs aux1 =>
    have argsCompiled : compileExpsHOL s.maxApp args aux = (targetArgs, aux1) := by
      rw [compileExps_eq_list]
      exact argsCompile
    have wholeCompiled : compileExpsHOL s.maxApp [.op trace (.ffi name) args] aux =
        ([.op (.ffi name) targetArgs], aux1) := by
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
        exact evaluatePost_ffi_error s sMiddle t targetEnv f name targetArgs error
          (argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.err error)
            argsRun noTypeError argsCompiled argsLoc annotations argsVars installed envRelated states)
      | val values =>
        have maxApp : sMiddle.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        have argsPost := argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.val values)
          argsRun (by simp) argsCompiled argsLoc annotations argsVars installed envRelated states
        exact evaluatePost_ffi_call s sMiddle sFinal t targetEnv f name targetArgs values result argsPost run noTypeError maxApp

end Flapjack.Compiler.Backend.ClosToBvl
