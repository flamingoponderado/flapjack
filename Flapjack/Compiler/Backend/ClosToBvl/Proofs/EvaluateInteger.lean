import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateSequence
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.IntegerRelation

/-! Integer operation case of the closure-to-BVL simulation candidate. -/
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

/-- An error while evaluating the arguments propagates through the target
integer operation. -/
theorem evaluatePost_int_error {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (op : ClosLang.IntOp) (args : List Bvl.Exp)
    (error : ErrorResult ClosSem.Value)
    (post : evaluatePost s sFinal t targetEnv f (.err error) args) :
    evaluatePost s sFinal t targetEnv f (.err error) [.op (.intOp op) args] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨clock, .err targetError, tFinal, fFinal, ?_, related, state, map, refs, annotations, clocks⟩
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- Successful argument evaluation and integer dispatch compose into the
same postcondition as the expression simulation. -/
theorem evaluatePost_int_success {C F : Type} (s sMiddle : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (op : ClosLang.IntOp) (targetArgs : List Bvl.Exp)
    (values : List ClosSem.Value) (value : ClosSem.Value)
    (post : evaluatePost s sMiddle t targetEnv f (.val values) targetArgs)
    (run : ClosSem.doIntApp op values.reverse = some value)
    (maxApp : sMiddle.maxApp = s.maxApp) :
    evaluatePost s sMiddle t targetEnv f (.val [value]) [.op (.intOp op) targetArgs] := by
  obtain ⟨clock, targetResult, tMiddle, fMiddle, targetRun, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | err error => simp [resultRel] at related
  | val targetValues =>
    have argsRel : List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code)
        values.reverse targetValues.reverse := by
      simpa [resultRel, maxApp] using reverse_related related
    obtain ⟨target, targetInt, valueRel⟩ := doIntApp_related op values.reverse targetValues.reverse argsRel value run
    refine ⟨clock, .val [target], tMiddle, fMiddle, ?_, ?_, state, map, refs, annotations, clocks⟩
    · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, targetRun]
      simp [BvlSem.doApp, BvlSem.applyNumeric, targetInt]
    · exact List.Forall₂.cons (by simpa [maxApp] using valueRel) .nil

/-- The integer-operation expression case follows from the argument-list
induction hypothesis. This candidate remains untagged pending review of the
semantic carriers and the assembled pass theorem. -/
theorem expressionSimulation_int {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.IntOp) (args : List ClosLang.Exp)
    (argsIH : expressionSimulation (C := C) (F := F) args) :
    expressionSimulation (C := C) (F := F) [.op trace (.intOp op) args] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases argsCompile : compileExpListHOL s.maxApp args aux with
  | mk targetArgs aux1 =>
    have argsCompiled : compileExpsHOL s.maxApp args aux = (targetArgs, aux1) := by
      rw [compileExps_eq_list]
      exact argsCompile
    have wholeCompiled : compileExpsHOL s.maxApp [.op trace (.intOp op) args] aux =
        ([.op (.intOp op) targetArgs], aux1) := by
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
        exact evaluatePost_int_error s sMiddle t targetEnv f op targetArgs error
          (argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.err error)
            argsRun noTypeError argsCompiled argsLoc annotations argsVars installed envRelated states)
      | val values =>
        have maxApp : sMiddle.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        have argsPost := argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.val values)
          argsRun (by simp) argsCompiled argsLoc annotations argsVars installed envRelated states
        cases intRun : ClosSem.doIntApp op values.reverse with
        | none =>
          simp [ClosSem.doApp, ClosSem.applyNumeric, intRun] at run
          exact False.elim (noTypeError run.1.symm)
        | some value =>
          simp [ClosSem.doApp, ClosSem.applyNumeric, intRun] at run
          rcases run with ⟨rfl, rfl⟩
          exact evaluatePost_int_success s sMiddle t targetEnv f op targetArgs values value argsPost intRun maxApp

end Flapjack.Compiler.Backend.ClosToBvl
