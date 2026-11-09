import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateSequence
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.WordRelation

/-! Word operation case of the closure-to-BVL simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- An error while evaluating the arguments propagates through the target
word operation. -/
theorem evaluatePost_word_error {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (op : ClosLang.WordOp) (args : List Bvl.Exp)
    (error : ErrorResult ClosSem.Value)
    (post : evaluatePost s sFinal t targetEnv f (.err error) args) :
    evaluatePost s sFinal t targetEnv f (.err error) [.op (.wordOp op) args] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨clock, .err targetError, tFinal, fFinal, ?_, related, state, map, refs, annotations, clocks⟩
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- Successful argument evaluation and word dispatch compose into the
same postcondition as the expression simulation. -/
theorem evaluatePost_word_success {C F : Type} (s sMiddle : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (op : ClosLang.WordOp) (targetArgs : List Bvl.Exp)
    (values : List ClosSem.Value) (value : ClosSem.Value)
    (post : evaluatePost s sMiddle t targetEnv f (.val values) targetArgs)
    (run : ClosSem.doWordApp op values.reverse = some value)
    (maxApp : sMiddle.maxApp = s.maxApp) :
    evaluatePost s sMiddle t targetEnv f (.val [value]) [.op (.wordOp op) targetArgs] := by
  obtain ⟨clock, targetResult, tMiddle, fMiddle, targetRun, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | err error => simp [resultRel] at related
  | val targetValues =>
    have argsRel : List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code)
        values.reverse targetValues.reverse := by
      simpa [resultRel, maxApp] using reverse_related related
    obtain ⟨target, targetWord, valueRel⟩ := doWordApp_related op values.reverse targetValues.reverse argsRel value run
    refine ⟨clock, .val [target], tMiddle, fMiddle, ?_, ?_, state, map, refs, annotations, clocks⟩
    · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, targetRun]
      simp [BvlSem.doApp, BvlSem.applyNumeric, targetWord]
    · exact List.Forall₂.cons (by simpa [maxApp] using valueRel) .nil

/-- Bounded simulation for the operator and its argument expressions. -/
theorem expressionSimulationBelow_word {C F : Type} (clockBound : Nat) (trace : BackendCommon.Tra)
    (op : ClosLang.WordOp) (args : List ClosLang.Exp)
    (argsIH : expressionSimulationBelow (C := C) (F := F) clockBound args) :
    expressionSimulationBelow (C := C) (F := F) clockBound [.op trace (.wordOp op) args] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result clockBounded run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases argsCompile : compileExpListHOL s.maxApp args aux with
  | mk targetArgs aux1 =>
    have argsCompiled : compileExpsHOL s.maxApp args aux = (targetArgs, aux1) := by
      rw [compileExps_eq_list]
      exact argsCompile
    have wholeCompiled : compileExpsHOL s.maxApp [.op trace (.wordOp op) args] aux =
        ([.op (.wordOp op) targetArgs], aux1) := by
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
        exact evaluatePost_word_error s sMiddle t targetEnv f op targetArgs error
          (argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.err error)
            clockBounded argsRun noTypeError argsCompiled argsLoc annotations argsVars installed envRelated states)
      | val values =>
        have maxApp : sMiddle.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        have argsPost := argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.val values)
          clockBounded argsRun (by simp) argsCompiled argsLoc annotations argsVars installed envRelated states
        cases wordRun : ClosSem.doWordApp op values.reverse with
        | none =>
          simp [ClosSem.doApp, ClosSem.applyNumeric, wordRun] at run
          exact False.elim (noTypeError run.1.symm)
        | some value =>
          simp [ClosSem.doApp, ClosSem.applyNumeric, wordRun] at run
          rcases run with ⟨rfl, rfl⟩
          exact evaluatePost_word_success s sMiddle t targetEnv f op targetArgs values value argsPost wordRun maxApp


end Flapjack.Compiler.Backend.ClosToBvl
