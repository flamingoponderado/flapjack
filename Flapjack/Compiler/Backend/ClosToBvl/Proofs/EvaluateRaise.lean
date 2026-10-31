import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateSequence

/-! Raising case of the closure-to-BVL expression simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- If the operand aborts or raises, its error and the simulated state pass
through a target raise unchanged. -/
theorem evaluatePost_raise_error {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (body : Bvl.Exp) (error : ErrorResult ClosSem.Value)
    (post : evaluatePost s sFinal t targetEnv f (.err error) [body]) :
    evaluatePost s sFinal t targetEnv f (.err error) [.raise body] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨clock, .err targetError, tFinal, fFinal, ?_, related, state, map, refs, annotations, clocks⟩
    rw [BvlSem.evaluate, run]

/-- Related successful operand values become related exception payloads. -/
theorem evaluatePost_raise_value {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (body : Bvl.Exp) (value : ClosSem.Value)
    (post : evaluatePost s sFinal t targetEnv f (.val [value]) [body]) :
    evaluatePost s sFinal t targetEnv f (.err (.raise value)) [.raise body] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | err error => simp [resultRel] at related
  | val values =>
    cases related with
    | @cons source target sourceTail targetTail valueRel restRel =>
      cases restRel
      refine ⟨clock, .err (.raise target), tFinal, fFinal, ?_, ?_, state, map, refs, annotations, clocks⟩
      · rw [BvlSem.evaluate, run]
        rfl
      · exact valueRel

/-- Raising an expression satisfies the source-shaped pass simulation when
its operand satisfies the expression induction hypothesis. This candidate is
untagged until the evaluator and state carriers are reviewed against HOL. -/
theorem expressionSimulation_raise {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    expressionSimulation (C := C) (F := F) [.raise trace body] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases bodyCompile : compileExpHOL s.maxApp body aux with
  | mk targetBody auxBody =>
    have bodyCompiled : compileExpsHOL s.maxApp [body] aux = ([targetBody], auxBody) := by
      rw [compileExps_eq_list]
      simp [compileExpListHOL, bodyCompile]
    have wholeCompiled : compileExpsHOL s.maxApp [.raise trace body] aux = ([.raise targetBody], auxBody) := by
      rw [compileExps_eq_list]
      simp [compileExpListHOL, compileExpHOL, bodyCompile]
    have equal := compile.symm.trans wholeCompiled
    cases equal
    have bodyLocations : ClosProps.everyFnLocationSome [body] := by
      simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
    have bodyVars : ClosProps.everyFnVarsSome [body] := by
      simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using varsAnnotated
    rw [ClosSem.evaluate] at run
    cases bodyRun : ClosSem.evaluate [body] sourceEnv s with
    | mk bodyResult sBody =>
      rw [bodyRun] at run
      cases bodyResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact evaluatePost_raise_error s sBody t targetEnv f targetBody error
          (bodyIH s sBody t sourceEnv targetEnv f aux finalAux [targetBody] (.err error)
            bodyRun noTypeError bodyCompiled bodyLocations annotations bodyVars installed envRelated states)
      | val values =>
        obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value body sourceEnv s sBody values bodyRun
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact evaluatePost_raise_value s sBody t targetEnv f targetBody value
          (bodyIH s sBody t sourceEnv targetEnv f aux finalAux [targetBody] (.val [value])
            bodyRun (by simp) bodyCompiled bodyLocations annotations bodyVars installed envRelated states)

end Flapjack.Compiler.Backend.ClosToBvl
