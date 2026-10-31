import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateSequence

/-! Tick case of the closure-to-BVL expression simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- A tick satisfies the pass simulation when its operand satisfies the
expression induction hypothesis. The zero-clock and positive-clock paths
are both covered; this candidate remains untagged pending carrier review. -/
theorem expressionSimulation_tick {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    expressionSimulation (C := C) (F := F) [.tick trace body] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases bodyCompile : compileExpHOL s.maxApp body aux with
  | mk targetBody auxBody =>
    have bodyCompiled : compileExpsHOL s.maxApp [body] aux = ([targetBody], auxBody) := by
      rw [compileExps_eq_list]
      simp [compileExpListHOL, bodyCompile]
    have wholeCompiled : compileExpsHOL s.maxApp [.tick trace body] aux = ([.tick targetBody], auxBody) := by
      rw [compileExps_eq_list]
      simp [compileExpListHOL, compileExpHOL, bodyCompile]
    have equal := compile.symm.trans wholeCompiled
    cases equal
    have bodyLocations : ClosProps.everyFnLocationSome [body] := by
      simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
    have bodyVars : ClosProps.everyFnVarsSome [body] := by
      simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using varsAnnotated
    by_cases zero : s.clock = 0
    · simp [ClosSem.evaluate, zero] at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨0, .err (.abort .timeoutError), { t with clock := 0 }, f, ?_, ?_, ?_, ?_, ?_, annotations, ?_⟩
      · simp [BvlSem.evaluate, zero]
      · simp [resultRel, excRel]
      · exact (stateRel_clock f s t 0).1.mpr states
      · intro key value lookup
        exact lookup
      · intro key value lookup fresh
        exact ⟨lookup, fresh⟩
      · simpa using zero
    · have bodyRun : ClosSem.evaluate [body] sourceEnv (ClosSem.decClock 1 s) = (result, sFinal) := by
        simpa [ClosSem.evaluate, zero] using run
      have bodyState : stateRel f (ClosSem.decClock 1 s) t := by
        exact (stateRel_clock f s t (s.clock - 1)).2.mpr states
      have bodyAnnotations : codeAnnotations (ClosSem.decClock 1 s) := by
        simpa [codeAnnotations, ClosSem.decClock] using annotations
      have bodyPost := bodyIH (ClosSem.decClock 1 s) sFinal t sourceEnv targetEnv f aux finalAux
        [targetBody] result bodyRun noTypeError (by simpa [ClosSem.decClock] using bodyCompiled)
        bodyLocations bodyAnnotations bodyVars installed (by simpa [ClosSem.decClock] using envRelated) bodyState
      obtain ⟨clock, targetResult, tFinal, fFinal, targetRun, related, finalState, map, refs,
        finalAnnotations, clocks⟩ := bodyPost
      have positive : s.clock + clock ≠ 0 := by omega
      have clockEq : s.clock + clock - 1 = s.clock - 1 + clock := by omega
      refine ⟨clock, targetResult, tFinal, fFinal, ?_, ?_, finalState, map, refs, finalAnnotations, clocks⟩
      · rw [BvlSem.evaluate]
        simp only [positive, ↓reduceIte]
        simpa [BvlSem.decClock, ClosSem.decClock, clockEq] using targetRun
      · simpa [ClosSem.decClock] using related

end Flapjack.Compiler.Backend.ClosToBvl
