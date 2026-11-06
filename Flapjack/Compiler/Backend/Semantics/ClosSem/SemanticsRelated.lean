import Flapjack.Compiler.Backend.Semantics.ClosSem.Semantics
import Flapjack.Compiler.Backend.Semantics.ClosSem.SemanticsSimulation
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateEventsClockFull
import Flapjack.SemanticPrimitivesProps.ResultRelation

/-! Observational consequences of same-clock simulations between programs. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- The observable terminating outcome, absent on clock exhaustion. -/
def resultOutcome (result : Result (List Value) Value) : Option HolOutcome :=
  match result with
  | .err (.abort .timeoutError) => none
  | .err (.abort (.ffiError event)) => some (.ffiOutcome event)
  | _ => some .success

/-- The result relation preserves observable termination and FFI outcomes.
This is Flapjack infrastructure for relating compiler passes. -/
theorem resultRelOutcome (values : List Value → List Value → Prop) (errors : Value → Value → Prop)
    (source target : Result (List Value) Value) (h : resultRel values errors source target) :
    resultOutcome source = resultOutcome target ∧
      (source = .err (.abort .typeError) ↔ target = .err (.abort .typeError)) := by
  cases source with
  | val a => cases target <;> simp_all [resultRel, resultOutcome]
  | err a =>
    cases target with
    | val b => simp [resultRel] at h
    | err b =>
      cases a <;> cases b <;> simp_all [resultRel, excRel, resultOutcome]

private theorem outcomeCondition (result : Result (List Value) Value) (outcome : HolOutcome) :
    (match result, outcome with
     | .err (.abort .timeoutError), _ => False
     | .err (.abort (.ffiError event)), outcome => outcome = HolOutcome.ffiOutcome event
     | _, outcome => outcome = HolOutcome.success) ↔ resultOutcome result = some outcome := by
  cases result with
  | val values => simp [resultOutcome, eq_comm]
  | err error =>
    cases error with
    | raise value => simp [resultOutcome, eq_comm]
    | abort error => cases error <;> simp [resultOutcome, eq_comm]

/-- Same-clock evaluations with the same observable result shape and FFI
state have the same whole-program behavior, even when the programs and
compiler-state carriers differ. This is Flapjack infrastructure; it does not
assume a target evaluation result in a compiler correctness statement. -/
theorem semantics_eq_of_related_evaluations {C D F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (sourceCode targetCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (sourceOracle : CompileOracle C) (targetOracle : CompileOracle D)
    (sourceCompiler : Compiler C) (targetCompiler : Compiler D)
    (sourceProgram targetProgram : List ClosLang.Exp)
    (same : ∀ clock,
      resultOutcome (evaluate sourceProgram [] (initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock)).1 =
        resultOutcome (evaluate targetProgram [] (initialState ffi maxApp targetCode targetOracle targetCompiler clock)).1 ∧
      ((evaluate sourceProgram [] (initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock)).1 = .err (.abort .typeError) ↔
        (evaluate targetProgram [] (initialState ffi maxApp targetCode targetOracle targetCompiler clock)).1 = .err (.abort .typeError)) ∧
      (evaluate sourceProgram [] (initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock)).2.ffi =
        (evaluate targetProgram [] (initialState ffi maxApp targetCode targetOracle targetCompiler clock)).2.ffi) :
    semantics ffi maxApp sourceCode sourceOracle sourceCompiler sourceProgram =
      semantics ffi maxApp targetCode targetOracle targetCompiler targetProgram := by
  classical
  have failureEq : (∃ clock, (evaluate sourceProgram [] (initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock)).1 = .err (.abort .typeError)) ↔
      (∃ clock, (evaluate targetProgram [] (initialState ffi maxApp targetCode targetOracle targetCompiler clock)).1 = .err (.abort .typeError)) := by
    constructor
    · rintro ⟨clock, h⟩; exact ⟨clock, (same clock).2.1.mp h⟩
    · rintro ⟨clock, h⟩; exact ⟨clock, (same clock).2.1.mpr h⟩
  have terminatingEq : terminatingObservation ffi maxApp sourceCode sourceOracle sourceCompiler sourceProgram =
      terminatingObservation ffi maxApp targetCode targetOracle targetCompiler targetProgram := by
    funext behavior
    unfold terminatingObservation
    apply propext
    constructor
    · rintro ⟨clock, result, final, outcome, run, condition, behaviorEq⟩
      cases targetRun : evaluate targetProgram [] (initialState ffi maxApp targetCode targetOracle targetCompiler clock) with
      | mk targetResult targetFinal =>
        have observation := same clock
        rw [run, targetRun] at observation
        simp only at observation
        have outcomeEq := (outcomeCondition result outcome).mp condition
        refine ⟨clock, targetResult, targetFinal, outcome, targetRun, ?_, ?_⟩
        · apply (outcomeCondition targetResult outcome).mpr
          exact observation.1.symm.trans outcomeEq
        · simpa [observation.2.2] using behaviorEq
    · rintro ⟨clock, result, final, outcome, run, condition, behaviorEq⟩
      cases sourceRun : evaluate sourceProgram [] (initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock) with
      | mk sourceResult sourceFinal =>
        have observation := same clock
        rw [sourceRun, run] at observation
        simp only at observation
        have outcomeEq := (outcomeCondition result outcome).mp condition
        refine ⟨clock, sourceResult, sourceFinal, outcome, sourceRun, ?_, ?_⟩
        · apply (outcomeCondition sourceResult outcome).mpr
          exact observation.1.trans outcomeEq
        · simpa [← observation.2.2] using behaviorEq
  have traceEq : (fun trace => ∃ clock, trace = HolLList.fromList
      (evaluate sourceProgram [] (initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock)).2.ffi.ioEvents) =
      (fun trace => ∃ clock, trace = HolLList.fromList
        (evaluate targetProgram [] (initialState ffi maxApp targetCode targetOracle targetCompiler clock)).2.ffi.ioEvents) := by
    funext trace
    apply propext
    constructor <;> rintro ⟨clock, eq⟩ <;> refine ⟨clock, ?_⟩
    · simpa [(same clock).2.2] using eq
    · simpa [(same clock).2.2] using eq
  unfold semantics
  rw [failureEq, terminatingEq, traceEq]


/-- A forward simulation with a target clock allowance preserves whole-program
behavior when it preserves observable result shape and FFI state. The source
and target may use different programs, code maps, and compiler carriers. This
is Flapjack-specific observational infrastructure. -/
theorem semantics_eq_of_related_clocked_simulation {C D F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (sourceCode targetCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (sourceOracle : CompileOracle C) (targetOracle : CompileOracle D)
    (sourceCompiler : Compiler C) (targetCompiler : Compiler D)
    (sourceProgram targetProgram : List ClosLang.Exp)
    (sourceSafe : ∀ clock, (evaluate sourceProgram [] (initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock)).1 ≠ .err (.abort .typeError))
    (simulation : ∀ clock result final,
      evaluate sourceProgram [] (initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock) = (result, final) →
      ∃ extra targetResult targetFinal,
        evaluate targetProgram [] (initialState ffi maxApp targetCode targetOracle targetCompiler (clock + extra)) =
          (targetResult, targetFinal) ∧
        resultOutcome result = resultOutcome targetResult ∧
        (result = .err (.abort .typeError) ↔ targetResult = .err (.abort .typeError)) ∧
        final.ffi = targetFinal.ffi) :
    semantics ffi maxApp sourceCode sourceOracle sourceCompiler sourceProgram =
      semantics ffi maxApp targetCode targetOracle targetCompiler targetProgram := by
  classical
  have targetSafe : ∀ clock, (evaluate targetProgram [] (initialState ffi maxApp targetCode targetOracle targetCompiler clock)).1 ≠ .err (.abort .typeError) := by
    intro clock targetError
    cases sourceRun : evaluate sourceProgram [] (initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock) with
    | mk sourceResult sourceFinal =>
      obtain ⟨extra, targetResult, targetFinal, targetRun, _, errorEq, _⟩ := simulation clock sourceResult sourceFinal sourceRun
      cases targetRun0 : evaluate targetProgram [] (initialState ffi maxApp targetCode targetOracle targetCompiler clock) with
      | mk oldResult oldFinal =>
        have oldError : oldResult = .err (.abort .typeError) := by simpa [targetRun0] using targetError
        subst oldResult
        have shifted := evaluate_initial_addClock ffi maxApp clock extra targetCode targetOracle targetCompiler targetProgram
          (.err (.abort .typeError)) oldFinal targetRun0 (by simp)
        rw [targetRun] at shifted
        have targetEq : targetResult = .err (.abort .typeError) := (Prod.mk.inj shifted).1
        exact sourceSafe clock (by simpa [sourceRun] using errorEq.mpr targetEq)
  have terminatingEq : terminatingObservation ffi maxApp sourceCode sourceOracle sourceCompiler sourceProgram =
      terminatingObservation ffi maxApp targetCode targetOracle targetCompiler targetProgram := by
    funext behavior
    apply propext
    constructor
    · rintro ⟨clock, result, final, outcome, run, outcomeEq, behaviorEq⟩
      obtain ⟨extra, targetResult, targetFinal, targetRun, resultEq, _, ffiEq⟩ := simulation clock result final run
      refine ⟨clock + extra, targetResult, targetFinal, outcome, targetRun, ?_, ?_⟩
      · exact (outcomeCondition targetResult outcome).mpr (resultEq.symm.trans ((outcomeCondition result outcome).mp outcomeEq))
      · simpa [ffiEq] using behaviorEq
    · rintro ⟨clock, result, targetFinal, outcome, targetRun, outcomeEq, behaviorEq⟩
      have notTimeout : result ≠ .err (.abort .timeoutError) := by
        intro impossible
        subst result
        simp at outcomeEq
      cases sourceRun : evaluate sourceProgram [] (initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock) with
      | mk sourceResult sourceFinal =>
        obtain ⟨extra, simulatedResult, simulatedFinal, simulatedRun, resultEq, _, ffiEq⟩ := simulation clock sourceResult sourceFinal sourceRun
        have shifted := evaluate_initial_addClock ffi maxApp clock extra targetCode targetOracle targetCompiler targetProgram
          result targetFinal targetRun notTimeout
        rw [simulatedRun] at shifted
        obtain ⟨resultSame, stateSame⟩ := Prod.mk.inj shifted
        have sourceOutcome : resultOutcome sourceResult = some outcome := by
          rw [resultEq, resultSame]
          exact (outcomeCondition result outcome).mp outcomeEq
        have finalFfi : sourceFinal.ffi = targetFinal.ffi := by rw [ffiEq, stateSame]
        exact ⟨clock, sourceResult, sourceFinal, outcome, sourceRun,
          (outcomeCondition sourceResult outcome).mpr sourceOutcome, by simpa [finalFfi] using behaviorEq⟩
  have tracesEq :
      HolLList.buildLprefixLub (fun trace => ∃ clock,
        trace = HolLList.fromList (evaluate sourceProgram [] (initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock)).2.ffi.ioEvents) =
      HolLList.buildLprefixLub (fun trace => ∃ clock,
        trace = HolLList.fromList (evaluate targetProgram [] (initialState ffi maxApp targetCode targetOracle targetCompiler clock)).2.ffi.ioEvents) := by
    apply clocked_traces_lub_eq _ _
      (evaluate_initial_ioEvents_mono ffi maxApp sourceCode sourceOracle sourceCompiler sourceProgram)
      (evaluate_initial_ioEvents_mono ffi maxApp targetCode targetOracle targetCompiler targetProgram)
    intro clock
    cases sourceRun : evaluate sourceProgram [] (initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock) with
    | mk result final =>
      obtain ⟨extra, targetResult, targetFinal, targetRun, _, _, ffiEq⟩ := simulation clock result final sourceRun
      exact ⟨extra, by simp [targetRun, ffiEq]⟩
  unfold semantics
  simp only [show ¬ ∃ clock, (evaluate sourceProgram [] (initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock)).1 = .err (.abort .typeError) from
    fun ⟨clock, error⟩ => sourceSafe clock error,
    show ¬ ∃ clock, (evaluate targetProgram [] (initialState ffi maxApp targetCode targetOracle targetCompiler clock)).1 = .err (.abort .typeError) from
    fun ⟨clock, error⟩ => targetSafe clock error, if_false]
  rw [terminatingEq, tracesEq]

end Flapjack.Compiler.Backend.ClosSem
