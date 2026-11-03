import Flapjack.Compiler.Backend.Semantics.ClosSem.Semantics
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

end Flapjack.Compiler.Backend.ClosSem
