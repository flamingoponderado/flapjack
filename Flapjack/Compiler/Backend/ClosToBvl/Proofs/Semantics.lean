module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateAll
public import Flapjack.Compiler.Backend.Semantics.ClosSem.SemanticsSimulation
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateEventsClockFull
public import Flapjack.Compiler.Backend.Semantics.BvlSem.Semantics
public import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateEventsClock

@[expose] public section

/-! Observable consequences of the closure-to-BVL simulation candidate.
The evaluators and their carriers remain subject to source review. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- Result relation after discarding the different value representations. -/
def observableResultRel (source : Result (List ClosSem.Value) ClosSem.Value)
    (target : Result (List BvlSem.Value) BvlSem.Value) : Prop :=
  resultRel (fun _ _ => True) (fun _ _ => True) source target

/-- The source-shaped forward simulation of an initial closure program by a
BVL entry point. This is Flapjack infrastructure, not a reviewed HOL port. -/
def initialEvaluationSimulation {C₁ C₂ F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (sourceCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (sourceOracle : ClosSem.CompileOracle C₁)
    (sourceCompiler : ClosSem.Compiler C₁) (program : List ClosLang.Exp)
    (targetCode : Spt (Nat × Bvl.Exp)) (targetOracle : BvlSem.CompileOracle C₂)
    (targetCompiler : BvlSem.Compiler C₂) (start : Nat) : Prop :=
  ∀ clock result final,
    ClosSem.evaluate program [] (ClosSem.initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock) = (result, final) →
    result ≠ .err (.abort .typeError) →
    ∃ extra targetResult targetFinal,
      BvlSem.evaluate [.call 0 (some start) []] []
        (BvlSem.initialState ffi targetCode targetOracle targetCompiler (clock + extra)) = (targetResult, targetFinal) ∧
      observableResultRel result targetResult ∧ final.ffi = targetFinal.ffi

/-- A related target type error is necessarily a source type error. -/
theorem observableResultRel_target_typeError {source : Result (List ClosSem.Value) ClosSem.Value}
    (related : observableResultRel source (.err (.abort .typeError))) :
    source = .err (.abort .typeError) := by
  cases source with
  | val values => simp [observableResultRel, resultRel] at related
  | err error =>
    cases error with
    | raise value => simp [observableResultRel, resultRel, excRel] at related
    | abort reason =>
      simp [observableResultRel, resultRel, excRel] at related
      simp [related]

/-- Source safety and forward clock extension rule out target type errors at
every initial clock, including clocks below the chosen simulation clock. -/
theorem initialSimulation_targetSafe {C₁ C₂ F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (sourceCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (sourceOracle : ClosSem.CompileOracle C₁)
    (sourceCompiler : ClosSem.Compiler C₁) (program : List ClosLang.Exp)
    (targetCode : Spt (Nat × Bvl.Exp)) (targetOracle : BvlSem.CompileOracle C₂)
    (targetCompiler : BvlSem.Compiler C₂) (start : Nat)
    (sourceSafe : ∀ clock, (ClosSem.evaluate program []
      (ClosSem.initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock)).1 ≠ .err (.abort .typeError))
    (simulation : initialEvaluationSimulation ffi maxApp sourceCode sourceOracle sourceCompiler program
      targetCode targetOracle targetCompiler start) :
    ∀ clock, (BvlSem.evaluate [.call 0 (some start) []] []
      (BvlSem.initialState ffi targetCode targetOracle targetCompiler clock)).1 ≠ .err (.abort .typeError) := by
  intro clock targetError
  cases sourceRun : ClosSem.evaluate program []
      (ClosSem.initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock) with
  | mk sourceResult sourceFinal =>
    have notType : sourceResult ≠ .err (.abort .typeError) := by simpa [sourceRun] using sourceSafe clock
    obtain ⟨extra, targetResult, targetFinal, targetRun, related, _⟩ :=
      simulation clock sourceResult sourceFinal sourceRun notType
    cases targetRun0 : BvlSem.evaluate [.call 0 (some start) []] []
        (BvlSem.initialState ffi targetCode targetOracle targetCompiler clock) with
    | mk result0 final0 =>
      have resultEq : result0 = .err (.abort .typeError) := by simpa [targetRun0] using targetError
      subst result0
      have shifted := BvlProps.evaluate_addClock [.call 0 (some start) []] []
        (BvlSem.initialState ffi targetCode targetOracle targetCompiler clock) final0
        (.err (.abort .typeError)) extra targetRun0 (by simp)
      have shifted' : BvlSem.evaluate [.call 0 (some start) []] []
          (BvlSem.initialState ffi targetCode targetOracle targetCompiler (clock + extra)) =
          (.err (.abort .typeError), { final0 with clock := final0.clock + extra }) := by
        simpa [BvlSem.initialState] using shifted
      rw [targetRun] at shifted'
      have targetEq : targetResult = .err (.abort .typeError) := (Prod.mk.inj shifted').1
      rw [targetEq] at related
      exact notType (observableResultRel_target_typeError related)

/-- The termination outcome records only timeout and the final FFI event,
not the language-specific value returned by the evaluator. -/
def resultObservesOutcome {α β : Type} (result : Result α β) (outcome : HolOutcome) : Prop :=
  match result with
  | .err (.abort .timeoutError) => False
  | .err (.abort (.ffiError event)) => outcome = .ffiOutcome event
  | _ => outcome = .success

/-- Related closure and BVL results have exactly the same termination outcome. -/
theorem observableResultRel_outcome {source : Result (List ClosSem.Value) ClosSem.Value}
    {target : Result (List BvlSem.Value) BvlSem.Value} (related : observableResultRel source target)
    (outcome : HolOutcome) : resultObservesOutcome source outcome ↔ resultObservesOutcome target outcome := by
  cases source with
  | val sourceValues =>
    cases target with
    | val targetValues => rfl
    | err error => simp [observableResultRel, resultRel] at related
  | err sourceError =>
    cases target with
    | val values => simp [observableResultRel, resultRel] at related
    | err targetError =>
      cases sourceError with
      | raise sourceValue =>
        cases targetError with
        | raise targetValue => rfl
        | abort reason => simp [observableResultRel, resultRel, excRel] at related
      | abort sourceReason =>
        cases targetError with
        | raise value => simp [observableResultRel, resultRel, excRel] at related
        | abort targetReason =>
          have same : sourceReason = targetReason := by simpa [observableResultRel, resultRel, excRel] using related
          subst targetReason
          cases sourceReason <;> rfl

/-- A result that has a terminating observation cannot be a timeout. -/
theorem resultObservesOutcome_notTimeout {α β : Type} (result : Result α β) (outcome : HolOutcome)
    (observes : resultObservesOutcome result outcome) : result ≠ .err (.abort .timeoutError) := by
  intro equal
  subst result
  exact observes

/-- Forward simulation and source safety determine the same terminating
observations even though the two languages return different value types. -/
theorem initialSimulation_terminatingObservation_eq {C₁ C₂ F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (sourceCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (sourceOracle : ClosSem.CompileOracle C₁)
    (sourceCompiler : ClosSem.Compiler C₁) (program : List ClosLang.Exp)
    (targetCode : Spt (Nat × Bvl.Exp)) (targetOracle : BvlSem.CompileOracle C₂)
    (targetCompiler : BvlSem.Compiler C₂) (start : Nat)
    (sourceSafe : ∀ clock, (ClosSem.evaluate program []
      (ClosSem.initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock)).1 ≠ .err (.abort .typeError))
    (simulation : initialEvaluationSimulation ffi maxApp sourceCode sourceOracle sourceCompiler program
      targetCode targetOracle targetCompiler start) :
    ClosSem.terminatingObservation ffi maxApp sourceCode sourceOracle sourceCompiler program =
      BvlSem.terminatingObservation ffi targetCode targetOracle targetCompiler start := by
  funext behavior
  apply propext
  constructor
  · rintro ⟨clock, result, final, outcome, run, observes, behaviorEq⟩
    have notType : result ≠ .err (.abort .typeError) := by simpa [run] using sourceSafe clock
    obtain ⟨extra, targetResult, targetFinal, targetRun, related, ffiEq⟩ :=
      simulation clock result final run notType
    have sourceOutcome : resultObservesOutcome result outcome := by
      cases result with
      | val value => exact observes
      | err error => cases error with
        | raise value => exact observes
        | abort reason => cases reason <;> exact observes
    have targetOutcome := (observableResultRel_outcome related outcome).mp sourceOutcome
    refine ⟨clock + extra, targetResult, targetFinal, outcome, ?_, ?_, ?_⟩
    · exact targetRun
    · cases targetResult with
      | val value => exact targetOutcome
      | err error => cases error with
        | raise value => exact targetOutcome
        | abort reason => cases reason <;> exact targetOutcome
    · simpa [ffiEq] using behaviorEq
  · rintro ⟨clock, targetResult, targetFinal, outcome, targetRun, observes, behaviorEq⟩
    have targetOutcome : resultObservesOutcome targetResult outcome := by
      cases targetResult with
      | val value => exact observes
      | err error => cases error with
        | raise value => exact observes
        | abort reason => cases reason <;> exact observes
    have notTimeout := resultObservesOutcome_notTimeout targetResult outcome targetOutcome
    cases sourceRun : ClosSem.evaluate program []
        (ClosSem.initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock) with
    | mk sourceResult sourceFinal =>
      have notType : sourceResult ≠ .err (.abort .typeError) := by simpa [sourceRun] using sourceSafe clock
      obtain ⟨extra, result2, final2, targetRun2, related, ffiEq⟩ :=
        simulation clock sourceResult sourceFinal sourceRun notType
      have shifted := BvlProps.evaluate_addClock [.call 0 (some start) []] []
        (BvlSem.initialState ffi targetCode targetOracle targetCompiler clock) targetFinal targetResult extra
        targetRun notTimeout
      have shifted' : BvlSem.evaluate [.call 0 (some start) []] []
          (BvlSem.initialState ffi targetCode targetOracle targetCompiler (clock + extra)) =
          (targetResult, { targetFinal with clock := targetFinal.clock + extra }) := by
        simpa [BvlSem.initialState] using shifted
      rw [targetRun2] at shifted'
      obtain ⟨resultEq, stateEq⟩ := Prod.mk.inj shifted'
      subst result2
      have finalFfi : sourceFinal.ffi = targetFinal.ffi := by rw [ffiEq, stateEq]
      have sourceOutcome := (observableResultRel_outcome related outcome).mpr targetOutcome
      refine ⟨clock, sourceResult, sourceFinal, outcome, sourceRun, ?_, by simpa [finalFfi] using behaviorEq⟩
      cases sourceResult with
      | val value => exact sourceOutcome
      | err error => cases error with
        | raise value => exact sourceOutcome
        | abort reason => cases reason <;> exact sourceOutcome

/-- A non-failing closure program and its forward-simulated BVL entry have
the same proof-side whole-program behavior, including divergence traces. The
simulation is an explicit prerequisite until the initial code and oracle
relations are connected to the expression proof. -/
theorem semantics_eq_of_initialSimulation {C₁ C₂ F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (sourceCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (sourceOracle : ClosSem.CompileOracle C₁)
    (sourceCompiler : ClosSem.Compiler C₁) (program : List ClosLang.Exp)
    (targetCode : Spt (Nat × Bvl.Exp)) (targetOracle : BvlSem.CompileOracle C₂)
    (targetCompiler : BvlSem.Compiler C₂) (start : Nat)
    (nonfail : ClosSem.semantics ffi maxApp sourceCode sourceOracle sourceCompiler program ≠ .fail)
    (simulation : initialEvaluationSimulation ffi maxApp sourceCode sourceOracle sourceCompiler program
      targetCode targetOracle targetCompiler start) :
    BvlSem.semantics ffi targetCode targetOracle targetCompiler start =
      ClosSem.semantics ffi maxApp sourceCode sourceOracle sourceCompiler program := by
  classical
  have sourceSafe := (ClosSem.semantics_ne_fail_iff ffi maxApp sourceCode sourceOracle sourceCompiler program).mp nonfail
  have targetSafe := initialSimulation_targetSafe ffi maxApp sourceCode sourceOracle sourceCompiler program
    targetCode targetOracle targetCompiler start sourceSafe simulation
  have terminatingEq := initialSimulation_terminatingObservation_eq ffi maxApp sourceCode sourceOracle sourceCompiler
    program targetCode targetOracle targetCompiler start sourceSafe simulation
  have traceEq :
      HolLList.buildLprefixLub (fun trace => ∃ clock,
        trace = HolLList.fromList (ClosSem.evaluate program []
          (ClosSem.initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock)).2.ffi.ioEvents) =
      HolLList.buildLprefixLub (fun trace => ∃ clock,
        trace = HolLList.fromList (BvlSem.evaluate [.call 0 (some start) []] []
          (BvlSem.initialState ffi targetCode targetOracle targetCompiler clock)).2.ffi.ioEvents) := by
    apply ClosSem.clocked_traces_lub_eq
    · exact ClosSem.evaluate_initial_ioEvents_mono ffi maxApp sourceCode sourceOracle sourceCompiler program
    · intro k l bound
      obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le bound
      simpa [BvlSem.initialState] using BvlProps.evaluate_addClock_ioEvents_prefix [.call 0 (some start) []] []
        (BvlSem.initialState ffi targetCode targetOracle targetCompiler k) extra
    · intro clock
      cases sourceRun : ClosSem.evaluate program []
          (ClosSem.initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock) with
      | mk result final =>
        have notType : result ≠ .err (.abort .typeError) := by simpa [sourceRun] using sourceSafe clock
        obtain ⟨extra, targetResult, targetFinal, targetRun, _, ffiEq⟩ :=
          simulation clock result final sourceRun notType
        exact ⟨extra, by simp [targetRun, ffiEq]⟩
  unfold BvlSem.semantics ClosSem.semantics
  simp only [show ¬ ∃ clock, (ClosSem.evaluate program []
      (ClosSem.initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock)).1 = .err (.abort .typeError) from
        fun ⟨clock, error⟩ => sourceSafe clock error,
    show ¬ ∃ clock, (BvlSem.evaluateTuple ([.call 0 (some start) []], [],
      BvlSem.initialState ffi targetCode targetOracle targetCompiler clock)).1 = .err (.abort .typeError) from
        fun ⟨clock, error⟩ => targetSafe clock error, if_false]
  rw [terminatingEq, traceEq]
  rfl

end Flapjack.Compiler.Backend.ClosToBvl
