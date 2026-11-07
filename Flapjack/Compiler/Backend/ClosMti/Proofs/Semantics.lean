import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluateMutual
import Flapjack.Compiler.Backend.Semantics.ClosSem.Semantics

/-! Observable consequences for the current Lean closure evaluator. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem BackendProps SemanticPrimitivesProps

/-- Initial states are related when the source oracle satisfies the unary and
empty-label invariant. This is Lean-side infrastructure pending HOL review. -/
theorem initialStates_related {C F : Type} (ffi : HolFfiState F) (maxApp clock : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C)
    (positive : 1 ≤ maxApp)
    (safe : ∀ n, (oracle n).2.2 = [] ∧ ∀ e ∈ (oracle n).2.1, ClosProps.noMti e) :
    StateRel
      (initialState ffi maxApp HolFiniteMapExact.empty oracle (pureCc (compileInc maxApp) compiler) clock)
      (initialState ffi maxApp HolFiniteMapExact.empty (pureCo (compileInc maxApp) ∘ oracle) compiler clock) := by
  refine ⟨safe, rfl, rfl, rfl, positive, rfl, rfl, .nil, ?_, rfl, rfl⟩
  constructor
  · intro key
    simp [initialState, HolFiniteMapExact.empty]
  · intro key value found
    simp [initialState, HolFiniteMapExact.empty] at found

/-- Related evaluator results agree on an abort reason. -/
theorem resultRel_abort_iff {A B C D : Type} (values : A → B → Prop) (errors : C → D → Prop)
    (left : SemanticPrimitivesHOL.Result A C) (right : SemanticPrimitivesHOL.Result B D)
    (related : resultRel values errors left right) (reason : SemanticPrimitivesHOL.Abort) :
    left = .err (.abort reason) ↔ right = .err (.abort reason) := by
  cases left <;> cases right <;> simp_all [resultRel]
  case err.err leftError rightError =>
    cases leftError <;> cases rightError <;> simp_all [excRel]

/-- The outcome admitted by a closure result, excluding clock exhaustion. -/
def terminatingResult {A B : Type} (result : SemanticPrimitivesHOL.Result A B) (outcome : HolOutcome) : Prop :=
  match result with
  | .err (.abort .timeoutError) => False
  | .err (.abort (.ffiError event)) => outcome = .ffiOutcome event
  | _ => outcome = .success

/-- Related evaluator results induce the same termination outcome predicate. -/
theorem resultRel_termination_iff {A B C D : Type} (values : A → B → Prop) (errors : C → D → Prop)
    (left : SemanticPrimitivesHOL.Result A C) (right : SemanticPrimitivesHOL.Result B D)
    (related : resultRel values errors left right) (outcome : HolOutcome) :
    terminatingResult left outcome ↔ terminatingResult right outcome := by
  cases left <;> cases right <;> simp_all [resultRel, terminatingResult]
  case err.err leftError rightError =>
    cases leftError <;> cases rightError <;> simp_all [excRel]
    case abort.abort leftAbort rightAbort =>
      subst rightAbort
      cases leftAbort <;> rfl

/-- Related clock-indexed results and equal FFI states imply equal
observations, even when successful values use different representations. -/
theorem semantics_eq_of_related_observations {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (sourceOracle targetOracle : CompileOracle C)
    (sourceCompiler targetCompiler : Compiler C) (sourceProgram targetProgram : List ClosLang.Exp)
    (related : ∀ clock,
      resultRel (List.Forall₂ (ValueRel maxApp)) (ValueRel maxApp)
        (evaluate sourceProgram [] (initialState ffi maxApp code sourceOracle sourceCompiler clock)).1
        (evaluate targetProgram [] (initialState ffi maxApp code targetOracle targetCompiler clock)).1 ∧
      (evaluate sourceProgram [] (initialState ffi maxApp code sourceOracle sourceCompiler clock)).2.ffi =
        (evaluate targetProgram [] (initialState ffi maxApp code targetOracle targetCompiler clock)).2.ffi) :
    semantics ffi maxApp code sourceOracle sourceCompiler sourceProgram =
      semantics ffi maxApp code targetOracle targetCompiler targetProgram := by
  classical
  have failureEq :
      (∃ clock, (evaluate sourceProgram [] (initialState ffi maxApp code sourceOracle sourceCompiler clock)).1 =
        .err (.abort .typeError)) ↔
      (∃ clock, (evaluate targetProgram [] (initialState ffi maxApp code targetOracle targetCompiler clock)).1 =
        .err (.abort .typeError)) := by
    constructor <;> rintro ⟨clock, failure⟩ <;> refine ⟨clock, ?_⟩
    · exact (resultRel_abort_iff _ _ _ _ (related clock).1 _).mp failure
    · exact (resultRel_abort_iff _ _ _ _ (related clock).1 _).mpr failure
  have terminatingEq : terminatingObservation ffi maxApp code sourceOracle sourceCompiler sourceProgram =
      terminatingObservation ffi maxApp code targetOracle targetCompiler targetProgram := by
    funext behavior
    unfold terminatingObservation
    apply propext
    constructor
    · rintro ⟨clock, result, state, outcome, run, outcomeEq, behaviorEq⟩
      have observed := related clock
      rw [run] at observed
      refine ⟨clock, (evaluate targetProgram [] (initialState ffi maxApp code targetOracle targetCompiler clock)).1,
        (evaluate targetProgram [] (initialState ffi maxApp code targetOracle targetCompiler clock)).2,
        outcome, ?_, ?_, ?_⟩
      · exact (Prod.eta _).symm
      · have initial : terminatingResult result outcome := by
          cases result with
          | val value => simpa [terminatingResult] using outcomeEq
          | err error =>
            cases error with
            | raise value => simpa [terminatingResult] using outcomeEq
            | abort reason => cases reason <;> simp [terminatingResult] at outcomeEq ⊢ <;> assumption
        have output := (resultRel_termination_iff _ _ _ _ observed.1 outcome).mp initial
        cases evaluated : (evaluate targetProgram []
            (initialState ffi maxApp code targetOracle targetCompiler clock)).1 with
        | val value => simpa [evaluated, terminatingResult] using output
        | err error =>
          cases error with
          | raise value => simpa [evaluated, terminatingResult] using output
          | abort reason => cases reason <;> simp [evaluated, terminatingResult] at output ⊢ <;> assumption
      · simpa [← observed.2] using behaviorEq
    · rintro ⟨clock, result, state, outcome, run, outcomeEq, behaviorEq⟩
      have observed := related clock
      rw [run] at observed
      refine ⟨clock, (evaluate sourceProgram [] (initialState ffi maxApp code sourceOracle sourceCompiler clock)).1,
        (evaluate sourceProgram [] (initialState ffi maxApp code sourceOracle sourceCompiler clock)).2,
        outcome, ?_, ?_, ?_⟩
      · exact (Prod.eta _).symm
      · have initial : terminatingResult result outcome := by
          cases result with
          | val value => simpa [terminatingResult] using outcomeEq
          | err error =>
            cases error with
            | raise value => simpa [terminatingResult] using outcomeEq
            | abort reason => cases reason <;> simp [terminatingResult] at outcomeEq ⊢ <;> assumption
        have output := (resultRel_termination_iff _ _ _ _ observed.1 outcome).mpr initial
        cases evaluated : (evaluate sourceProgram []
            (initialState ffi maxApp code sourceOracle sourceCompiler clock)).1 with
        | val value => simpa [evaluated, terminatingResult] using output
        | err error =>
          cases error with
          | raise value => simpa [evaluated, terminatingResult] using output
          | abort reason => cases reason <;> simp [evaluated, terminatingResult] at output ⊢ <;> assumption
      · simpa [observed.2] using behaviorEq
  have tracesEq :
      (fun trace => ∃ clock, trace = HolLList.fromList
        (evaluate sourceProgram [] (initialState ffi maxApp code sourceOracle sourceCompiler clock)).2.ffi.ioEvents) =
      (fun trace => ∃ clock, trace = HolLList.fromList
        (evaluate targetProgram [] (initialState ffi maxApp code targetOracle targetCompiler clock)).2.ffi.ioEvents) := by
    funext trace
    apply propext
    constructor <;> rintro ⟨clock, equal⟩ <;> refine ⟨clock, ?_⟩
    · simpa [(related clock).2] using equal
    · simpa [← (related clock).2] using equal
  unfold semantics
  simp only [failureEq]
  rw [terminatingEq, tracesEq]

/-- Multi-argument introduction preserves the current Lean observational
semantics under the unary oracle and program invariants. This source-shaped
result is not tagged as the HOL theorem: the evaluator, state carriers, and
observational semantics still require correspondence review. -/
theorem semantics_introMulti_candidate {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C) (program : List ClosLang.Exp)
    (positive : 1 ≤ maxApp)
    (safe : ∀ n, (oracle n).2.2 = [] ∧ ∀ e ∈ (oracle n).2.1, ClosProps.noMti e)
    (unary : ∀ e ∈ program, ClosProps.noMti e) :
    semantics ffi maxApp HolFiniteMapExact.empty oracle (pureCc (compileInc maxApp) compiler) program =
      semantics ffi maxApp HolFiniteMapExact.empty (pureCo (compileInc maxApp) ∘ oracle) compiler
        (introList maxApp program) := by
  apply semantics_eq_of_related_observations
  intro clock
  let source := initialState ffi maxApp HolFiniteMapExact.empty oracle (pureCc (compileInc maxApp) compiler) clock
  let target := initialState ffi maxApp HolFiniteMapExact.empty (pureCo (compileInc maxApp) ∘ oracle) compiler clock
  have states : StateRel source target := initialStates_related ffi maxApp clock oracle compiler positive safe
  cases sourceRun : evaluate program [] source with
  | mk sourceResult sourceFinal =>
    obtain ⟨targetResult, targetFinal, targetRun, resultsRelated, finalStates⟩ :=
      introMulti_correct_candidate program [] [] source target sourceFinal sourceResult sourceRun unary .nil states
    change resultRel (List.Forall₂ (ValueRel maxApp)) (ValueRel maxApp)
      sourceResult (evaluate (introList maxApp program) [] target).1 ∧
      sourceFinal.ffi = (evaluate (introList maxApp program) [] target).2.ffi
    have targetRun' : evaluate (introList maxApp program) [] target = (targetResult, targetFinal) := by
      simpa [source, initialState] using targetRun
    rw [targetRun']
    exact ⟨by simpa [source, initialState] using resultsRelated, finalStates.2.2.2.2.2.2.1.symm⟩

/-- The optional multi-argument pass preserves the current Lean
observational semantics. The compiler route and HOL correspondence require
separate review, so this is not tagged as the original theorem. -/
theorem semantics_compile_candidate {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (enabled : Bool) (oracle : CompileOracle C) (compiler : Compiler C) (program : List ClosLang.Exp)
    (positive : enabled = true → 1 ≤ maxApp)
    (safe : enabled = true → ∀ n, (oracle n).2.2 = [] ∧ ∀ e ∈ (oracle n).2.1, ClosProps.noMti e)
    (unary : enabled = true → ∀ e ∈ program, ClosProps.noMti e) :
    semantics ffi maxApp HolFiniteMapExact.empty oracle
      (if enabled then pureCc (compileInc maxApp) compiler else compiler) program =
    semantics ffi maxApp HolFiniteMapExact.empty
      (if enabled then pureCo (compileInc maxApp) ∘ oracle else oracle) compiler
      (compile enabled maxApp program) := by
  cases enabled with
  | false => rfl
  | true =>
    simpa [compile] using semantics_introMulti_candidate ffi maxApp oracle compiler program
      (positive rfl) (safe rfl) (unary rfl)

end Flapjack.Compiler.Backend.ClosMti
