import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.AnnotateCorrect
import Flapjack.Compiler.Backend.Semantics.ClosSem.Semantics

/-! Observable consequences of the candidate annotation simulation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL (Result)

/-- The terminating outcome carried by an evaluator result, with timeout
represented by absence of a terminating observation. -/
def resultOutcome : Result (List Value) Value → Option HolOutcome
  | .err (.abort .timeoutError) => none
  | .err (.abort (.ffiError event)) => some (.ffiOutcome event)
  | _ => some .success

/-- Related results agree on type errors and observable termination. -/
theorem resultRel_observations (left right : Result (List Value) Value) (related : ResultRel left right) :
    (left = .err (.abort .typeError) ↔ right = .err (.abort .typeError)) ∧
      resultOutcome left = resultOutcome right := by
  cases left with
  | val values => cases right with
    | val nextValues => simp [resultOutcome]
    | err error => cases error <;> simp [ResultRel] at related
  | err error =>
    cases right with
    | val values => cases error <;> simp [ResultRel] at related
    | err nextError =>
      cases error with
      | raise value => cases nextError <;> simp_all [ResultRel, resultOutcome]
      | abort abort =>
        cases nextError with
        | raise value => simp [ResultRel] at related
        | abort nextAbort =>
          have equal : abort = nextAbort := related
          subst nextAbort
          cases abort <;> simp [resultOutcome]

/-- Terminating observations can be expressed through `resultOutcome`. -/
theorem terminatingObservation_iff {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (program : List ClosLang.Exp) (behavior : HolBehaviour) :
    terminatingObservation ffi maxApp code oracle compiler program behavior ↔
      ∃ clock result state outcome,
        evaluate program [] (initialState ffi maxApp code oracle compiler clock) = (result, state) ∧
        resultOutcome result = some outcome ∧ behavior = .terminate outcome state.ffi.ioEvents := by
  unfold terminatingObservation
  constructor <;> rintro ⟨clock, result, state, outcome, run, out, behaviorEq⟩ <;>
    refine ⟨clock, result, state, outcome, run, ?_, behaviorEq⟩ <;>
    cases result with
    | val values => simpa [resultOutcome] using out.symm
    | err error =>
      cases error with
      | raise value => simpa [resultOutcome] using out.symm
      | abort abort => cases abort <;> simp_all [resultOutcome]

/-- Related clock-by-clock results and identical FFI states give identical
proof-side observable semantics. This congruence is Flapjack infrastructure. -/
theorem semantics_eq_of_related {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (sourceCode targetCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (sourceOracle targetOracle : CompileOracle C) (sourceCompiler targetCompiler : Compiler C)
    (program nextProgram : List ClosLang.Exp)
    (related : ∀ clock,
      ResultRel (evaluate program [] (initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock)).1
        (evaluate nextProgram [] (initialState ffi maxApp targetCode targetOracle targetCompiler clock)).1 ∧
      (evaluate program [] (initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock)).2.ffi =
        (evaluate nextProgram [] (initialState ffi maxApp targetCode targetOracle targetCompiler clock)).2.ffi) :
    semantics ffi maxApp sourceCode sourceOracle sourceCompiler program =
      semantics ffi maxApp targetCode targetOracle targetCompiler nextProgram := by
  classical
  have failureEq :
      (∃ clock, (evaluate program [] (initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock)).1 = .err (.abort .typeError)) ↔
      (∃ clock, (evaluate nextProgram [] (initialState ffi maxApp targetCode targetOracle targetCompiler clock)).1 = .err (.abort .typeError)) := by
    constructor <;> rintro ⟨clock, h⟩ <;> refine ⟨clock, ?_⟩
    · exact ((resultRel_observations _ _ (related clock).1).1).mp h
    · exact ((resultRel_observations _ _ (related clock).1).1).mpr h
  have terminatingEq : terminatingObservation ffi maxApp sourceCode sourceOracle sourceCompiler program =
      terminatingObservation ffi maxApp targetCode targetOracle targetCompiler nextProgram := by
    funext behavior
    apply propext
    rw [terminatingObservation_iff, terminatingObservation_iff]
    constructor
    · rintro ⟨clock, result, state, outcome, run, outcomeEq, behaviorEq⟩
      have obs := related clock
      rw [run] at obs
      refine ⟨clock, (evaluate nextProgram [] (initialState ffi maxApp targetCode targetOracle targetCompiler clock)).1,
        (evaluate nextProgram [] (initialState ffi maxApp targetCode targetOracle targetCompiler clock)).2, outcome,
        by exact Prod.eta _, ?_, ?_⟩
      · exact (resultRel_observations _ _ obs.1).2.symm.trans outcomeEq
      · simpa [← obs.2] using behaviorEq
    · rintro ⟨clock, result, state, outcome, run, outcomeEq, behaviorEq⟩
      have obs := related clock
      rw [run] at obs
      refine ⟨clock, (evaluate program [] (initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock)).1,
        (evaluate program [] (initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock)).2, outcome,
        by exact Prod.eta _, ?_, ?_⟩
      · exact (resultRel_observations _ _ obs.1).2.trans outcomeEq
      · simpa [obs.2] using behaviorEq
  have tracesEq :
      (fun trace => ∃ clock, trace = HolLList.fromList (evaluate program []
        (initialState ffi maxApp sourceCode sourceOracle sourceCompiler clock)).2.ffi.ioEvents) =
      (fun trace => ∃ clock, trace = HolLList.fromList (evaluate nextProgram []
        (initialState ffi maxApp targetCode targetOracle targetCompiler clock)).2.ffi.ioEvents) := by
    funext trace
    apply propext
    constructor <;> rintro ⟨clock, h⟩ <;> refine ⟨clock, ?_⟩
    · simpa [(related clock).2] using h
    · simpa [← (related clock).2] using h
  unfold semantics
  simp only [failureEq]
  rw [terminatingEq, tracesEq]

/-- Closure annotation preserves the proof-side observable behavior for a
safe program and oracle when the source semantics does not fail. The
evaluation model is not yet reviewed as a HOL port. -/
theorem annotate_semantics_correct {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C) (program : List ClosLang.Exp)
    (safe : everyFnVarsNone program)
    (oracleSafe : ∀ n, everyFnVarsNone (oracle n).2.1 ∧
      everyFnVarsNone ((oracle n).2.2.map (fun (_, _, body) => body)))
    (notFail : semantics ffi maxApp HolFiniteMapExact.empty oracle (pureCc compileInc compiler) program ≠ .fail) :
    semantics ffi maxApp HolFiniteMapExact.empty oracle (pureCc compileInc compiler) program =
      semantics ffi maxApp HolFiniteMapExact.empty (pureCo compileInc ∘ oracle) compiler (annotateList 0 program) := by
  apply semantics_eq_of_related
  intro clock
  let source := initialState ffi maxApp HolFiniteMapExact.empty oracle (pureCc compileInc compiler) clock
  let outcome := evaluate program [] source
  have noType : outcome.1 ≠ .err (.abort .typeError) := by
    exact (semantics_ne_fail_iff ffi maxApp HolFiniteMapExact.empty oracle (pureCc compileInc compiler) program).mp notFail clock
  obtain ⟨targetResult, targetNext, targetRun, results, nextRel⟩ :=
    initial_evaluate_annotated ffi maxApp clock oracle compiler program outcome.1 outcome.2
      (by exact Prod.eta _) noType safe oracleSafe
  rw [targetRun]
  exact ⟨results, nextRel.2.1⟩

end Flapjack.Compiler.Backend.ClosAnnotate
