import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import Flapjack.Misc.LprefixLub

/-! Observations of the proof-side closure evaluator. The evaluator and state
carriers still require HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- A terminating observation of a clocked closure evaluation. -/
def terminatingObservation {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (program : List ClosLang.Exp) (behavior : HolBehaviour) : Prop :=
  ∃ clock result state outcome,
    evaluate program [] (initialState ffi maxApp code oracle compiler clock) = (result, state) ∧
    (match result with
     | .err (.abort .timeoutError) => False
     | .err (.abort (.ffiError event)) => outcome = HolOutcome.ffiOutcome event
     | _ => outcome = HolOutcome.success) ∧
    behavior = HolBehaviour.terminate outcome state.ffi.ioEvents

/-- Observable closure behavior derived from the current proof-side
evaluator. It remains untagged pending review of that evaluator and its
carriers against the original semantics. -/
noncomputable def semantics {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (program : List ClosLang.Exp) : HolBehaviour :=
  open Classical in
  if ∃ clock, (evaluate program [] (initialState ffi maxApp code oracle compiler clock)).1 = .err (.abort .typeError)
  then .fail
  else
    match holOptionSome (terminatingObservation ffi maxApp code oracle compiler program) with
    | some behavior => behavior
    | none => .diverge (HolLList.buildLprefixLub (fun trace => ∃ clock,
        trace = HolLList.fromList (evaluate program [] (initialState ffi maxApp code oracle compiler clock)).2.ffi.ioEvents))

/-- Equal result and FFI observations at every clock give equal factored
semantics. This is Flapjack-specific congruence for the proof-side evaluator. -/
theorem semantics_eq_of_same_observations {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (sourceOracle targetOracle : CompileOracle C)
    (sourceCompiler targetCompiler : Compiler C) (program : List ClosLang.Exp)
    (same : ∀ clock,
      (evaluate program [] (initialState ffi maxApp code sourceOracle sourceCompiler clock)).1 =
        (evaluate program [] (initialState ffi maxApp code targetOracle targetCompiler clock)).1 ∧
      (evaluate program [] (initialState ffi maxApp code sourceOracle sourceCompiler clock)).2.ffi =
        (evaluate program [] (initialState ffi maxApp code targetOracle targetCompiler clock)).2.ffi) :
    semantics ffi maxApp code sourceOracle sourceCompiler program =
      semantics ffi maxApp code targetOracle targetCompiler program := by
  classical
  have failureEq : (∃ clock, (evaluate program [] (initialState ffi maxApp code sourceOracle sourceCompiler clock)).1 = .err (.abort .typeError)) ↔
      (∃ clock, (evaluate program [] (initialState ffi maxApp code targetOracle targetCompiler clock)).1 = .err (.abort .typeError)) := by
    constructor <;> rintro ⟨clock, h⟩ <;> refine ⟨clock, ?_⟩
    · exact (same clock).1.symm.trans h
    · exact (same clock).1.trans h
  have terminatingEq : terminatingObservation ffi maxApp code sourceOracle sourceCompiler program =
      terminatingObservation ffi maxApp code targetOracle targetCompiler program := by
    funext behavior
    unfold terminatingObservation
    apply propext
    constructor
    · rintro ⟨clock, result, state, outcome, run, outcomeEq, behaviorEq⟩
      have observed := same clock
      rw [run] at observed
      refine ⟨clock, result, (evaluate program [] (initialState ffi maxApp code targetOracle targetCompiler clock)).2, outcome, ?_, outcomeEq, ?_⟩
      · apply Prod.ext
        · exact observed.1.symm
        · rfl
      · simpa [← observed.2] using behaviorEq
    · rintro ⟨clock, result, state, outcome, run, outcomeEq, behaviorEq⟩
      have observed := same clock
      rw [run] at observed
      refine ⟨clock, result, (evaluate program [] (initialState ffi maxApp code sourceOracle sourceCompiler clock)).2, outcome, ?_, outcomeEq, ?_⟩
      · apply Prod.ext
        · exact observed.1
        · rfl
      · simpa [observed.2] using behaviorEq
  have tracesEq :
      (fun trace => ∃ clock, trace = HolLList.fromList (evaluate program [] (initialState ffi maxApp code sourceOracle sourceCompiler clock)).2.ffi.ioEvents) =
      (fun trace => ∃ clock, trace = HolLList.fromList (evaluate program [] (initialState ffi maxApp code targetOracle targetCompiler clock)).2.ffi.ioEvents) := by
    funext trace
    apply propext
    constructor <;> rintro ⟨clock, h⟩ <;> refine ⟨clock, ?_⟩
    · simpa [(same clock).2] using h
    · simpa [← (same clock).2] using h
  unfold semantics
  simp only [failureEq]
  rw [terminatingEq, tracesEq]

end Flapjack.Compiler.Backend.ClosSem
