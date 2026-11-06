import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import Flapjack.Misc.LprefixLub

/-! Observations of the clocked closure evaluator. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

private def maptoBroadlookup (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : Nat → Option (Nat × ClosLang.Exp) :=
  code.lookup
private def mapofBroad (lookup : Nat → Option (Nat × ClosLang.Exp))
    (support : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact Nat (Nat × ClosLang.Exp) := ⟨lookup, support⟩

/-- The supplied code map has the canonical lookup/support roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_semantics_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    mapofBroad (maptoBroadlookup code) code.finiteSupport = code := by cases code; rfl

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

/-- Observable closure behavior derived from the clocked evaluator. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "semantics_def"
  (fmap_as_finite_support_parameters := [code])]
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

/-- Failure occurs exactly when some clocked evaluation reports a type error. -/
theorem semantics_ne_fail_iff {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (program : List ClosLang.Exp) :
    semantics ffi maxApp code oracle compiler program ≠ .fail ↔
      ∀ clock, (evaluate program [] (initialState ffi maxApp code oracle compiler clock)).1 ≠ .err (.abort .typeError) := by
  classical
  unfold semantics
  by_cases failure : ∃ clock, (evaluate program [] (initialState ffi maxApp code oracle compiler clock)).1 = .err (.abort .typeError)
  · simp [failure]
  · simp only [failure, if_false]
    constructor
    · intro _ clock h
      exact failure ⟨clock, h⟩
    · intro _
      cases chosen : holOptionSome (terminatingObservation ffi maxApp code oracle compiler program) with
      | none => simp
      | some behavior =>
        obtain ⟨_, _, _, _, _, _, shape⟩ := holOptionSome_some chosen
        simp [shape]

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
