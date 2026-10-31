import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL
import Flapjack.Misc.LprefixLub

/-! Whole-program observations of the BVL evaluator. -/
namespace Flapjack.Compiler.Backend.BvlSem
open Flapjack.SemanticPrimitivesHOL

/-- A terminating observation of an initial BVL call. This is auxiliary
infrastructure for the Flapjack whole-program semantics. -/
def terminatingObservation {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvl.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) (behavior : HolBehaviour) : Prop :=
  ∃ clock result state outcome,
    evaluateTuple ([.call 0 (some start) []], [], initialState ffi code oracle compiler clock) = (result, state) ∧
    (match result with
     | .err (.abort .timeoutError) => False
     | .err (.abort (.ffiError event)) => outcome = HolOutcome.ffiOutcome event
     | _ => outcome = HolOutcome.success) ∧
    behavior = HolBehaviour.terminate outcome state.ffi.ioEvents

/-- Observable behavior of an initial BVL program. This is untagged pending
representation review of the finite map in the internally used evaluator
state; the existing finite-map qualifier requires its owner in the signature. -/
noncomputable def semantics {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvl.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) : HolBehaviour :=
  open Classical in
  let run := fun clock => evaluateTuple ([.call 0 (some start) []], [],
    initialState ffi code oracle compiler clock)
  if ∃ clock, (run clock).1 = .err (.abort .typeError) then .fail
  else match holOptionSome (terminatingObservation ffi code oracle compiler start) with
  | some behavior => behavior
  | none => .diverge (HolLList.buildLprefixLub (fun trace => ∃ clock,
      trace = HolLList.fromList (run clock).2.ffi.ioEvents))

/-- A non-failing whole-program behavior excludes type errors at every clock. -/
theorem noTypeError_of_semantics_ne_fail {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvl.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat)
    (nonfail : semantics ffi code oracle compiler start ≠ .fail) :
    ∀ clock, (evaluateTuple ([.call 0 (some start) []], [],
      initialState ffi code oracle compiler clock)).1 ≠ .err (.abort .typeError) := by
  intro clock error
  apply nonfail
  simp [semantics, show ∃ k, (evaluateTuple ([.call 0 (some start) []], [],
    initialState ffi code oracle compiler k)).1 = .err (.abort .typeError) from ⟨clock, error⟩]

/-- If the whole-program semantics terminates, its result is one of the
initial evaluator's terminating observations. -/
theorem terminatingObservation_of_semantics_eq_terminate {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvl.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : semantics ffi code oracle compiler start = .terminate outcome events) :
    terminatingObservation ffi code oracle compiler start (.terminate outcome events) := by
  classical
  unfold semantics at terminates
  by_cases bad : ∃ clock, (evaluateTuple ([.call 0 (some start) []], [],
      initialState ffi code oracle compiler clock)).1 = .err (.abort .typeError)
  · simp [bad] at terminates
  · simp only [bad, if_false] at terminates
    cases selected : holOptionSome (terminatingObservation ffi code oracle compiler start) with
    | none => simp [selected] at terminates
    | some behavior =>
      have observed := holOptionSome_some selected
      simp only [selected] at terminates
      simpa [terminates] using observed

end Flapjack.Compiler.Backend.BvlSem
