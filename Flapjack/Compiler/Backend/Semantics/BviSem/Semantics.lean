import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateList
import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateClockShift
import Flapjack.Misc.LprefixLub

/-! Whole-program observations of the BVI evaluator. -/
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.SemanticPrimitivesHOL

/-- A terminating observation of an initial BVI call. This is auxiliary
infrastructure for the Flapjack whole-program semantics. -/
def terminatingObservation {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvi.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) (behavior : HolBehaviour) : Prop :=
  ∃ clock result state outcome,
    evaluateTuple ([.call 0 (some start) [] none], [],
      initialState ffi code oracle compiler clock) = (result, state) ∧
    (match result with
     | .err (.abort (.ffiError event)) => outcome = HolOutcome.ffiOutcome event
     | .val _ => outcome = HolOutcome.success
     | _ => False) ∧
    behavior = HolBehaviour.terminate outcome state.ffi.ioEvents

/-- Observable behavior of an initial BVI program. This remains untagged
until the evaluator and its internally used finite-map state representation
have been reviewed against the source semantics. -/
noncomputable def semantics {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvi.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) : HolBehaviour :=
  open Classical in
  let run := fun clock => evaluateTuple ([.call 0 (some start) [] none], [],
    initialState ffi code oracle compiler clock)
  if ∃ clock error, (run clock).1 = .err error ∧
      error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event) then .fail
  else match holOptionSome (terminatingObservation ffi code oracle compiler start) with
  | some behavior => behavior
  | none => .diverge (HolLList.buildLprefixLub (fun trace => ∃ clock,
      trace = HolLList.fromList (run clock).2.ffi.ioEvents))

/-- Two terminating observations of the same initial program have the same
outcome and trace. A non-timeout run is stable when its clock is extended. -/
theorem terminatingObservation_unique {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvi.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) (first second : HolBehaviour)
    (hfirst : terminatingObservation ffi code oracle compiler start first)
    (hsecond : terminatingObservation ffi code oracle compiler start second) :
    first = second := by
  obtain ⟨clock1, result1, state1, outcome1, run1, outcomeRun1, rfl⟩ := hfirst
  obtain ⟨clock2, result2, state2, outcome2, run2, outcomeRun2, rfl⟩ := hsecond
  have notTimeout1 : result1 ≠ .err (.abort .timeoutError) := by
    intro h; subst result1; simp at outcomeRun1
  have notTimeout2 : result2 ≠ .err (.abort .timeoutError) := by
    intro h; subst result2; simp at outcomeRun2
  have extended1 := BviProps.evaluate_addClock [.call 0 (some start) [] none] []
    (initialState ffi code oracle compiler clock1) state1 result1 clock2 run1 notTimeout1
  have extended2 := BviProps.evaluate_addClock [.call 0 (some start) [] none] []
    (initialState ffi code oracle compiler clock2) state2 result2 clock1 run2 notTimeout2
  have same : (result1, { state1 with clock := state1.clock + clock2 }) =
      (result2, { state2 with clock := state2.clock + clock1 }) := by
    exact extended1.symm.trans (by simpa [initialState, Nat.add_comm] using extended2)
  have resultEq : result1 = result2 := congrArg Prod.fst same
  have eventsEq : state1.ffi.ioEvents = state2.ffi.ioEvents :=
    congrArg (fun p => p.2.ffi.ioEvents) same
  subst result2
  have outcomeEq : outcome1 = outcome2 := by
    cases result1 with
    | val values => simpa using outcomeRun1.trans outcomeRun2.symm
    | err error =>
      cases error with
      | raise value => simp at outcomeRun1
      | abort reason =>
        cases reason with
        | typeError => simp at outcomeRun1
        | timeoutError => simp at outcomeRun1
        | ffiError event => simpa using outcomeRun1.trans outcomeRun2.symm
  simp [outcomeEq, eventsEq]

/-- If no initial clock fails, a terminating observation determines the
whole-program semantics. -/
theorem semantics_eq_of_terminatingObservation {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvi.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) (behavior : HolBehaviour)
    (noFatal : ¬ ∃ clock error, (evaluateTuple ([.call 0 (some start) [] none], [],
      initialState ffi code oracle compiler clock)).1 = .err error ∧
      error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event))
    (observed : terminatingObservation ffi code oracle compiler start behavior) :
    semantics ffi code oracle compiler start = behavior := by
  classical
  unfold semantics
  simp only [noFatal, if_false]
  rw [HolLList.holOptionSome_eq_some observed
    (fun other otherObserved => terminatingObservation_unique ffi code oracle compiler start
      other behavior otherObserved observed)]

/-- With no fatal result or terminating observation, the whole program
diverges with the least upper bound of its finite-clock traces. -/
theorem semantics_diverges_of_no_observation {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvi.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat)
    (noFatal : ¬ ∃ clock error, (evaluateTuple ([.call 0 (some start) [] none], [],
      initialState ffi code oracle compiler clock)).1 = .err error ∧
      error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event))
    (noObservation : ∀ behavior, ¬ terminatingObservation ffi code oracle compiler start behavior) :
    ∃ trace, semantics ffi code oracle compiler start = .diverge trace := by
  classical
  unfold semantics
  simp only [noFatal, if_false]
  have selected : holOptionSome (terminatingObservation ffi code oracle compiler start) = none := by
    unfold holOptionSome
    simp [not_exists.mpr noObservation]
  simp [selected]

/-- In the absence of a fatal initial result, the observable behavior is
either a terminating observation or a divergent trace. -/
theorem semantics_ne_fail_of_noFatalError {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvi.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat)
    (noFatal : ¬ ∃ clock error, (evaluateTuple ([.call 0 (some start) [] none], [],
      initialState ffi code oracle compiler clock)).1 = .err error ∧
      error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event)) :
    semantics ffi code oracle compiler start ≠ .fail := by
  classical
  unfold semantics
  simp only [noFatal, if_false]
  cases selected : holOptionSome (terminatingObservation ffi code oracle compiler start) with
  | none => simp
  | some behavior =>
    have observed := holOptionSome_some selected
    obtain ⟨_, _, _, outcome, _, _, rfl⟩ := observed
    simp

end Flapjack.Compiler.Backend.BviSem
