module

public import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL
public import Flapjack.Misc.LprefixLub
public import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateClockShift

@[expose] public section

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

/-- A terminating BVL program has at most one observable behavior.
This Flapjack-specific fact justifies the choice in the source-shaped semantics:
clock extension makes every pair of non-timeout observations agree. -/
theorem terminatingObservation_unique {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvl.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) (first second : HolBehaviour)
    (firstRun : terminatingObservation ffi code oracle compiler start first)
    (secondRun : terminatingObservation ffi code oracle compiler start second) : first = second := by
  obtain ⟨k₁, r₁, s₁, out₁, run₁, outcome₁, rfl⟩ := firstRun
  obtain ⟨k₂, r₂, s₂, out₂, run₂, outcome₂, rfl⟩ := secondRun
  have safe₁ : r₁ ≠ .err (.abort .timeoutError) := by
    intro h
    rw [h] at outcome₁
    exact outcome₁
  have safe₂ : r₂ ≠ .err (.abort .timeoutError) := by
    intro h
    rw [h] at outcome₂
    exact outcome₂
  have shift₁ := BvlProps.evaluateAddClockInitialState [.call 0 (some start) []] [] ffi code oracle compiler
    k₁ r₁ s₁ ⟨run₁, safe₁⟩ k₂
  have shift₂ := BvlProps.evaluateAddClockInitialState [.call 0 (some start) []] [] ffi code oracle compiler
    k₂ r₂ s₂ ⟨run₂, safe₂⟩ k₁
  rw [Nat.add_comm k₂ k₁] at shift₂
  have same := shift₁.symm.trans shift₂
  have resultEq : r₁ = r₂ := congrArg Prod.fst same
  have eventsEq : s₁.ffi.ioEvents = s₂.ffi.ioEvents := by
    simpa using congrArg (fun output => output.2.ffi.ioEvents) same
  subst r₂
  have outcomeEq : out₁ = out₂ := by
    cases r₁ with
    | val values => simp_all
    | err error =>
      cases error with
      | raise value => simp_all
      | abort abort => cases abort <;> simp_all
  rw [outcomeEq, eventsEq]

/-- Observable behavior of an initial BVL program. Its HOL cross-reference is
the source-shaped `semantics_def` equation below, which exposes the original
existential state and records the reference-map representation. -/
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

namespace SemanticsCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end SemanticsCarrier

open Classical in
/-- The complete source semantics equation, with its terminating state binder
shown explicitly. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "semantics_def"
  (fmap_as_finite_support := [refs])]
theorem semantics_def {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvl.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) :
    semantics ffi code oracle compiler start =
      if ∃ clock, (evaluateTuple ([.call 0 (some start) []], [],
          initialState ffi code oracle compiler clock)).1 = .err (.abort .typeError) then .fail
      else match holOptionSome (fun behavior =>
        ∃ clock, ∃ state : Flapjack.Compiler.Backend.BvlSem.State C F, ∃ result outcome,
          evaluateTuple ([.call 0 (some start) []], [], initialState ffi code oracle compiler clock) =
            (result, state) ∧
          (match result with
           | .err (.abort .timeoutError) => False
           | .err (.abort (.ffiError event)) => outcome = HolOutcome.ffiOutcome event
           | _ => outcome = HolOutcome.success) ∧
          behavior = HolBehaviour.terminate outcome state.ffi.ioEvents) with
      | some behavior => behavior
      | none => .diverge (HolLList.buildLprefixLub (fun trace => ∃ clock,
          trace = HolLList.fromList (evaluateTuple ([.call 0 (some start) []], [],
            initialState ffi code oracle compiler clock)).2.ffi.ioEvents)) := by
  have terminating : terminatingObservation ffi code oracle compiler start =
      (fun behavior => ∃ clock, ∃ state : Flapjack.Compiler.Backend.BvlSem.State C F, ∃ result outcome,
        evaluateTuple ([.call 0 (some start) []], [], initialState ffi code oracle compiler clock) =
          (result, state) ∧
        (match result with
         | .err (.abort .timeoutError) => False
         | .err (.abort (.ffiError event)) => outcome = HolOutcome.ffiOutcome event
         | _ => outcome = HolOutcome.success) ∧
        behavior = HolBehaviour.terminate outcome state.ffi.ioEvents) := by
    funext behavior
    apply propext
    constructor
    · rintro ⟨clock, result, state, outcome, run, ending, rfl⟩
      exact ⟨clock, state, result, outcome, run, ending, rfl⟩
    · rintro ⟨clock, state, result, outcome, run, ending, rfl⟩
      exact ⟨clock, result, state, outcome, run, ending, rfl⟩
  unfold semantics
  rw [terminating]
  rfl

/-- Whole-program behavior is non-failing exactly when no initial call has a
type error. This Flapjack-specific characterization covers every source
semantics branch and introduces no semantic assumption. -/
theorem semantics_ne_fail_iff {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvl.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) :
    semantics ffi code oracle compiler start ≠ .fail ↔
      ∀ clock, (evaluateTuple ([.call 0 (some start) []], [],
        initialState ffi code oracle compiler clock)).1 ≠ .err (.abort .typeError) := by
  classical
  constructor
  · intro nonfail clock error
    apply nonfail
    simp [semantics, show ∃ k, (evaluateTuple ([.call 0 (some start) []], [],
      initialState ffi code oracle compiler k)).1 = .err (.abort .typeError) from ⟨clock, error⟩]
  · intro safe
    unfold semantics
    have noBad : ¬ ∃ clock, (evaluateTuple ([.call 0 (some start) []], [],
        initialState ffi code oracle compiler clock)).1 = .err (.abort .typeError) := by
      intro h
      obtain ⟨clock, bad⟩ := h
      exact safe clock bad
    simp only [noBad, if_false]
    cases selected : holOptionSome (terminatingObservation ffi code oracle compiler start) with
    | none => simp
    | some behavior =>
      have observed := holOptionSome_some selected
      obtain ⟨_, _, _, outcome, _, _, rfl⟩ := observed
      simp

/-- Termination is characterized by the absence of type errors at every clock
and the unique terminating observation. This Flapjack-specific equivalence
makes the source semantics' guarded choice independent of its selected witness. -/
theorem semantics_eq_terminate_iff {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvl.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) (outcome : HolOutcome) (events : List HolIoEvent) :
    semantics ffi code oracle compiler start = .terminate outcome events ↔
      (∀ clock, (evaluateTuple ([.call 0 (some start) []], [],
        initialState ffi code oracle compiler clock)).1 ≠ .err (.abort .typeError)) ∧
      terminatingObservation ffi code oracle compiler start (.terminate outcome events) := by
  constructor
  · intro terminates
    have nonfail : semantics ffi code oracle compiler start ≠ .fail := by
      rw [terminates]
      simp
    refine ⟨(semantics_ne_fail_iff ffi code oracle compiler start).1 nonfail, ?_⟩
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
  · rintro ⟨safe, observed⟩
    classical
    unfold semantics
    have noBad : ¬ ∃ clock, (evaluateTuple ([.call 0 (some start) []], [],
        initialState ffi code oracle compiler clock)).1 = .err (.abort .typeError) := by
      intro h
      obtain ⟨clock, bad⟩ := h
      exact safe clock bad
    simp only [noBad, if_false]
    have selected := (holOptionSome_eq_some_iff
      (terminatingObservation ffi code oracle compiler start)
      (terminatingObservation_unique ffi code oracle compiler start)
      (.terminate outcome events)).2 observed
    simp only [selected]

/-- Divergence is characterized by the absence of type errors and terminating
observations, together with the full least upper bound of event traces. This
Flapjack-specific equivalence exposes every branch of the source-shaped semantics. -/
theorem semantics_eq_diverge_iff {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvl.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) (trace : HolLList HolIoEvent) :
    semantics ffi code oracle compiler start = .diverge trace ↔
      (∀ clock, (evaluateTuple ([.call 0 (some start) []], [],
        initialState ffi code oracle compiler clock)).1 ≠ .err (.abort .typeError)) ∧
      (∀ behavior, ¬ terminatingObservation ffi code oracle compiler start behavior) ∧
      trace = HolLList.buildLprefixLub (fun tr => ∃ clock, tr = HolLList.fromList
        (evaluateTuple ([.call 0 (some start) []], [],
          initialState ffi code oracle compiler clock)).2.ffi.ioEvents) := by
  classical
  constructor
  · intro diverges
    have nonfail : semantics ffi code oracle compiler start ≠ .fail := by
      rw [diverges]
      simp
    have safe := (semantics_ne_fail_iff ffi code oracle compiler start).1 nonfail
    refine ⟨safe, ?_⟩
    unfold semantics at diverges
    have noBad : ¬ ∃ clock, (evaluateTuple ([.call 0 (some start) []], [],
        initialState ffi code oracle compiler clock)).1 = .err (.abort .typeError) := by
      intro h
      obtain ⟨clock, bad⟩ := h
      exact safe clock bad
    simp only [noBad, if_false] at diverges
    cases selected : holOptionSome (terminatingObservation ffi code oracle compiler start) with
    | none =>
      refine ⟨holOptionSome_none selected, ?_⟩
      simpa only [selected, HolBehaviour.diverge.injEq] using diverges.symm
    | some behavior =>
      have observed := holOptionSome_some selected
      obtain ⟨_, _, _, outcome, _, _, rfl⟩ := observed
      simp [selected] at diverges
  · rintro ⟨safe, noTermination, rfl⟩
    unfold semantics
    have noBad : ¬ ∃ clock, (evaluateTuple ([.call 0 (some start) []], [],
        initialState ffi code oracle compiler clock)).1 = .err (.abort .typeError) := by
      intro h
      obtain ⟨clock, bad⟩ := h
      exact safe clock bad
    have noChoice : holOptionSome (terminatingObservation ffi code oracle compiler start) = none := by
      unfold holOptionSome
      simp [not_exists.mpr noTermination]
    simp [noBad, noChoice]

end Flapjack.Compiler.Backend.BvlSem
