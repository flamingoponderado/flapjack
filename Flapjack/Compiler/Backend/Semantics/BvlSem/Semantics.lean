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
    refine ⟨noTypeError_of_semantics_ne_fail ffi code oracle compiler start nonfail, ?_⟩
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
    cases selected : holOptionSome (terminatingObservation ffi code oracle compiler start) with
    | none => exact (holOptionSome_none selected _ observed).elim
    | some behavior =>
      have chosen := holOptionSome_some selected
      have same := terminatingObservation_unique ffi code oracle compiler start behavior
        (.terminate outcome events) chosen observed
      simpa only [selected] using same

/-- A divergent whole-program behavior excludes terminating observations. -/
theorem no_terminatingObservation_of_semantics_eq_diverge {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvl.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) (trace : HolLList HolIoEvent)
    (diverges : semantics ffi code oracle compiler start = .diverge trace) :
    ∀ behavior, ¬ terminatingObservation ffi code oracle compiler start behavior := by
  classical
  unfold semantics at diverges
  by_cases bad : ∃ clock, (evaluateTuple ([.call 0 (some start) []], [],
      initialState ffi code oracle compiler clock)).1 = .err (.abort .typeError)
  · simp [bad] at diverges
  · simp only [bad, if_false] at diverges
    cases selected : holOptionSome (terminatingObservation ffi code oracle compiler start) with
    | none => exact holOptionSome_none selected
    | some behavior =>
      have observed := holOptionSome_some selected
      obtain ⟨_, _, _, outcome, _, _, rfl⟩ := observed
      simp [selected] at diverges

end Flapjack.Compiler.Backend.BvlSem
