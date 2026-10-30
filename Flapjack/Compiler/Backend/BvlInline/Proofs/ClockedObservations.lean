import Flapjack.Compiler.Backend.Semantics.ClosSem.SemanticsSimulation

/-! Generic clocked-observation infrastructure for BVL pass correctness.
These declarations do not port standalone HOL declarations. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.SemanticPrimitivesHOL

/-- A clocked result and its observable event list. -/
abbrev ClockObservation (A V : Type) := Result A V × List HolIoEvent

/-- One terminating behavior represented by a family of clocked observations. -/
def clockTerminating {A V : Type} (observation : Nat → ClockObservation A V)
    (behavior : HolBehaviour) : Prop :=
  ∃ clock result outcome,
    (observation clock).1 = result ∧
    (match result with
     | .err (.abort .timeoutError) => False
     | .err (.abort (.ffiError event)) => outcome = HolOutcome.ffiOutcome event
     | _ => outcome = HolOutcome.success) ∧
    behavior = HolBehaviour.terminate outcome (observation clock).2

/-- The original fail/terminate/diverge choice factored over clocked result
and event observations. -/
noncomputable def clockSemantics {A V : Type} (observation : Nat → ClockObservation A V) : HolBehaviour :=
  open Classical in
  if ∃ clock, (observation clock).1 = .err (.abort .typeError) then .fail
  else match holOptionSome (clockTerminating observation) with
  | some behavior => behavior
  | none => .diverge (HolLList.buildLprefixLub (fun trace => ∃ clock,
      trace = HolLList.fromList (observation clock).2))

/-- Non-timeout observations remain unchanged as the clock increases. -/
def clockStable {A V : Type} (observation : Nat → ClockObservation A V) : Prop :=
  ∀ clock extra, (observation clock).1 ≠ .err (.abort .timeoutError) →
    observation (clock + extra) = observation clock

/-- Every finite trace is a prefix of the trace at a larger clock. -/
def clockMonotone {A V : Type} (observation : Nat → ClockObservation A V) : Prop :=
  ∀ clock later, clock ≤ later → (observation clock).2 <+: (observation later).2

/-- A forward clock extension simulation preserves type-error existence. -/
theorem clockFailure_iff {A V : Type} (source target : Nat → ClockObservation A V)
    (targetStable : clockStable target)
    (simulation : ∀ clock, ∃ extra, source clock = target (clock + extra)) :
    (∃ clock, (source clock).1 = .err (.abort .typeError)) ↔
      ∃ clock, (target clock).1 = .err (.abort .typeError) := by
  constructor
  · rintro ⟨clock, fail⟩
    obtain ⟨extra, equal⟩ := simulation clock
    exact ⟨clock + extra, by simpa [equal] using fail⟩
  · rintro ⟨clock, fail⟩
    obtain ⟨extra, equal⟩ := simulation clock
    have notTimeout : (target clock).1 ≠ .err (.abort .timeoutError) := by rw [fail]; simp
    have stable := targetStable clock extra notTimeout
    exact ⟨clock, by rw [equal, stable]; exact fail⟩

/-- The forward simulation and target stability characterize the same
terminating observations, without a source-safety hypothesis. -/
theorem clockTerminating_eq {A V : Type} (source target : Nat → ClockObservation A V)
    (targetStable : clockStable target)
    (simulation : ∀ clock, ∃ extra, source clock = target (clock + extra)) :
    clockTerminating source = clockTerminating target := by
  funext behavior
  apply propext
  constructor
  · rintro ⟨clock, result, outcome, resultEq, outcomeEq, behaviorEq⟩
    obtain ⟨extra, equal⟩ := simulation clock
    refine ⟨clock + extra, result, outcome, ?_, outcomeEq, ?_⟩
    · simpa [equal] using resultEq
    · simpa [equal] using behaviorEq
  · rintro ⟨clock, result, outcome, resultEq, outcomeEq, behaviorEq⟩
    have notTimeout : (target clock).1 ≠ .err (.abort .timeoutError) := by
      rw [resultEq]
      intro bad
      rw [bad] at outcomeEq
      exact outcomeEq
    obtain ⟨extra, equal⟩ := simulation clock
    have stable := targetStable clock extra notTimeout
    refine ⟨clock, result, outcome, ?_, outcomeEq, ?_⟩
    · simpa [equal, stable] using resultEq
    · simpa [equal, stable] using behaviorEq

/-- A forward clock-extension simulation preserves all observations when
both trace families are monotone and target non-timeout results are stable. -/
theorem clockSemantics_eq {A V : Type} (source target : Nat → ClockObservation A V)
    (targetStable : clockStable target) (sourceMono : clockMonotone source)
    (targetMono : clockMonotone target)
    (simulation : ∀ clock, ∃ extra, source clock = target (clock + extra)) :
    clockSemantics source = clockSemantics target := by
  classical
  have failures := clockFailure_iff source target targetStable simulation
  have terminations := clockTerminating_eq source target targetStable simulation
  have traces :
      HolLList.buildLprefixLub (fun trace => ∃ clock, trace = HolLList.fromList (source clock).2) =
      HolLList.buildLprefixLub (fun trace => ∃ clock, trace = HolLList.fromList (target clock).2) := by
    apply ClosSem.clocked_traces_lub_eq _ _ sourceMono targetMono
    intro clock
    obtain ⟨extra, equal⟩ := simulation clock
    exact ⟨extra, congrArg Prod.snd equal⟩
  unfold clockSemantics
  simp only [failures]
  rw [terminations, traces]

end Flapjack.Compiler.Backend.BvlInline.Proofs
