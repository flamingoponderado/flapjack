import Flapjack.SemanticsHOL
import Flapjack.EvaluateProps.ClockIoConsequences

/-! Clock-indexed source program trace properties. The source evaluator and
its carriers remain pending review. -/
namespace Flapjack.SemanticsProps
open Flapjack.SemanticsHOL Flapjack.EvaluateHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.EvaluateProps Flapjack.AstHOL

/-- Clock order gives a prefix of the program observations. This is a local
Lean helper derived from the declaration evaluator invariant. -/
theorem evaluateProgWithClock_prefix {σ : Type} (st : State σ) (env : SemEnv Value)
    (prog : List Dec) {k₁ k₂ : Nat} (h : k₁ ≤ k₂) :
    (evaluateProgWithClock st env k₁ prog).1.ioEvents <+:
      (evaluateProgWithClock st env k₂ prog).1.ioEvents := by
  simpa only [evaluateProgWithClock] using (evaluateDecs_ffiMonoClock k₁ k₂ st env prog h).1

@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "evaluate_prog_events_determ"]
theorem evaluateProg_eventsDeterm {σ : Type} (st : State σ) (env : SemEnv Value)
    (k : Nat) (prog : List Dec) (k' : Nat)
    (h : (evaluateProgWithClock st env k prog).1.ioEvents.length =
      (evaluateProgWithClock st env k' prog).1.ioEvents.length) :
    (evaluateProgWithClock st env k prog).1.ioEvents =
      (evaluateProgWithClock st env k' prog).1.ioEvents := by
  rcases Nat.le_total k k' with hk | hk
  · exact (evaluateProgWithClock_prefix st env prog hk).eq_of_length_le (Nat.le_of_eq h.symm)
  · exact ((evaluateProgWithClock_prefix st env prog hk).eq_of_length_le (Nat.le_of_eq h)).symm

@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "evaluate_prog_io_events_chain"]
theorem evaluateProg_ioEventsChain {σ : Type} (st : State σ) (env : SemEnv Value)
    (prog : List Dec) :
    HolLList.lprefixChain (fun events => ∃ k : Nat,
      HolLList.fromList (evaluateProgWithClock st env k prog).1.ioEvents = events) := by
  intro left right hl hr
  obtain ⟨k₁, rfl⟩ := hl
  obtain ⟨k₂, rfl⟩ := hr
  rcases Nat.le_total k₁ k₂ with hk | hk
  · exact Or.inl ((HolLList.lprefix_fromList _ _).mpr (evaluateProgWithClock_prefix st env prog hk))
  · exact Or.inr ((HolLList.lprefix_fromList _ _).mpr (evaluateProgWithClock_prefix st env prog hk))

@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "semantics_prog_total"]
theorem semanticsProg_total {σ : Type} (st : State σ) (env : SemEnv Value)
    (prog : List Dec) : ∃ behavior, semanticsProg st env prog behavior := by
  classical
  by_cases htype : ∃ k, (evaluateProgWithClock st env k prog).2 = .err (.abort .typeError)
  · exact ⟨.fail, htype⟩
  · by_cases hdone : ∃ k, (evaluateProgWithClock st env k prog).2 ≠ .err (.abort .timeoutError)
    · obtain ⟨k, hdone⟩ := hdone
      have hnotType : (evaluateProgWithClock st env k prog).2 ≠ .err (.abort .typeError) := by
        intro h
        exact htype ⟨k, h⟩
      generalize heq : evaluateProgWithClock st env k prog = pair at *
      rcases pair with ⟨ffi, result⟩
      cases result with
      | val value =>
          exact ⟨.terminate .success ffi.ioEvents, k, ffi, .val value, heq, ⟨hdone, rfl⟩, rfl, hnotType⟩
      | err error =>
          cases error with
          | raise value =>
              exact ⟨.terminate .success ffi.ioEvents, k, ffi, .err (.raise value), heq, ⟨hdone, rfl⟩, rfl, hnotType⟩
          | abort error =>
              cases error with
              | typeError => exact False.elim (hnotType rfl)
              | timeoutError => exact False.elim (hdone rfl)
              | ffiError event =>
                  exact ⟨.terminate (.ffiOutcome event) ffi.ioEvents, k, ffi, .err (.abort (.ffiError event)), heq, rfl, rfl, hnotType⟩
    · let traces := fun events => ∃ k : Nat,
          HolLList.fromList (evaluateProgWithClock st env k prog).1.ioEvents = events
      refine ⟨.diverge (HolLList.buildLprefixLub traces), ?_,
        HolLList.buildLprefixLub_thm (evaluateProg_ioEventsChain st env prog)⟩
      intro k
      have h : (evaluateProgWithClock st env k prog).2 = .err (.abort .timeoutError) := by
        by_contra hn
        exact hdone ⟨k, hn⟩
      refine ⟨(evaluateProgWithClock st env k prog).1, ?_⟩
      calc
        evaluateProgWithClock st env k prog =
            ((evaluateProgWithClock st env k prog).1, (evaluateProgWithClock st env k prog).2) := (Prod.eta _).symm
        _ = _ := congrArg (fun x => ((evaluateProgWithClock st env k prog).1, x)) h

end Flapjack.SemanticsProps
