import Flapjack.EvaluateProps.EvaluateFfiFull

/-! Original combined clock, state-growth and FFI-trace invariant. The main
mutual evaluator proof and its bind/check closure lemmas remain open. The
source evaluator and its carriers remain pending review. -/
namespace Flapjack.EvaluateProps
open Flapjack.SemanticPrimitivesHOL

/-- The source invariant compares every clock, preserving non-timeout results,
clock consumption, monotonic state fields and ordered FFI event histories. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_def"]
def isClockIoMono {σ α β : Type} (f : State σ → State σ × Result α β) (s : State σ) : Prop :=
  let (next, result) := f s
  ioEventsMonoHOL s.ffi next.ffi ∧
  next.clock ≤ s.clock ∧
  s.nextTypeStamp ≤ next.nextTypeStamp ∧
  s.nextExnStamp ≤ next.nextExnStamp ∧
  s.refs.length ≤ next.refs.length ∧
  ∀ clock,
    let (other, otherResult) := f { s with clock }
    (otherResult ≠ .err (.abort .timeoutError) →
      result ≠ .err (.abort .timeoutError) →
      otherResult = result ∧ other = { next with clock := clock - (s.clock - next.clock) }) ∧
    (result ≠ .err (.abort .timeoutError) →
      (clock ≥ s.clock - next.clock ↔ otherResult ≠ .err (.abort .timeoutError))) ∧
    (otherResult ≠ .err (.abort .timeoutError) → clock ≤ s.clock →
      result ≠ .err (.abort .timeoutError)) ∧
    (clock ≤ s.clock → ioEventsMonoHOL other.ffi next.ffi)

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_return"]
theorem isClockIoMono_return {σ α β : Type} (s : State σ) (value : α) :
    isClockIoMono (fun st => (st, Result.val (β := β) value)) s := by
  simp [isClockIoMono, ioEventsMonoHOL]

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_err"]
theorem isClockIoMono_err {σ α β : Type} (s : State σ) (error : ErrorResult β) :
    isClockIoMono (fun st => (st, Result.err (α := α) error)) s := by
  simp [isClockIoMono, ioEventsMonoHOL]
  intros
  assumption

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "adj_clock_def"]
def adjClock {σ : Type} (inc dec : Nat) (s : State σ) : State σ :=
  { s with clock := s.clock + inc - dec }

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "dec_inc_clock"]
theorem decIncClock {σ : Type} (s : State σ) : EvaluateHOL.decClock (adjClock 1 0 s) = s := by
  cases s
  simp [adjClock, EvaluateHOL.decClock]

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_extra"]
theorem isClockIoMono_extra {σ α β : Type} (f : State σ → State σ × Result α β)
    (mono : ∀ s, isClockIoMono f s) (s next : State σ) (result : Result α β) (extra : Nat)
    (h : f s = (next, result) ∧ result ≠ .err (.abort .timeoutError)) :
    f { s with clock := s.clock + extra } = ({ next with clock := next.clock + extra }, result) := by
  obtain ⟨h, notTimeout⟩ := h
  have inv := mono s
  simp only [isClockIoMono, h] at inv
  rcases inv with ⟨_, bound, _, _, _, comparisons⟩
  specialize comparisons (s.clock + extra)
  cases heval : f { s with clock := s.clock + extra } with
  | mk other otherResult =>
    simp only [heval] at comparisons
    have otherNotTimeout : otherResult ≠ .err (.abort .timeoutError) :=
      (comparisons.2.1 notTimeout).mp (by omega)
    obtain ⟨resultEq, stateEq⟩ := comparisons.1 otherNotTimeout notTimeout
    have clockEq : s.clock + extra - (s.clock - next.clock) = next.clock + extra := by omega
    rw [resultEq, stateEq, clockEq]

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_extra_mono"]
theorem isClockIoMono_extra_mono {σ α β : Type} (f : State σ → State σ × Result α β)
    (mono : ∀ s, isClockIoMono f s) (s : State σ) (extra : Nat) :
    ioEventsMonoHOL (f s).1.ffi (f { s with clock := s.clock + extra }).1.ffi := by
  let raised := { s with clock := s.clock + extra }
  have inv := mono raised
  cases hlarge : f raised with
  | mk large largeResult =>
    simp only [isClockIoMono, hlarge] at inv
    rcases inv with ⟨_, _, _, _, _, comparisons⟩
    specialize comparisons s.clock
    have reset : { raised with clock := s.clock } = s := by
      cases s
      rfl
    simp only [reset] at comparisons
    have relation := comparisons.2.2.2 (by simp [raised])
    simpa only [hlarge] using relation

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_cong"]
theorem isClockIoMono_cong {σ α β : Type} (s t : State σ)
    (f g : State σ → State σ × Result α β) (eq : s = t)
    (same : ∀ state, state.evalState = t.evalState ∧ state.refs = t.refs ∧ state.ffi = t.ffi →
      f state = g state) : isClockIoMono f s ↔ isClockIoMono g t := by
  subst t
  have mainEq : f s = g s := same s ⟨rfl, rfl, rfl⟩
  have clockEq (clock : Nat) : f { s with clock } = g { s with clock } :=
    same { s with clock } ⟨rfl, rfl, rfl⟩
  simp only [isClockIoMono, mainEq, clockEq]

end Flapjack.EvaluateProps
