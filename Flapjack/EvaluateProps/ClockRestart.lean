module

public import Flapjack.EvaluateProps.ClockIoFull
public import Flapjack.EvaluateProps.ClockIoConsequences

@[expose] public section

/-! Re-running a clock-monotone computation with a different starting clock. -/
namespace Flapjack.EvaluateProps
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.EvaluateHOL

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_set_clock"]
theorem isClockIoMono_setClock {σ α β : Type} (f : State σ → State σ × Result α β)
    (st next : State σ) (result : Result α β) (clock : Nat)
    (mono : isClockIoMono f st) (run : f st = (next, result))
    (hne : result ≠ .err (.abort .timeoutError)) :
    ∃ clock0, f { st with clock := clock0 } = ({ next with clock := clock }, result) := by
  simp only [isClockIoMono, run] at mono
  rcases mono with ⟨_, _, _, _, _, comparisons⟩
  refine ⟨clock + (st.clock - next.clock), ?_⟩
  specialize comparisons (clock + (st.clock - next.clock))
  cases heval : f { st with clock := clock + (st.clock - next.clock) } with
  | mk other otherResult =>
    simp only [heval] at comparisons
    have otherNotTimeout : otherResult ≠ .err (.abort .timeoutError) :=
      (comparisons.2.1 hne).mp (by omega)
    obtain ⟨resultEq, stateEq⟩ := comparisons.1 otherNotTimeout hne
    have clockEq : clock + (st.clock - next.clock) - (st.clock - next.clock) = clock := by
      omega
    rw [resultEq, stateEq, clockEq]

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_set_clock"]
theorem evaluate_setClock {σ : Type} (st next : State σ) (env : SemEnv Value)
    (es : List AstHOL.Exp) (result : Result (List Value) Value)
    (run : evaluate st env es = (next, result))
    (hne : result ≠ .err (.abort .timeoutError)) (clock : Nat) :
    ∃ clock0, evaluate { st with clock := clock0 } env es =
      ({ next with clock := clock }, result) :=
  isClockIoMono_setClock (fun state => evaluate state env es) st next result clock
    (isClockIoMono_evaluate.1 st env es) run hne

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_decs_set_clock"]
theorem evaluateDecs_setClock {σ : Type} (st next : State σ) (env : SemEnv Value)
    (decs : List Dec) (result : Result (SemEnv Value) Value)
    (run : evaluateDecs st env decs = (next, result))
    (hne : result ≠ .err (.abort .timeoutError)) (clock : Nat) :
    ∃ clock0, evaluateDecs { st with clock := clock0 } env decs =
      ({ next with clock := clock }, result) :=
  isClockIoMono_setClock (fun state => evaluateDecs state env decs) st next result clock
    (isClockIoMono_evaluate.2.2 st env decs) run hne

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_minimal"]
theorem isClockIoMono_minimal {σ α β : Type} (f : State σ → State σ × Result α β)
    (st next : State σ) (result : Result α β) (k : Nat)
    (mono : isClockIoMono f st) (run : f st = (next, result))
    (hclock : next.clock = 0) (hne : result ≠ .err (.abort .timeoutError))
    (hgt : st.clock > k) :
    ∃ next', f { st with clock := k } = (next', .err (.abort .timeoutError)) ∧
      ioEventsMonoHOL next'.ffi next.ffi := by
  simp only [isClockIoMono, run] at mono
  rcases mono with ⟨_, _, _, _, _, comparisons⟩
  specialize comparisons k
  cases heval : f { st with clock := k } with
  | mk other otherResult =>
    simp only [heval] at comparisons
    have notTimeout : ¬ otherResult ≠ .err (.abort .timeoutError) := by
      intro hother
      have bound := (comparisons.2.1 hne).mpr hother
      omega
    have timeoutEq : otherResult = .err (.abort .timeoutError) :=
      Classical.byContradiction notTimeout
    refine ⟨other, ?_, comparisons.2.2.2 (by omega)⟩
    rw [timeoutEq]

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_minimal_clock"]
theorem evaluate_minimalClock {σ : Type} (st next : State σ) (env : SemEnv Value)
    (es : List AstHOL.Exp) (result : Result (List Value) Value) (k : Nat)
    (run : evaluate st env es = (next, result)) (hclock : next.clock = 0)
    (hne : result ≠ .err (.abort .timeoutError)) (hgt : st.clock > k) :
    ∃ next', evaluate { st with clock := k } env es = (next', .err (.abort .timeoutError)) ∧
      ioEventsMonoHOL next'.ffi next.ffi :=
  isClockIoMono_minimal (fun state => evaluate state env es) st next result k
    (isClockIoMono_evaluate.1 st env es) run hclock hne hgt

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_match_minimal_clock"]
theorem evaluateMatch_minimalClock {σ : Type} (st next : State σ) (env : SemEnv Value)
    (value : Value) (clauses : List (Pat × AstHOL.Exp)) (errorValue : Value)
    (result : Result (List Value) Value) (k : Nat)
    (run : evaluateMatch st env value clauses errorValue = (next, result))
    (hclock : next.clock = 0) (hne : result ≠ .err (.abort .timeoutError))
    (hgt : st.clock > k) :
    ∃ next', evaluateMatch { st with clock := k } env value clauses errorValue =
        (next', .err (.abort .timeoutError)) ∧ ioEventsMonoHOL next'.ffi next.ffi :=
  isClockIoMono_minimal (fun state => evaluateMatch state env value clauses errorValue)
    st next result k (isClockIoMono_evaluate.2.1 st env value clauses errorValue)
    run hclock hne hgt

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "evaluate_set_init_clock"]
theorem evaluate_setInitClock {σ : Type} (st next : State σ) (env : SemEnv Value)
    (es : List AstHOL.Exp) (result : Result (List Value) Value)
    (run : evaluate st env es = (next, result))
    (hne : result ≠ .err (.abort .timeoutError)) (k : Nat) :
    ∃ clock' res' state', evaluate { st with clock := k } env es = (state', res') ∧
      ((res' = result ∧ state' = { next with clock := clock' }) ∨
       (res' = .err (.abort .timeoutError) ∧ ioEventsMonoHOL state'.ffi next.ffi)) := by
  obtain ⟨clock0, run0⟩ := evaluate_setClock st next env es result run hne 0
  by_cases hle : clock0 ≤ k
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
    have addRun := evaluate_addToClock { st with clock := clock0 } env es { next with clock := 0 }
      result extra ⟨run0, hne⟩
    refine ⟨extra, result, { next with clock := extra }, ?_, Or.inl ⟨rfl, rfl⟩⟩
    simpa using addRun
  · have hgt : clock0 > k := Nat.lt_of_not_le hle
    obtain ⟨state', run', mono⟩ := evaluate_minimalClock { st with clock := clock0 }
      { next with clock := 0 } env es result k run0 rfl hne hgt
    exact ⟨0, .err (.abort .timeoutError), state', run', Or.inr ⟨rfl, mono⟩⟩

end Flapjack.EvaluateProps
