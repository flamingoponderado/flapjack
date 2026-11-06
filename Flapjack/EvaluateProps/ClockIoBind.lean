import Flapjack.EvaluateProps.ClockIo

/-! Composition of the original clock-and-I/O invariant. -/
namespace Flapjack.EvaluateProps
open Flapjack.SemanticPrimitivesHOL

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_bind"]
theorem isClockIoMono_bind {σ α β γ δ : Type}
    (f : State σ → State σ × Result α β)
    (g : Result α β → State σ → State σ × Result γ δ) (s : State σ)
    (h : isClockIoMono f s ∧
      (∀ next result, f s = (next, result) → isClockIoMono (g result) next) ∧
      (∀ next, g (.err (.abort .timeoutError)) next = (next, .err (.abort .timeoutError)))) :
    isClockIoMono (fun st => let (next, result) := f st; g result next) s := by
  cases hfirst : f s with
  | mk middle firstResult =>
    cases hsecond : g firstResult middle with
    | mk final finalResult =>
      have firstInv := h.1
      have secondInv := h.2.1 middle firstResult hfirst
      simp only [isClockIoMono, hfirst] at firstInv
      simp only [isClockIoMono, hsecond] at secondInv
      rcases firstInv with ⟨firstTrace, firstClock, firstTypes, firstExns, firstRefs, firstCmp⟩
      rcases secondInv with ⟨secondTrace, secondClock, secondTypes, secondExns, secondRefs, secondCmp⟩
      simp only [isClockIoMono, hfirst, hsecond]
      refine ⟨ioEventsMonoHOL_trans _ _ _ ⟨firstTrace, secondTrace⟩,
        Nat.le_trans secondClock firstClock,
        Nat.le_trans firstTypes secondTypes, Nat.le_trans firstExns secondExns,
        Nat.le_trans firstRefs secondRefs, ?_⟩
      intro clock
      cases haltFirst : f { s with clock } with
      | mk altMiddle altFirst =>
        cases haltSecond : g altFirst altMiddle with
        | mk altFinal altResult =>
          simp only
          have firstComparison := firstCmp clock
          simp only [haltFirst] at firstComparison
          by_cases firstTimeout : firstResult = .err (.abort .timeoutError)
          · subst firstResult
            have originalTimeout := h.2.2 middle
            rw [hsecond] at originalTimeout
            cases originalTimeout
            by_cases low : clock ≤ s.clock
            · have altTimeout : altFirst = .err (.abort .timeoutError) := by
                by_contra nontimeout
                exact (firstComparison.2.2.1 nontimeout low) rfl
              have altRun := h.2.2 altMiddle
              rw [altTimeout] at haltSecond
              rw [haltSecond] at altRun
              cases altRun
              simpa using firstComparison.2.2.2
            · simp [low]
          · by_cases altTimeout : altFirst = .err (.abort .timeoutError)
            · have altRun := h.2.2 altMiddle
              rw [altTimeout] at haltSecond
              rw [haltSecond] at altRun
              cases altRun
              have lower : clock < s.clock - middle.clock := by
                have notGe : ¬ clock ≥ s.clock - middle.clock := by
                  intro ge
                  exact ((firstComparison.2.1 firstTimeout).mp ge) altTimeout
                omega
              have low : clock ≤ s.clock := by omega
              have threshold : ¬ clock ≥ s.clock - final.clock := by omega
              have traceRel := ioEventsMonoHOL_trans _ _ _ ⟨firstComparison.2.2.2 low, secondTrace⟩
              simp [threshold, traceRel]
            · have firstUsed : s.clock - middle.clock ≤ clock :=
                (firstComparison.2.1 firstTimeout).mpr altTimeout
              obtain ⟨firstEq, middleEq⟩ := firstComparison.1 altTimeout firstTimeout
              subst altFirst
              subst altMiddle
              let remaining := clock - (s.clock - middle.clock)
              have secondComparison := secondCmp remaining
              have adjustedEval : g firstResult { middle with clock := remaining } = (altFinal, altResult) := by
                simpa only [remaining] using haltSecond
              simp only [adjustedEval] at secondComparison
              have clockEq : remaining - (middle.clock - final.clock) = clock - (s.clock - final.clock) := by
                dsimp [remaining]
                omega
              have geEq : (remaining ≥ middle.clock - final.clock) ↔ (clock ≥ s.clock - final.clock) := by
                dsimp [remaining]
                omega
              have leEq : (remaining ≤ middle.clock) ↔ (clock ≤ s.clock) := by
                dsimp [remaining]
                omega
              simpa only [clockEq, geEq, leEq] using secondComparison

end Flapjack.EvaluateProps
