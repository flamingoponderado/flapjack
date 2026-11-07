import Flapjack.EvaluateProps.ClockIoBind

/-! Clock-independent branching prerequisites for the source evaluator
clock-and-I/O proof. Source and carrier review remain pending. -/
namespace Flapjack.EvaluateProps
open Flapjack.SemanticPrimitivesHOL

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_acc_safe"]
theorem isClockIoMono_accSafe {σ α β γ : Type} (f : State σ → α) (s : State σ)
    (v : α) (g : α → State σ → State σ × Result β γ)
    (h : (∀ state clock, f { state with clock } = f state) ∧
      (f s = v ∨ f s ≠ v) ∧ isClockIoMono (fun state => g (f s) state) s) :
    isClockIoMono (fun state => g (f state) state) s := by
  obtain ⟨independent, _, invariant⟩ := h
  simp only [isClockIoMono] at invariant ⊢
  simp only [independent]
  exact invariant

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_if_safe"]
theorem isClockIoMono_ifSafe {σ α β : Type} (f : State σ → Bool)
    (j k : State σ → State σ × Result α β) (st : State σ)
    (h : (∀ state clock, f { state with clock } = f state) ∧
      isClockIoMono (fun state => if f st then j state else k state) st) :
    isClockIoMono (fun state => if f state then j state else k state) st := by
  apply isClockIoMono_accSafe f st true (fun b state => if b then j state else k state)
  exact ⟨h.1, Classical.em _, h.2⟩

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_option_case_safe"]
theorem isClockIoMono_optionCaseSafe {σ α β γ : Type} (f : State σ → Option α)
    (g : State σ → State σ × Result β γ) (h : α → State σ → State σ × Result β γ)
    (st : State σ)
    (assumptions : (∀ state clock, f { state with clock } = f state) ∧
      isClockIoMono (fun state => match f st with | none => g state | some x => h x state) st) :
    isClockIoMono (fun state => match f state with | none => g state | some x => h x state) st := by
  apply isClockIoMono_accSafe f st none (fun value state => match value with | none => g state | some x => h x state)
  exact ⟨assumptions.1, Classical.em _, assumptions.2⟩

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_match_case_safe"]
theorem isClockIoMono_matchCaseSafe {σ α β γ : Type} (f : State σ → MatchResult α)
    (g h : State σ → State σ × Result β γ) (j : α → State σ → State σ × Result β γ)
    (st : State σ)
    (assumptions : (∀ state clock, f { state with clock } = f state) ∧
      isClockIoMono (fun state => match f st with
        | .noMatch => g state | .typeError => h state | .match value => j value state) st) :
    isClockIoMono (fun state => match f state with
      | .noMatch => g state | .typeError => h state | .match value => j value state) st := by
  apply isClockIoMono_accSafe f st .noMatch (fun value state => match value with
    | .noMatch => g state | .typeError => h state | .match x => j x state)
  exact ⟨assumptions.1, Classical.em _, assumptions.2⟩

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "is_clock_io_mono_match_case_pair_safe"]
theorem isClockIoMono_matchCasePairSafe {σ α β γ : Type} (f : State σ → MatchResult α)
    (g h : State σ → Result β γ) (j : α → State σ → Result β γ) (st : State σ)
    (assumptions : (∀ state clock, f { state with clock } = f state) ∧
      isClockIoMono (fun state => (state, match f st with
        | .noMatch => g state | .typeError => h state | .match value => j value state)) st) :
    isClockIoMono (fun state => (state, match f state with
      | .noMatch => g state | .typeError => h state | .match value => j value state)) st := by
  apply isClockIoMono_accSafe f st .noMatch (fun value state => (state, match value with
    | .noMatch => g state | .typeError => h state | .match x => j x state))
  exact ⟨assumptions.1, Classical.em _, assumptions.2⟩

end Flapjack.EvaluateProps
