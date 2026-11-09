module

@[expose] public section

/-! Shared lexicographic `(clock, weight)` induction for backend evaluator proofs. -/
namespace Flapjack

/-- Induction on the lexicographic pair `(clock s, weight e)`, clock first. The
    step may use any pair with a smaller-or-equal clock and a strictly smaller
    weight, and any pair with a strictly smaller clock. This packages the measure
    HOL's generated `evaluate_ind` theorems are derived from, so backend evaluator
    proofs can state their motive once instead of nesting two `Nat.strongRecOn`
    inductions and restating it for each induction hypothesis.

    Flapjack infrastructure, so it carries no `@[hol]` tag: HOL has no single
    lemma of this shape, since each generated `evaluate_ind` restates the same
    nested measure for its own evaluator. -/
theorem clockWeightInduction {α σ : Type _} (clock : σ → Nat) (weight : α → Nat)
    {motive : α → σ → Prop}
    (step : ∀ e s,
      (∀ e' s', clock s' ≤ clock s → weight e' < weight e → motive e' s') →
      (∀ e' s', clock s' < clock s → motive e' s') →
      motive e s) :
    ∀ e s, motive e s := by
  intro e s
  have key : ∀ (c w : Nat) (e : α) (s : σ), clock s = c → weight e = w → motive e s := by
    intro c
    induction c using Nat.strongRecOn with
    | ind c cIH =>
      intro w
      induction w using Nat.strongRecOn with
      | ind w wIH =>
        intro e s hc hw
        refine step e s ?_ ?_
        · intro e' s' hle hlt
          have hc' : clock s' ≤ c := by rw [← hc]; exact hle
          have hw' : weight e' < w := by rw [← hw]; exact hlt
          rcases Nat.lt_or_eq_of_le hc' with h | h
          · exact cIH _ h _ e' s' rfl rfl
          · exact wIH _ hw' e' s' h rfl
        · intro e' s' hlt
          have hc' : clock s' < c := by rw [← hc]; exact hlt
          exact cIH _ hc' _ e' s' rfl rfl
  exact key _ _ e s rfl rfl

/-- Mutual induction on the lexicographic pair `(clock s, weight e)` for an
    expression motive `motiveE` and an application motive `motiveA`.

    The application step may only use strictly smaller clocks, for both the
    body expression and recursive applications, so it can be proved before the
    weight induction at the same clock. The expression step may use
    `(≤ clock, < weight)`, `< clock`, and applications at `≤ clock`, which is
    the shape of the Clos `evaluate`/`evaluateApp` proofs.

    Flapjack infrastructure, so it carries no `@[hol]` tag: HOL derives each
    generated `evaluate_ind` from the same nested measure, with the application
    part folded into the evaluator's own induction rather than stated as a
    separate lemma. -/
theorem clockWeightAppInduction {α β σ : Type _} (clock : σ → Nat) (weight : α → Nat)
    {motiveE : α → σ → Prop} {motiveA : β → σ → Prop}
    (stepA : ∀ b s,
      (∀ e s', clock s' < clock s → motiveE e s') →
      (∀ b' s', clock s' < clock s → motiveA b' s') → motiveA b s)
    (stepE : ∀ e s,
      (∀ e' s', clock s' ≤ clock s → weight e' < weight e → motiveE e' s') →
      (∀ e' s', clock s' < clock s → motiveE e' s') →
      (∀ b s', clock s' ≤ clock s → motiveA b s') → motiveE e s) :
    (∀ e s, motiveE e s) ∧ (∀ b s, motiveA b s) := by
  have ranks : ∀ c : Nat,
      (∀ (w : Nat) (e : α) (s : σ), clock s = c → weight e = w → motiveE e s) ∧
      (∀ (b : β) (s : σ), clock s = c → motiveA b s) := by
    intro c
    induction c using Nat.strongRecOn with
    | ind c cIH =>
      have appIH : ∀ (b : β) (s : σ), clock s = c → motiveA b s := by
        intro b s hc
        refine stepA b s ?_ ?_
        · intro e s' hlt
          have hc' : clock s' < c := by rw [← hc]; exact hlt
          exact (cIH _ hc').1 _ e s' rfl rfl
        · intro b' s' hlt
          have hc' : clock s' < c := by rw [← hc]; exact hlt
          exact (cIH _ hc').2 b' s' rfl
      constructor
      · intro w
        induction w using Nat.strongRecOn with
        | ind w wIH =>
          intro e s hc hw
          refine stepE e s ?_ ?_ ?_
          · intro e' s' hle hlt
            have hc' : clock s' ≤ c := by rw [← hc]; exact hle
            have hw' : weight e' < w := by rw [← hw]; exact hlt
            rcases Nat.lt_or_eq_of_le hc' with h | h
            · exact (cIH _ h).1 _ e' s' rfl rfl
            · exact wIH _ hw' e' s' h rfl
          · intro e' s' hlt
            have hc' : clock s' < c := by rw [← hc]; exact hlt
            exact (cIH _ hc').1 _ e' s' rfl rfl
          · intro b s' hle
            have hc' : clock s' ≤ c := by rw [← hc]; exact hle
            rcases Nat.lt_or_eq_of_le hc' with h | h
            · exact (cIH _ h).2 b s' rfl
            · exact appIH b s' h
      · exact appIH
  constructor
  · intro e s
    exact (ranks _).1 _ e s rfl rfl
  · intro b s
    exact (ranks _).2 b s rfl

end Flapjack
