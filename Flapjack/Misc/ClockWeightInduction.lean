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

end Flapjack
