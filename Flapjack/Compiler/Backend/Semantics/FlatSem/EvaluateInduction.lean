import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateExact
import Flapjack.Misc.ClockWeightInduction
namespace Flapjack.Compiler.Backend.FlatSem
/-- Mutual clock-and-weight induction for flat expression and declaration lists.
This Flapjack infrastructure specializes the shared lexicographic induction;
HOL derives the corresponding induction principle from the evaluator definition. -/
theorem flatEvaluateMeasureRec {C F : Type}
    (P : Environment Value → State C F → List FlatLang.Exp → Prop)
    (Q : State C F → List FlatLang.Exp → Prop)
    (stepE : ∀ env state es,
      (∀ env' state' es', state'.clock ≤ state.clock → expsWeight es' < expsWeight es → P env' state' es') →
      (∀ env' state' es', state'.clock < state.clock → P env' state' es') →
      (∀ state' ds, state'.clock ≤ state.clock → expsWeight ds + 1 < expsWeight es → Q state' ds) →
      (∀ state' ds, state'.clock < state.clock → Q state' ds) → P env state es)
    (stepD : ∀ state ds,
      (∀ env' state' es, state'.clock ≤ state.clock → expsWeight es < expsWeight ds + 1 → P env' state' es) →
      (∀ env' state' es, state'.clock < state.clock → P env' state' es) →
      (∀ state' ds', state'.clock ≤ state.clock → expsWeight ds' + 1 < expsWeight ds + 1 → Q state' ds') →
      (∀ state' ds', state'.clock < state.clock → Q state' ds') → Q state ds) :
    (∀ env state es, P env state es) ∧ (∀ state ds, Q state ds) := by
  let weight : (Environment Value × List FlatLang.Exp) ⊕ List FlatLang.Exp → Nat
    | .inl (_, es) => expsWeight es
    | .inr ds => expsWeight ds + 1
  let motive : ((Environment Value × List FlatLang.Exp) ⊕ List FlatLang.Exp) → State C F → Prop
    | .inl (env, es), state => P env state es
    | .inr ds, state => Q state ds
  have all : ∀ node state, motive node state := by
    refine Flapjack.clockWeightInduction (fun state : State C F => state.clock) weight (motive := motive) ?_
    intro node state smaller lessClock
    cases node with
    | inl pair =>
      obtain ⟨env, es⟩ := pair
      apply stepE env state es
      · intro env' state' es' hclock hweight
        exact smaller (.inl (env', es')) state' hclock hweight
      · intro env' state' es' hclock
        exact lessClock (.inl (env', es')) state' hclock
      · intro state' ds hclock hweight
        exact smaller (.inr ds) state' hclock hweight
      · intro state' ds hclock
        exact lessClock (.inr ds) state' hclock
    | inr ds =>
      apply stepD state ds
      · intro env' state' es hclock hweight
        exact smaller (.inl (env', es)) state' hclock hweight
      · intro env' state' es hclock
        exact lessClock (.inl (env', es)) state' hclock
      · intro state' ds' hclock hweight
        exact smaller (.inr ds') state' hclock hweight
      · intro state' ds' hclock
        exact lessClock (.inr ds') state' hclock
  exact ⟨fun env state es => all (.inl (env, es)) state,
    fun state ds => all (.inr ds) state⟩
end Flapjack.Compiler.Backend.FlatSem
