import Flapjack.Compiler.Backend.Parmove.StepSem

namespace Flapjack.Compiler.Backend.Parmove

/-- Original reflexive-transitive scheduler semantic preservation. The full
initial invariant and actual Step closure suffice: intermediate wf follows
from wf_steps, and the arbitrary-environment real-register equalities compose.
No intermediate or final equivalence is assumed. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "steps_sem"]
theorem steps_sem {α β : Type} [DecidableEq α] (first second : State α) :
    Steps first second ∧ wf first → ∀ env : Option α → β,
      eqenv (sem first env) (sem second env) := by
  rintro ⟨steps, valid⟩ env register real
  induction steps with
  | refl => rfl
  | @tail middle last steps step ih =>
      exact ih.trans (step_sem middle last step
        (wf_steps first middle ⟨valid, steps⟩) env register real)

end Flapjack.Compiler.Backend.Parmove
