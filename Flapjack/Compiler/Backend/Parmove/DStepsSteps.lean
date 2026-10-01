import Flapjack.Compiler.Backend.Parmove.Invariants.Preservation
import Flapjack.Compiler.Backend.Parmove.DStepStep

namespace Flapjack.Compiler.Backend.Parmove

/-- Deterministic-step closure refines primitive-step closure under the
original initial-state well-formedness premise. Intermediate well-formedness
is derived from primitive closure preservation, rather than assumed. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "dsteps_steps"]
theorem dsteps_steps {α : Type} (first second : State α) :
    DSteps first second → wf first → Steps first second := by
  intro transitions valid
  induction transitions with
  | refl => exact Relation.ReflTransGen.refl
  | @tail middle last transitions transition ih =>
      exact ih.trans (dstep_step middle last transition
        (wf_steps first middle ⟨valid, ih⟩))

end Flapjack.Compiler.Backend.Parmove
