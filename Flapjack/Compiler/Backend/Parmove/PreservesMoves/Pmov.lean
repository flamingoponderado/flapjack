import Flapjack.Compiler.Backend.Parmove.PreservesMoves.Steps
import Flapjack.Compiler.Backend.Parmove.PmovDsteps
import Flapjack.Compiler.Backend.Parmove.DStepsSteps

namespace Flapjack.Compiler.Backend.Parmove

/-- The actual scheduler preserves each destination of an initial non-self
move under the original well-formedness premise. Its primitive transition
trace is derived, not assumed. `DecidableEq` supplies the canonical scheduler's
computational propositional equality; it adds no equality-law premise. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "pmov_preserves_moves"]
theorem pmovPreservesMoves {α : Type} [DecidableEq α]
    (x y : Option α) (state : State α) :
    wf state ∧ (x, y) ∈ stateToList state ∧ x ≠ y →
      x ∈ (stateToList (pmov state)).map Prod.fst := by
  rintro ⟨valid, member, different⟩
  obtain ⟨source, retained, _⟩ := stepsPreservesMoves x state (pmov state)
    ⟨⟨y, member, different⟩, dsteps_steps state (pmov state) (pmovDsteps state) valid⟩
  exact List.mem_map.mpr ⟨(x, source), retained, rfl⟩

end Flapjack.Compiler.Backend.Parmove
