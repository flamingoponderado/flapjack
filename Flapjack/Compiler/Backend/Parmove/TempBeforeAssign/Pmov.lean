import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign.Steps
import Flapjack.Compiler.Backend.Parmove.PmovDsteps
import Flapjack.Compiler.Backend.Parmove.DStepsSteps

namespace Flapjack.Compiler.Backend.Parmove

/-- The actual scheduler preserves scratch initialization in the reversed
active/emitted chronology under the original initial well-formedness and
scratch-safety premises. The original unused quantified `i` is retained with
an arbitrary independent carrier. Scheduler reachability and intermediate
invariants are derived, not assumed. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "pmov_not_use_temp_before_assign"]
theorem pmovNotUseTempBeforeAssign {α ι : Type} [DecidableEq α]
    (state : State α) (_i : ι) :
    wf state ∧ notUseTempBeforeAssign (state.2.1 ++ state.2.2).reverse = true →
      notUseTempBeforeAssign ((pmov state).2.1 ++ (pmov state).2.2).reverse = true := by
  rintro ⟨valid, safe⟩
  exact (stepsNotUseTempBeforeAssign state (pmov state)
    ⟨⟨valid, safe⟩, dsteps_steps state (pmov state) (pmovDsteps state) valid⟩).2

end Flapjack.Compiler.Backend.Parmove
