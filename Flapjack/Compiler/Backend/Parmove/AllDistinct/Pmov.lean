import Flapjack.Compiler.Backend.Parmove.AllDistinct.Steps
import Flapjack.Compiler.Backend.Parmove.PmovDsteps
import Flapjack.Compiler.Backend.Parmove.DStepsSteps

namespace Flapjack.Compiler.Backend.Parmove

/-- The actual scheduler preserves distinct real destinations across all
three move lists. Scratch destinations are filtered before checking Nodup.
The only premises are HOL's initial well-formedness and distinctness; actual
scheduler reachability and every intermediate invariant are derived. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "ALL_DISTINCT_pmov"]
theorem allDistinctPmov {α : Type} [DecidableEq α] (state : State α) :
    wf state ∧
      (((state.1 ++ state.2.1 ++ state.2.2).map Prod.fst).filter Option.isSome).Nodup →
    ((((pmov state).1 ++ (pmov state).2.1 ++ (pmov state).2.2).map Prod.fst).filter
      Option.isSome).Nodup := by
  rintro ⟨valid, distinct⟩
  exact allDistinctSteps state (pmov state)
    ⟨distinct, dsteps_steps state (pmov state) (pmovDsteps state) valid⟩

end Flapjack.Compiler.Backend.Parmove
