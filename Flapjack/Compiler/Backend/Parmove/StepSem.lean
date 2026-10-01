import Flapjack.Compiler.Backend.Parmove.StepSem.StartExtend
import Flapjack.Compiler.Backend.Parmove.StepSem.RemoveSelfEmitLast
import Flapjack.Compiler.Backend.Parmove.StepSem.Save
import Flapjack.Compiler.Backend.Parmove.StepSem.EmitHead

namespace Flapjack.Compiler.Backend.Parmove

/-- Full original one-step scheduler semantic preservation. The source Step
and full input wf are the only premises; the target equivalence is proved by
all six genuine constructor cases, for arbitrary environments and histories. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "step_sem"]
theorem step_sem {α β : Type} [DecidableEq α] (first second : State α) :
    Step first second → wf first → ∀ env : Option α → β,
      eqenv (sem first env) (sem second env) := by
  intro transition valid
  cases transition with
  | removeSelf r before after active emitted =>
      exact step_sem_removeSelf r before after active emitted valid
  | start d s before after emitted =>
      exact step_sem_start d s before after emitted valid
  | extend d r s before after active emitted =>
      exact step_sem_extend d r s before after active emitted valid
  | save d s pending active emitted =>
      exact step_sem_save d s pending active emitted valid
  | emitHead d0 dn s0 sn pending active emitted noRead distinct =>
      exact step_sem_emitHead d0 dn s0 sn pending active emitted noRead distinct valid
  | emitLast d s pending emitted noRead =>
      exact step_sem_emitLast d s pending emitted noRead valid

end Flapjack.Compiler.Backend.Parmove
