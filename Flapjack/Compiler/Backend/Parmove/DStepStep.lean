import Flapjack.Compiler.Backend.Parmove.DSteps
import Flapjack.Compiler.Backend.Parmove.Invariants

namespace Flapjack.Compiler.Backend.Parmove

/-- Each deterministic transition is a finite sequence of primitive transitions.
The cycle clause performs Save followed by EmitHead; its non-temporary head
follows from the original well-formedness premise, not an extra assumption. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "dstep_step"]
theorem dstep_step {α : Type} (first second : State α) :
    DStep first second → wf first → Steps first second := by
  intro transition valid
  cases transition with
  | removeSelf r pending emitted =>
    exact Relation.ReflTransGen.single (by
      simpa using Step.removeSelf r [] pending [] emitted)
  | start d s pending emitted distinct =>
    exact Relation.ReflTransGen.single (by
      simpa using Step.start d s [] pending emitted)
  | extend d r s before after active emitted noRead =>
    exact Relation.ReflTransGen.single (Step.extend d r s before after active emitted)
  | saveEmit r s d pending active emitted noRead =>
    have real : r.isSome = true :=
      valid.2.2.2.2.1 (r,s) (by simp)
    have distinct : r ≠ none := by
      intro equality
      simp [equality] at real
    have save := Step.save d r pending ([(r,s)] ++ active) emitted
    have emit := Step.emitHead d r none s pending active ([(none,r)] ++ emitted)
      noRead distinct
    simpa [List.append_assoc] using
      (Relation.ReflTransGen.single save).tail emit
  | emitHead d0 dn s0 sn pending active emitted noRead distinct =>
    exact Relation.ReflTransGen.single
      (Step.emitHead d0 dn s0 sn pending active emitted noRead distinct)
  | emitLast d s pending emitted noRead =>
    exact Relation.ReflTransGen.single (Step.emitLast d s pending emitted noRead)

end Flapjack.Compiler.Backend.Parmove
