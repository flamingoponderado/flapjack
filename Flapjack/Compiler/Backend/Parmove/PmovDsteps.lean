import Flapjack.Compiler.Backend.Parmove.FstepDstep

namespace Flapjack.Compiler.Backend.Parmove

/-- Unconditional reflexive-transitive deterministic-step closure of the
actual scheduler recursion. No well-formedness or assumed output relation. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "pmov_dsteps"]
theorem pmovDsteps {α : Type} [DecidableEq α] (state : State α) :
    DSteps state (pmov state) := by
  induction state using pmov.induct with
  | case1 state finished =>
      rw [pmov.eq_def, dif_pos finished]
  | case2 state unfinished ih =>
      rw [pmov.eq_def, dif_neg unfinished]
      apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single (fstepDstep state ?_)) ih
      intro emitted equal
      exact unfinished (equal ▸ ⟨rfl, rfl⟩)

end Flapjack.Compiler.Backend.Parmove
