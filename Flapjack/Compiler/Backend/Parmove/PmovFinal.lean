import Flapjack.Compiler.Backend.Parmove

namespace Flapjack.Compiler.Backend.Parmove

/-- Original unconditional terminal shape for the literal scheduler recursion.
The emitted history is existentially obtained from actual pmov, without a
well-formedness, simulation or assumed termination-result premise. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "pmov_final"]
theorem pmov_final {α : Type} [DecidableEq α] (state : State α) :
    ∃ emitted, pmov state = ([], [], emitted) := by
  induction state using pmov.induct with
  | case1 state finished =>
      rcases state with ⟨pending, active, emitted⟩
      rcases finished with ⟨rfl, rfl⟩
      exact ⟨emitted, by rw [pmov.eq_def]; simp⟩
  | case2 state unfinished ih =>
      rw [pmov.eq_def, dif_neg unfinished]
      exact ih

end Flapjack.Compiler.Backend.Parmove
