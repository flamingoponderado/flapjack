import Flapjack.Compiler.Backend.Parmove.PreservesMoves.Step

namespace Flapjack.Compiler.Backend.Parmove

/-- Primitive-step closure preserves a non-self source for the given
destination. The source witness may change along the trace. The free HOL
destination is explicit; no state validity or scratch-safety premise is added. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "steps_preserves_moves"]
theorem stepsPreservesMoves {α : Type} (x : Option α) (first second : State α) :
    (∃ y, (x, y) ∈ stateToList first ∧ x ≠ y) ∧ Steps first second →
      ∃ y, (x, y) ∈ stateToList second ∧ x ≠ y := by
  rintro ⟨witness, transitions⟩
  induction transitions with
  | refl => exact witness
  | @tail middle last previous transition ih =>
      exact stepPreservesMoves middle last transition x ih

end Flapjack.Compiler.Backend.Parmove
