import Flapjack.Compiler.Backend.Parmove.Semantics

namespace Flapjack.Compiler.Backend.Parmove

/-- Sequential moves preserve any register absent from their destinations.
Both the register and environment value carriers are unrestricted. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "seqsem_move_unchanged"]
theorem seqsemMoveUnchanged {α β : Type} [DecidableEq α]
    (moves : List (α × α)) (env : α → β) (key : α)
    (absent : key ∉ moves.map Prod.fst) :
    seqsem moves env key = env key := by
  induction moves generalizing env with
  | nil => rfl
  | cons move moves ih =>
      rcases move with ⟨destination, source⟩
      have h : key ≠ destination ∧ key ∉ moves.map Prod.fst := by
        simpa using absent
      rw [seqsem, ih _ h.2]
      simp [updateEnv, h.1]

end Flapjack.Compiler.Backend.Parmove
