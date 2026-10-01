import Flapjack.Compiler.Backend.Parmove.Semantics

namespace Flapjack.Compiler.Backend.Parmove

/-- Exact no-read rule. No destination uniqueness or no-write condition is
assumed: all reads in the tail avoid the updated destination. HOL's local
NoRead overload is expanded to its literal source-membership condition. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parsem_NoRead"]
theorem parsem_NoRead {α β : Type} [DecidableEq α]
    (moves : List (α × α)) (x y : α) (env : α → β) :
    x ∉ moves.map Prod.snd →
    parsem ((x,y) :: moves) env = parsem moves (updateEnv env x (env y)) := by
  intro noRead
  have updates : moves.map (fun move => (move.1, env move.2)) =
      moves.map (fun move => (move.1, updateEnv env x (env y) move.2)) := by
    apply List.map_congr_left
    intro move member
    have distinct : move.2 ≠ x := by
      intro equal
      apply noRead
      rw [← equal]
      exact List.mem_map.mpr ⟨move, member, rfl⟩
    simp [updateEnv, distinct]
  simp only [parsem, List.map_cons, updateEnvList]
  rw [updates]

end Flapjack.Compiler.Backend.Parmove
