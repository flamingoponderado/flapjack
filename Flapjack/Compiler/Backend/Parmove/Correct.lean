import Flapjack.Compiler.Backend.Parmove.PmovFinal
import Flapjack.Compiler.Backend.Parmove.PmovDsteps
import Flapjack.Compiler.Backend.Parmove.DStepsSteps
import Flapjack.Compiler.Backend.Parmove.StepsCorrect
import Flapjack.Compiler.Backend.Parmove.UpdateLemmas

namespace Flapjack.Compiler.Backend.Parmove

/-- Full parallel-move compiler correctness. The actual scheduler supplies its
terminal state and transition closure; only the original unique-destination
premise is assumed. Equivalence ignores the temporary register. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parmove_correct"]
theorem parmove_correct {α β : Type} [DecidableEq α]
    (moves : List (α × α)) :
    windmill moves → ∀ env : Option α → β,
      eqenv (seqsem (parmove moves) env)
        (parsem (moves.map fun move => (some move.1, some move.2)) env) := by
  intro unique env
  let pending := moves.map fun move => (some move.1, some move.2)
  have distinct : windmill pending := by
    change List.Pairwise (· ≠ ·) (pending.map Prod.fst)
    simpa only [pending, List.map_map, Function.comp_def] using
      unique.map (f := Option.some) (by
        intro a b distinct equal
        exact distinct (Option.some.inj equal))
  have destinations : ∀ move ∈ pending, move.1.isSome = true := by
    intro move member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    rfl
  have sources : ∀ move ∈ pending, move.2.isSome = true := by
    intro move member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    rfl
  have valid := wf_init (β := Move α) pending ⟨distinct, destinations, sources⟩
  obtain ⟨emitted, final⟩ := pmov_final (pending, [], [])
  have deterministic := pmovDsteps (pending, [], [])
  rw [final] at deterministic
  have transitions := dsteps_steps _ _ deterministic valid
  have result := eqenv_sym _ _
    (steps_correct pending emitted ⟨distinct, destinations, sources, transitions⟩ env)
  simpa [parmove, pending, final] using result

end Flapjack.Compiler.Backend.Parmove
