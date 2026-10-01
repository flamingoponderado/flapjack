import Flapjack.Compiler.Backend.Parmove.Invariants.Preservation
import Flapjack.Compiler.Backend.Parmove.Permutation
import Flapjack.Compiler.Backend.Parmove.EnvironmentChange

namespace Flapjack.Compiler.Backend.Parmove

/-- Generic list reassociation infrastructure: expose the final move of the
active list. This helper has no separately named HOL declaration. -/
private theorem finalToFront {α : Type} (pending active : List α) (move : α) :
    (pending ++ (active ++ [move])).Perm (move :: (pending ++ active)) := by
  simpa only [List.append_assoc, List.append_nil] using
    (List.perm_middle : ((pending ++ active) ++ move :: []).Perm
      (move :: ((pending ++ active) ++ [])))

/-- The Save case of HOL's `step_sem`, retaining the entire input invariant,
arbitrary emitted history and every-real-register equivalence conclusion.
The remaining's real-source property is derived from `wf`, not assumed as an
extra environment-agreement premise. The constructor is instantiated in the
two states, including its literal `NONE` temporary save. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "step_sem"]
theorem step_sem_save {α β : Type} [DecidableEq α]
    (d s : Option α) (pending active emitted : List (Move α)) :
    wf (pending, active ++ [(d,s)], emitted) →
      ∀ env : Option α → β,
        eqenv (sem (pending, active ++ [(d,s)], emitted) env)
          (sem (pending, active ++ [(d,none)], [(none,s)] ++ emitted) env) := by
  intro valid env register real
  let remaining := pending ++ active
  let base := seqsem emitted.reverse env
  let saved := updateEnv base none (base s)
  have perm := finalToFront pending active (d,s)
  have ordered := (perm.map Prod.fst).nodup_iff.mp valid.1
  have parts : d ∉ remaining.map Prod.fst ∧ windmill remaining := by
    simpa [remaining, windmill] using ordered
  have targetValid := wf_step _ _ (Step.save d s pending active emitted) valid
  have oldSame := parsem_perm (β := β) (pending ++ (active ++ [(d,s)]))
    ((d,s) :: remaining) ⟨valid.1, perm⟩
  have newSame := parsem_perm (β := β) (pending ++ (active ++ [(d,none)]))
    ((d,none) :: remaining) ⟨targetValid.1, finalToFront pending active (d,none)⟩
  have history : seqsem ([(none,s)] ++ emitted).reverse env = saved := by
    rw [List.reverse_append, List.reverse_singleton, seqsem_append]
    rfl
  change parsem (pending ++ (active ++ [(d,s)])) base register =
    parsem (pending ++ (active ++ [(d,none)]))
      (seqsem ([(none,s)] ++ emitted).reverse env) register
  rw [oldSame, newSame, history, parsem_cons d s remaining base parts.1,
    parsem_cons d none remaining saved parts.1]
  have savedSource : saved none = base s := by simp [saved, updateEnv]
  rw [savedSource]
  by_cases same : register = d
  · simp [updateEnv, same]
  · simp only [updateEnv, if_neg same]
    apply parsem_change_env remaining base saved register
    constructor
    · intro _fresh
      have notTemporary : register ≠ none := by
        intro equal
        simp [equal] at real
      simp [saved, updateEnv, notTemporary]
    · apply List.map_congr_left
      intro move member
      have isReal : move.2.isSome = true := by
        rcases List.mem_append.mp member with pendingMember | activeMember
        · exact valid.2.2.1 move pendingMember
        · apply valid.2.2.2.1 (by simp) move
          simpa using activeMember
      have notTemporary : move.2 ≠ none := by
        intro equal
        simp [equal] at isReal
      simp [saved, updateEnv, notTemporary]

end Flapjack.Compiler.Backend.Parmove
