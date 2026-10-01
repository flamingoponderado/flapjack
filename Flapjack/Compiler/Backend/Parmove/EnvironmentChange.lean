import Flapjack.Compiler.Backend.Parmove.Semantics

namespace Flapjack.Compiler.Backend.Parmove

/-- Flapjack function-update infrastructure, with no standalone HOL original:
equal updates preserve equality at a key if the initial values agree whenever
that key is untouched. This proves the codec fact used by the source lemma. -/
theorem updateEnvList_base_at {α β : Type} [DecidableEq α]
    (updates : List (α × β)) (first second : α → β) (key : α)
    (base : key ∉ updates.map Prod.fst → first key = second key) :
    updateEnvList updates first key = updateEnvList updates second key := by
  induction updates generalizing first second with
  | nil => exact base (by simp)
  | cons head tail ih =>
      rcases head with ⟨destination, value⟩
      apply ih
      intro fresh
      by_cases same : key = destination
      · simp [updateEnv, same]
      · simp only [updateEnv, if_neg same]
        exact base (by simp [same, fresh])

/-- Exact environment-change rule: retain the untouched-key conditional and
source-value map equality. No distinct-destination premise is added. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parsem_change_env"]
theorem parsem_change_env {α β : Type} [DecidableEq α]
    (moves : List (α × α)) (first second : α → β) (key : α) :
    (key ∉ moves.map Prod.fst → first key = second key) ∧
      moves.map (first ∘ Prod.snd) = moves.map (second ∘ Prod.snd) →
    parsem moves first key = parsem moves second key := by
  intro h
  have updates : moves.map (fun move => (move.1, first move.2)) =
      moves.map (fun move => (move.1, second move.2)) := by
    apply List.map_congr_left
    intro move member
    have values := List.map_eq_map_iff.mp h.2 move member
    exact congrArg (fun value => (move.1, value)) values
  unfold parsem
  rw [updates]
  apply updateEnvList_base_at
  simpa only [List.map_map, Function.comp_def] using h.1

end Flapjack.Compiler.Backend.Parmove
