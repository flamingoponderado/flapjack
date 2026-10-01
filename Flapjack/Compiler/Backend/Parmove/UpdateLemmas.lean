import Flapjack.Compiler.Backend.Parmove.Semantics

namespace Flapjack.Compiler.Backend.Parmove

/-- Flapjack infrastructure for distinct-key function updates; this supports
our UPDATE_LIST codec and is not presented as a separate named HOL port. -/
theorem updateEnv_commute {α β : Type} [DecidableEq α]
    (env : α → β) (x y : α) (vx vy : β) (distinct : x ≠ y) :
    updateEnv (updateEnv env x vx) y vy = updateEnv (updateEnv env y vy) x vx := by
  funext key
  by_cases hx : key = x <;> by_cases hy : key = y <;>
    simp_all [updateEnv]

/-- Flapjack UPDATE_LIST codec infrastructure: an update at a key absent from
all later destinations commutes through the complete update list. -/
theorem updateEnvList_fresh {α β : Type} [DecidableEq α]
    (updates : List (α × β)) (env : α → β) (key : α) (value : β)
    (fresh : key ∉ updates.map Prod.fst) :
    updateEnvList updates (updateEnv env key value) =
      updateEnv (updateEnvList updates env) key value := by
  induction updates generalizing env with
  | nil => rfl
  | cons move updates ih =>
      rcases move with ⟨destination, nextValue⟩
      simp only [List.map_cons, List.mem_cons, not_or] at fresh
      simp only [updateEnvList]
      rw [updateEnv_commute env key destination value nextValue fresh.1]
      exact ih (updateEnv env destination nextValue) fresh.2

/-- Flapjack UPDATE_LIST codec infrastructure for an untouched key. Unlike the
HOL parsem theorem, the stronger generic codec fact needs no windmill premise. -/
theorem updateEnvList_untouched {α β : Type} [DecidableEq α]
    (updates : List (α × β)) (env : α → β) (key : α)
    (fresh : key ∉ updates.map Prod.fst) :
    updateEnvList updates env key = env key := by
  induction updates generalizing env with
  | nil => rfl
  | cons move updates ih =>
      rcases move with ⟨destination, value⟩
      simp only [List.map_cons, List.mem_cons, not_or] at fresh
      simp only [updateEnvList]
      rw [ih (updateEnv env destination value) fresh.2]
      simp [updateEnv, fresh.1]

@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parsem_cons"]
theorem parsem_cons {α β : Type} [DecidableEq α]
    (x y : α) (moves : List (α × α)) (env : α → β) :
    x ∉ moves.map Prod.fst →
      parsem ((x, y) :: moves) env = updateEnv (parsem moves env) x (env y) := by
  intro fresh
  simp only [parsem, List.map_cons, updateEnvList]
  apply updateEnvList_fresh
  simpa [List.map_map, Function.comp_def] using fresh

@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parsem_untouched"]
theorem parsem_untouched {α β : Type} [DecidableEq α]
    (env : α → β) (moves : List (α × α)) (x : α) :
    windmill moves ∧ x ∉ moves.map Prod.fst → parsem moves env x = env x := by
  rintro ⟨_distinct, fresh⟩
  apply updateEnvList_untouched
  simpa [List.map_map, Function.comp_def] using fresh

@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "eqenv_sym"]
theorem eqenv_sym {α β : Type} (first second : Option α → β) :
    eqenv first second → eqenv second first := by
  intro same register real
  exact (same register real).symm

end Flapjack.Compiler.Backend.Parmove
