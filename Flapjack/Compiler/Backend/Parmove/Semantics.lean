import Flapjack.Compiler.Backend.Parmove

namespace Flapjack.Compiler.Backend.Parmove

/-- HOL's distinct-destination condition; there is no restriction on sources. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "windmill_def"]
def windmill {α : Type} (moves : List (α × α)) : Prop :=
  (moves.map Prod.fst).Nodup

/-- Flapjack infrastructure implementing one ordinary function update. Equality
is propositional; no boolean equality or finite-map representation is used. -/
def updateEnv {α β : Type} [DecidableEq α] (env : α → β)
    (destination : α) (value : β) : α → β :=
  fun key => if key = destination then value else env key

/-- Flapjack infrastructure implementing HOL's function `UPDATE_LIST`.
The original `UPDATE_LIST_THM` processes the head update before the tail, so
the last update to a repeated destination wins. -/
def updateEnvList {α β : Type} [DecidableEq α] :
    List (α × β) → (α → β) → (α → β)
  | [], env => env
  | (destination, value) :: updates, env =>
      updateEnvList updates (updateEnv env destination value)

/-- Parallel moves read every source from the original environment, then
apply the resulting destination/value updates in the original list order. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parsem_def"]
def parsem {α β : Type} [DecidableEq α] (moves : List (α × α))
    (env : α → β) : α → β :=
  updateEnvList (moves.map fun move => (move.1, env move.2)) env

/-- Sequential moves read from the environment updated by all earlier moves. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "seqsem_def"]
def seqsem {α β : Type} [DecidableEq α] :
    List (α × α) → (α → β) → (α → β)
  | [], env => env
  | (destination, source) :: moves, env =>
      seqsem moves (updateEnv env destination (env source))

/-- Semantic interpretation of the scheduler's three lists. The emitted list
is reversed before execution; pending and active moves then run in parallel. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "sem_def"]
def sem {α β : Type} [DecidableEq α]
    (state : List (α × α) × List (α × α) × List (α × α))
    (env : α → β) : α → β :=
  parsem (state.1 ++ state.2.1) (seqsem state.2.2.reverse env)

/-- Environment equivalence compares every real register and ignores the
temporary register `none`, exactly as HOL's `IS_SOME` guard does. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "eqenv_def"]
def eqenv {α β : Type} (first second : Option α → β) : Prop :=
  ∀ register, register.isSome = true → first register = second register

@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "seqsem_append"]
theorem seqsem_append {α β : Type} [DecidableEq α]
    (first second : List (α × α)) :
    seqsem (β := β) (first ++ second) = seqsem second ∘ seqsem first := by
  induction first with
  | nil => rfl
  | cons move first ih =>
      rcases move with ⟨destination, source⟩
      funext env
      exact congrFun ih (updateEnv env destination (env source))

@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "sem_init"]
theorem sem_init {α β : Type} [DecidableEq α] (pending : List (α × α)) :
    sem (β := β) (pending, [], []) = parsem pending := by
  funext env
  simp [sem, seqsem]

@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "sem_final"]
theorem sem_final {α β : Type} [DecidableEq α] (emitted : List (α × α)) :
    sem (β := β) ([], [], emitted) = seqsem emitted.reverse := by
  rfl

end Flapjack.Compiler.Backend.Parmove
