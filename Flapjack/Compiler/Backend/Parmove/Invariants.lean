import Flapjack.Compiler.Backend.Parmove.Semantics

namespace Flapjack.Compiler.Backend.Parmove

/-- Adjacent moves form a path when the earlier source is the later destination.
The empty and singleton lists satisfy the predicate without a side condition. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "path_def"]
def path {α : Type} : List (α × α) → Prop
  | [] => True
  | [_] => True
  | (_destination, source) :: (nextDestination, nextSource) :: rest =>
      nextDestination = source ∧ path ((nextDestination, nextSource) :: rest)

@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "path_tail"]
theorem path_tail {α : Type} (tail : List (α × α)) (head : α × α) :
    path (head :: tail) → path tail := by
  cases tail with
  | nil => simp [path]
  | cons next rest =>
      rcases head with ⟨destination, source⟩
      rcases next with ⟨nextDestination, nextSource⟩
      exact And.right

/-- The six HOL state-invariant conjuncts, in source order. `dropLast` models
FRONT only under the original nonempty-active implication, so no arbitrary
FRONT-empty value or extra premise is introduced. HOL gives the ignored emitted component an independent arbitrary carrier γ,
not necessarily a register-move list; this generality is retained. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "wf_def"]
def wf {α γ : Type} (state : List (Move α) × List (Move α) × γ) : Prop :=
  windmill (state.1 ++ state.2.1) ∧
  (∀ move ∈ state.1, move.1.isSome = true) ∧
  (∀ move ∈ state.1, move.2.isSome = true) ∧
  (state.2.1 ≠ [] → ∀ move ∈ state.2.1.dropLast, move.2.isSome = true) ∧
  (∀ move ∈ state.2.1, move.1.isSome = true) ∧
  path state.2.1

@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "wf_init"]
theorem wf_init {α β : Type} (pending : List (Move α)) :
    windmill pending ∧
    (∀ move ∈ pending, move.1.isSome = true) ∧
    (∀ move ∈ pending, move.2.isSome = true) → wf (pending, [], ([] : List β)) := by
  rintro ⟨distinct, destinations, sources⟩
  simpa [wf, path] using And.intro distinct (And.intro destinations sources)

end Flapjack.Compiler.Backend.Parmove
