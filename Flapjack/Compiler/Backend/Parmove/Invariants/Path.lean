import Flapjack.Compiler.Backend.Parmove.Invariants

namespace Flapjack.Compiler.Backend.Parmove

@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "windmill_cons"]
theorem windmill_cons {α : Type} (move : α × α) (moves : List (α × α)) :
    windmill (move :: moves) ↔ move.1 ∉ moves.map Prod.fst ∧ windmill moves := by
  simp [windmill]

/-- Changing only the source of the final move preserves the path, since every
path link checks the next destination against the preceding source. The exact
HOL conjunction of input-path and final-destination equality is retained. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "path_change_start"]
theorem path_change_start {α : Type} (before : List (α × α))
    (replacement last : α × α) :
    path (before ++ [last]) ∧ last.1 = replacement.1 →
      path (before ++ [replacement]) := by
  intro h
  induction before generalizing replacement last with
  | nil => simp [path]
  | cons head before ih =>
      rcases h with ⟨valid, sameDestination⟩
      cases before with
      | nil =>
          rcases head with ⟨destination, source⟩
          rcases last with ⟨lastDestination, lastSource⟩
          rcases replacement with ⟨newDestination, newSource⟩
          simp_all [path]
      | cons next rest =>
          rcases head with ⟨destination, source⟩
          rcases next with ⟨nextDestination, nextSource⟩
          change nextDestination = source ∧ path ((nextDestination, nextSource) :: (rest ++ [last])) at valid
          change nextDestination = source ∧ path ((nextDestination, nextSource) :: (rest ++ [replacement]))
          exact ⟨valid.1, ih replacement last ⟨valid.2, sameDestination⟩⟩

end Flapjack.Compiler.Backend.Parmove
