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

/-- Flapjack-only endpoint decomposition lemma. Each path read either names
one of its destinations or the final source. This structural helper has no
separately exported HOL original. -/
theorem path_read_mem_or_endpoint {α : Type} (before : List (α × α))
    (last : α × α) (valid : path (before ++ [last])) (read : α)
    (member : read ∈ (before ++ [last]).map Prod.snd) :
    read ∈ (before ++ [last]).map Prod.fst ∨ read = last.2 := by
  induction before with
  | nil => exact Or.inr (by simpa using member)
  | cons head before ih =>
      simp only [List.cons_append, List.map_cons, List.mem_cons] at member ⊢
      rcases member with equal | member
      · cases before with
        | nil =>
            have link : last.1 = head.2 := by
              simpa [path] using valid
            exact Or.inl (Or.inr (by simp [equal, link]))
        | cons next rest =>
            have link : next.1 = head.2 := by
              cases head; cases next
              exact valid.1
            exact Or.inl (Or.inr (by simp [equal, link]))
      · have tailValid : path (before ++ [last]) := path_tail _ head valid
        rcases ih tailValid member with found | endpoint
        · exact Or.inl (Or.inr found)
        · exact Or.inr endpoint

/-- Flapjack-only no-read infrastructure for the scheduler emit-head case.
The nonempty endpoint decomposition discharges HOL local NoRead_path length
and HD/LAST observations without choosing values for empty lists. Only the
original path, destination uniqueness and endpoint mismatch are assumed. -/
theorem path_tail_noRead {α : Type} (head : α × α)
    (middle : List (α × α)) (last : α × α)
    (valid : path (head :: (middle ++ [last])))
    (unique : windmill (head :: (middle ++ [last])))
    (different : head.1 ≠ last.2) :
    head.1 ∉ (middle ++ [last]).map Prod.snd := by
  intro member
  have noDestination := (windmill_cons head (middle ++ [last])).mp unique |>.1
  rcases path_read_mem_or_endpoint middle last (path_tail _ head valid) head.1 member with
    destination | endpoint
  · exact noDestination destination
  · exact different endpoint

end Flapjack.Compiler.Backend.Parmove
