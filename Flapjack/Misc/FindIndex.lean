module

public import Flapjack.HolRef

@[expose] public section

namespace Flapjack.Misc

/-- Literal first-match search with an arbitrary starting offset. Equality is
propositional equality; absence returns none without inspecting the offset. -/
@[hol "cakeml/misc/miscScript.sml" "find_index_def"]
def findIndex {α : Type} [DecidableEq α] (target : α) : List α → Nat → Option Nat
  | [], _ => none
  | head :: tail, offset =>
      if head = target then some offset else findIndex target tail (offset + 1)

/-- Original `find_index_APPEND_same`: a found index survives appending. -/
@[hol "cakeml/misc/miscScript.sml" "find_index_APPEND_same"]
theorem findIndex_append_same {α : Type} [DecidableEq α] (l1 : List α) :
    ∀ (n : α) (m : Nat) (i : Nat) (l2 : List α),
      findIndex n l1 m = some i → findIndex n (l1 ++ l2) m = some i := by
  induction l1 with
  | nil =>
    intro n m i l2 h
    cases h
  | cons a t ih =>
    intro n m i l2 h
    simp only [findIndex, List.cons_append] at h ⊢
    split at h
    · simp_all
    · simp_all

end Flapjack.Misc
