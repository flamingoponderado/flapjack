module

public import Flapjack.Basis.Pure.MlList.SortPerm
public import Mathlib.Data.Set.Basic

@[expose] public section

/-!
# Cake `mllist$sort_set`

HOL's `set` of a list is rendered as the membership-predicate set, so
`sort_set` states that sorting keeps the set of members. This lives in its own
module so the `Mathlib.Data.Set` import does not reach `SortPerm`'s many
downstream users.
-/

namespace Flapjack.Basis.Pure.MlList

/-- Exact HOL `sort_set` (`mllistScript.sml:331-335`): sorting keeps the set of
members, written as the membership predicate of HOL's list set. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "sort_set"]
theorem sortSet {α : Type} (R : α → α → Bool) (l : List α) :
    ({x | x ∈ sort R l} : Set α) = {x | x ∈ l} := by
  ext x
  exact sortMem x R l

end Flapjack.Basis.Pure.MlList
