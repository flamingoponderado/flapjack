module

public import Flapjack.Misc.FindIndex

@[expose] public section

namespace Flapjack.Misc

/-- Original `find_index_MAP_inj`: a function injective at the target on the
searched list preserves the search result when mapped over the list. The
premise is the HOL hypothesis `∀y. MEM y ls ⇒ f x = f y ⇒ x = y`, kept as one
hypothesis. -/
@[hol "cakeml/misc/miscScript.sml" "find_index_MAP_inj"]
theorem findIndex_map_inj {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (x : α) :
    ∀ (ls : List α) (n : Nat), (∀ y ∈ ls, f x = f y → x = y) →
      findIndex (f x) (ls.map f) n = findIndex x ls n := by
  intro ls
  induction ls with
  | nil =>
    intro n _
    simp [findIndex]
  | cons head tail ih =>
    intro n h
    have key : f head = f x ↔ head = x := by
      constructor
      · intro same
        exact (h head (by simp) same.symm).symm
      · intro same
        rw [same]
    simp only [List.map_cons, findIndex, key]
    by_cases same : head = x
    · rw [if_pos same, if_pos same]
    · rw [if_neg same, if_neg same]
      exact ih (n + 1) (fun y hy => h y (by simp [hy]))

end Flapjack.Misc
