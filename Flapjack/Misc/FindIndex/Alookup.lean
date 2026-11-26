module

public import Flapjack.Misc.FindIndex

@[expose] public section

namespace Flapjack.Misc

/-- Original `ALOOKUP_find_index_NONE`: when the association list has no entry
for the key, searching the projected key list fails too. HOL's `ALOOKUP` is
`List.lookup` and `MAP FST` is `List.map Prod.fst`. -/
@[hol "cakeml/misc/miscScript.sml" "ALOOKUP_find_index_NONE"]
theorem lookup_findIndex_none {α β : Type} [DecidableEq β] (env : List (β × α))
    (k : β) :
    ∀ m : Nat, env.lookup k = none → findIndex k (env.map Prod.fst) m = none := by
  induction env with
  | nil =>
    intro m _
    simp [findIndex]
  | cons pair rest ih =>
    intro m h
    obtain ⟨k', v⟩ := pair
    by_cases same : k' = k
    · have hbeq : (k == k') = true := by simp [same]
      simp [List.lookup, hbeq] at h
    · have hbeq : (k == k') = false := by simp [Ne.symm same]
      simp only [List.lookup, hbeq, List.map_cons, findIndex, if_neg same] at h ⊢
      exact ih (m + 1) h

end Flapjack.Misc
