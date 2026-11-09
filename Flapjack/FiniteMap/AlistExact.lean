import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-! HOL association-list maps in the canonical finite-support carrier. -/
namespace Flapjack.HolFiniteMapExact

/-- Raw lookup function for HOL's right-folded association-list map. This is
Flapjack infrastructure used to state the representation witness. -/
noncomputable def alistToFmapRaw {α β : Type} (entries : List (α × β)) : FiniteMap α β := by
  classical
  exact FUPDATE_LIST_HOL FEMPTY entries.reverse

/-- Build a finite map from an association list, retaining the first entry
when a key occurs more than once. -/
@[hol "HOL/src/finite_maps/alistScript.sml" "alist_to_fmap_def" (fmap_as_finite_support_result)]
noncomputable def alistToFmap {α β : Type} (entries : List (α × β)) : HolFiniteMapExact α β := by
  classical
  exact HolFiniteMapExact.empty.updateListEq entries.reverse

/-- Canonical lookup agrees with the independent raw map operation. -/
theorem holFmapAsFiniteSupportResultWitness_alistToFmap {α β : Type}
    (entries : List (α × β)) (key : α) :
    (alistToFmap entries).lookup key = alistToFmapRaw entries key := by
  classical
  rfl

/-- Lookup uses the first matching association, including duplicate keys. -/
theorem lookup_alistToFmap_head {α β : Type} (entry : α × β)
    (entries : List (α × β)) :
    (alistToFmap (entry :: entries)).lookup entry.1 = some entry.2 := by
  classical
  simp [alistToFmap, FUPDATE_LIST_HOL, List.foldl_append, FUPDATE_HOL]

/-- A different key is found in the remainder of the association list. -/
theorem lookup_alistToFmap_tail {α β : Type} (entry : α × β)
    (entries : List (α × β)) (key : α) (different : key ≠ entry.1) :
    (alistToFmap (entry :: entries)).lookup key = (alistToFmap entries).lookup key := by
  classical
  simp [alistToFmap, FUPDATE_LIST_HOL, List.foldl_append, FUPDATE_HOL, different]

end Flapjack.HolFiniteMapExact
