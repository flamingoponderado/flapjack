module

public import Flapjack.Pancake.Semantics.CrepSem.HOLState

@[expose] public section

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

/-- A successful lookup in `alistToFmap` identifies an association listed in the
    source list. Flapjack local support for HOL `ALOOKUP_MEM` (`alistScript.sml`),
    which has no Lean counterpart in this module; it has no tag of its own. -/
theorem lookup_alistToFmap_mem {α β : Type} (entries : List (α × β)) (key : α)
    (value : β) (found : (alistToFmap entries).lookup key = some value) :
    (key, value) ∈ entries := by
  induction entries with
  | nil => simp [alistToFmap] at found
  | cons entry rest ih =>
      by_cases same : key = entry.1
      · rw [same] at found ⊢
        rw [lookup_alistToFmap_head entry rest] at found
        have equal : value = entry.2 := (Option.some.inj found).symm
        exact List.mem_cons.mpr (Or.inl (by rw [equal]))
      · rw [lookup_alistToFmap_tail entry rest key same] at found
        exact List.mem_cons_of_mem _ (ih found)

end Flapjack.HolFiniteMapExact
