module

public import Flapjack.Misc.Sptree
public import Flapjack.FiniteMap.AlistExact.Lookup

@[expose] public section

/-! Association-list construction of sparse trees. -/
namespace Flapjack

/-- Looking up an association-list tree returns the first matching entry. -/
@[hol "HOL/src/finite_maps/sptreeScript.sml" "lookup_fromAList"]
theorem sptLookupFromAList {α : Type} (entries : List (Nat × α)) (key : Nat) :
    sptLookup key (sptFromAList entries) = holALookup entries key := by
  rw [sptLookup_sptFromAList]
  classical
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨k, v⟩ := entry
    by_cases h : key = k <;> simp [sptAListLookup, holALookup, h, ih]

end Flapjack
