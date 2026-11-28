module

public import Flapjack.Misc.Sptree.SizeInsert

@[expose] public section

/-!
# Size of `fromAList` in the sparse tree

Counterpart of `size_fromAList` from `cakeml/misc/miscScript.sml`: a tree built
from an association list with distinct keys has one value per entry.
-/

namespace Flapjack

open Classical in
/-- Original `size_fromAList`. -/
@[hol "cakeml/misc/miscScript.sml" "size_fromAList"]
theorem sptSize_sptFromAList {α : Type} (entries : List (Nat × α))
    (nodup : (entries.map Prod.fst).Nodup) :
    sptSize (sptFromAList entries) = entries.length := by
  induction entries with
  | nil => simp [sptFromAList]
  | cons entry rest ih =>
    obtain ⟨key, value⟩ := entry
    simp only [List.map_cons, List.nodup_cons] at nodup
    obtain ⟨hkey, hrest⟩ := nodup
    rw [sptFromAList, sptSize_sptInsert]
    have hnone : sptLookup key (sptFromAList rest) = none := by
      cases hlookup : sptLookup key (sptFromAList rest) with
      | none => rfl
      | some found =>
        rw [sptLookup_sptFromAList] at hlookup
        have hmem : (key, found) ∈ rest := sptAListLookup_mem key rest found hlookup
        have hfst : key ∈ rest.map Prod.fst := List.mem_map.mpr ⟨(key, found), hmem, rfl⟩
        exact absurd hfst hkey
    have hnotmem : ¬ sptDomain (sptFromAList rest) key := by
      show ¬ (sptLookup key (sptFromAList rest)).isSome = true
      rw [hnone]
      simp
    rw [if_neg hnotmem, ih hrest, List.length_cons]

end Flapjack
