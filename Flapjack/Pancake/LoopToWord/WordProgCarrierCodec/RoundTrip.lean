import Flapjack.Pancake.LoopToWord

namespace Flapjack

/-- Unit-valued list encoding used by production cutsets is the same insertion
order as the exact Spt association-list reconstruction. -/
private theorem toNumSetMapFst (entries : List (Nat × Unit)) :
    LoopToWord.toNumSetHOL (entries.map Prod.fst) = sptFromAList entries := by
  induction entries with
  | nil => rfl
  | cons pair tail ih =>
      rcases pair with ⟨key, value⟩
      cases value
      simp only [List.map_cons, LoopToWord.toNumSetHOL, sptFromAList, ih]

/-- Re-encoding an enumerated exact cutset preserves every lookup. Spt tree
shape may normalize, so this states its actual finite-map semantics rather
than an unjustified syntactic tree equality. Flapjack carrier infrastructure. -/
theorem toNumSet_fromNumSet_lookup (tree : Spt Unit) (key : Nat) :
    sptLookup key (LoopToWord.toNumSetHOL (LoopToWord.fromNumSetHOL tree)) =
      sptLookup key tree := by
  rw [LoopToWord.fromNumSetHOL, toNumSetMapFst,
    sptLookup_sptFromAList_sptToAList]

end Flapjack

