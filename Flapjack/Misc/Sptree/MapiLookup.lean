import Flapjack.Misc.Sptree.Mapi

namespace Flapjack

private theorem lookupMkBN {α : Type} (left right : Spt α) (key : Nat) :
    sptLookup key (sptMkBN left right) = sptLookup key (.bn left right) := by
  cases left <;> cases right <;> by_cases zero : key = 0 <;>
    simp [sptMkBN, sptLookup, zero]

private theorem lookupMkBS {α : Type} (left : Spt α) (value : α) (right : Spt α) (key : Nat) :
    sptLookup key (sptMkBS left value right) = sptLookup key (.bs left value right) := by
  cases left <;> cases right <;> by_cases zero : key = 0 <;>
    by_cases even : key % 2 = 0 <;> simp [sptMkBS, sptLookup, zero, even]

/-- Unconditional indexed-map lookup on the exact tree carrier. Both payload
types, function, arbitrary starting index and key are retained; malformed
nodes are normalized by the original smart constructors without a wf premise. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "lookup_mapi0"]
theorem sptLookupMapi0 {α β : Type} (f : Nat → α → β) (tree : Spt α) (index key : Nat) :
    sptLookup key (sptMapi0 f index tree) =
      (sptLookup key tree).map (f (sptAcc index key)) := by
  induction tree generalizing index key with
  | ln => simp [sptMapi0, sptLookup]
  | ls value =>
      by_cases zero : key = 0 <;> simp [sptMapi0, sptLookup, zero, sptAcc]
  | bn left right ihLeft ihRight =>
      rw [sptMapi0, lookupMkBN]
      by_cases zero : key = 0
      · simp [sptLookup, zero]
      · by_cases even : key % 2 = 0
        · simp only [sptLookup, zero, if_false, even, if_true, ihLeft]
          rw [sptAcc_childLeft]
          have address : 2 * ((key - 1) / 2) + 2 = key := by omega
          rw [address]
        · simp only [sptLookup, zero, if_false, even, ihRight]
          rw [sptAcc_childRight]
          have address : 2 * ((key - 1) / 2) + 1 = key := by omega
          rw [address]
  | bs left value right ihLeft ihRight =>
      rw [sptMapi0, lookupMkBS]
      by_cases zero : key = 0
      · simp [sptLookup, zero, sptAcc]
      · by_cases even : key % 2 = 0
        · simp only [sptLookup, zero, if_false, even, if_true, ihLeft]
          rw [sptAcc_childLeft]
          have address : 2 * ((key - 1) / 2) + 2 = key := by omega
          rw [address]
        · simp only [sptLookup, zero, if_false, even, ihRight]
          rw [sptAcc_childRight]
          have address : 2 * ((key - 1) / 2) + 1 = key := by omega
          rw [address]

/-- Full source lookup equation for the indexed map starting at zero. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "lookup_mapi"]
theorem sptLookupMapi {α β : Type} (f : Nat → α → β) (tree : Spt α) (key : Nat) :
    sptLookup key (sptMapi f tree) = (sptLookup key tree).map (f key) := by
  rw [sptMapi, sptLookupMapi0]
  simp [sptAcc_eq, lrNext]

end Flapjack
